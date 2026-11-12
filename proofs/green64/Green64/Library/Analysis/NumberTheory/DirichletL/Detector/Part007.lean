module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part004
public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.Canonical
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part003

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Detector / Part007

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsCentralRamified -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedStrictSelected (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    (rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j 1 0 1 0 /
      (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        (coordV (Ideal.absNorm (Ideal.span {p})) z)))

include hc in
theorem ramifiedSelected_central_regular (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j-ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      385*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0<Q := by dsimp [Q];linarith
  have hQ1 : 1≤Q := by linarith
  have hrem := rowClosedMarked_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  dsimp only at hrem
  simp only [Complex.ofReal_natCast] at hrem
  have hH := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z hQ heta ha hρ
    (by rw [hx];linarith) (by rw [hw];linarith) (by rw [hz]) (by rw [hx,hw];linarith) j hj
  have hV := first_region_V_half _ hQ z (by rw [hz])
  have h1V : ‖1-coordV Q z‖≤3/2 := by
    have h := norm_sub_le (1:ℂ) (coordV Q z)
    rw [norm_one] at h
    change ‖coordV Q z‖≤1/2 at hV
    linarith
  have hphase : ‖star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x‖≤Q^x.re := by
    rw [norm_mul,norm_star,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hqw : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)‖≤Q^(1/2:ℝ) := by
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
  have hid (B V M T q H : ℂ) : B*V*M-q*H-B*V*T=B*V*(M-T)-q*H := by ring
  unfold ramifiedSelected ramifiedStrictSelected
  rw [hid]
  apply (norm_sub_le _ _).trans
  simp only [norm_mul] at hphase ⊢
  calc
    _≤(Q^x.re*(3/2))*(128*Q^(1/2-x.re))+Q^(1/2:ℝ)*193 := by
      gcongr
    _=385*Q^(1/2:ℝ) := by
      have ht : Q^x.re*Q^(1/2-x.re)=Q^(1/2:ℝ) := by rw [←Real.rpow_add hQ0];congr 1;ring
      nlinarith [ht]
end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsCentralStrictSelected -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma ramifiedStrictSelected_from_entry (eta a rho x w z : ℂ) (j : ℕ) (b : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (heta : ‖eta‖≤1) (ha : ‖a‖≤1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (ht : ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^b) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(x.re+b) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0<Q := by dsimp [Q];linarith
  rw [sourceRowTerm_pos p hp hg eta a rho x w z j 1 0 1 0 (by omega)] at ht
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha hx hz)
  simp only [Complex.ofReal_natCast] at hr
  have hv := first_region_V_half _ hQ z hz
  have hs := norm_sub_le (1:ℂ) (coordV Q z)
  rw [norm_one] at hs
  have h1V : ‖1-coordV Q z‖≤3/2 := by change ‖coordV Q z‖≤1/2 at hv;linarith
  have hphase : ‖star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x‖≤Q^x.re := by
    rw [norm_mul,norm_star,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  unfold ramifiedStrictSelected
  rw [div_eq_mul_inv]
  simp only [norm_mul] at hphase ⊢
  calc
    _≤(Q^x.re*(3/2))*((2*Q^b)*2) := by gcongr
    _=6*Q^(x.re+b) := by rw [Real.rpow_add hQ0];ring

include hc in
theorem ramifiedStrictSelected_central_norm (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1-w.re) := by
  have hb := ramifiedStrictSelected_from_entry p hp hg eta a rho x w z j (1-x.re-w.re)
    hQ heta ha hx hz (sourceRowTerm_central_strict_norm p hp hg hc eta a rho x w z heta ha hρ j hj)
  convert hb using 1 ; congr 2 ; ring

include hc in
theorem ramifiedStrictSelected_boundary_norm (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j≤1) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-w.re) := by
  have hb := ramifiedStrictSelected_from_entry p hp hg eta a rho x w z j (-x.re-w.re)
    hQ heta ha hx hz (sourceRowTerm_central_boundary_norm p hp hg hc eta a rho x w z heta ha hρ j hj)
  convert hb using 1 ; congr 2 ; ring
end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsCentralRamifiedQuotient -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma norm_div_le_twice (A H : ℂ) (hH : 1/2≤‖H‖) : ‖A/H‖≤2*‖A‖ := by
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0<‖H‖)).mpr
  nlinarith [norm_nonneg A]

variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
theorem ramifiedSelected_central_quotient (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (hsmall : 198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps)≤1/2)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    Q^(-1:ℝ)*‖ramifiedSelected p hp hg eta a rho x w z j /
      ramifiedClosed p hp hg eta a rho x w z j‖≤
      800*Q^(-(1/2:ℝ))+(if 2≤j then 12*Q^(-w.re) else 0) := by
  dsimp only
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0<Q := by dsimp [Q];linarith
  have hQ1 : 1≤Q := by linarith
  have hH := ramifiedClosed_central_lower p hp hg hc eta a rho x w z alpha eps hQ hsmall heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hreg := ramifiedSelected_central_regular p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hnorm := norm_div_le_twice (ramifiedSelected p hp hg eta a rho x w z j)
    (ramifiedClosed p hp hg eta a rho x w z j) hH
  have htri := (norm_add_le _ _).trans (add_le_add hreg (le_refl ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖))
  rw [sub_add_cancel] at htri
  have hpow : Q^(-1:ℝ)*Q^(1/2:ℝ)=Q^(-(1/2:ℝ)) := by rw [←Real.rpow_add hQ0];norm_num
  have hqi : 0≤Q^(-1:ℝ) := Real.rpow_nonneg hQ0.le _
  by_cases hj2 : 2≤j
  · rw [ite_eq_left hj2]
    have hs := ramifiedStrictSelected_central_norm p hp hg hc eta a rho x w z hQ heta ha hρ
      (by rw [hx];linarith) (by rw [hz]) j hj
    have hb : ‖ramifiedSelected p hp hg eta a rho x w z j‖≤385*Q^(1/2:ℝ)+6*Q^(1-w.re) := by linarith
    have hprod : Q^(-1:ℝ)*Q^(1-w.re)=Q^(-w.re) := by rw [←Real.rpow_add hQ0];congr 1;ring
    calc
      _≤Q^(-1:ℝ)*(2*(385*Q^(1/2:ℝ)+6*Q^(1-w.re))) := mul_le_mul_of_nonneg_left (hnorm.trans (by linarith)) hqi
      _=770*Q^(-(1/2:ℝ))+12*Q^(-w.re) := by nlinarith [hpow,hprod]
      _≤_ := by nlinarith [Real.rpow_nonneg hQ0.le (-(1/2:ℝ))]
  · rw [ite_eq_right hj2,add_zero]
    have hs := ramifiedStrictSelected_boundary_norm p hp hg hc eta a rho x w z hQ heta ha hρ
      (by rw [hx];linarith) (by rw [hz]) j (by omega)
    have hqw : Q^(-w.re)≤Q^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
    have hb : ‖ramifiedSelected p hp hg eta a rho x w z j‖≤391*Q^(1/2:ℝ) := by nlinarith
    calc
      _≤Q^(-1:ℝ)*(2*(391*Q^(1/2:ℝ))) := mul_le_mul_of_nonneg_left (hnorm.trans (by linarith)) hqi
      _=782*Q^(-(1/2:ℝ)) := by nlinarith [hpow]
      _≤_ := mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hQ0.le _)
end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.MarkedValuations -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic UniqueFactorizationMonoid ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma prime_dvd_iff_valuation (P : PrimeIdeal) (I : Id) (hI : I≠0) :
    P.val∣I ↔ primeValuations I P≠0 := by
  rw [primeValuations_apply,Multiset.count_ne_zero,mem_normalizedFactors_iff hI]
  exact ⟨fun h=>⟨P.property,h⟩,fun h=>h.2⟩

lemma prime_dvd_high_completed (P : PrimeIdeal) (v : PrimeIdeal→₀HighValuation) :
    P.val∣(highIdeals v).1.1*(highIdeals v).1.2^3 ↔ (v P).1.1+3*(v P).1.2≠0 := by
  have hI : (highIdeals v).1.1≠0 := idealFromValuations_ne_zero _
  have hJ : (highIdeals v).1.2≠0 := idealFromValuations_ne_zero _
  rw [prime_dvd_iff_valuation P _ (mul_ne_zero hI (pow_ne_zero _ hJ)),
    primeValuations_mul _ _ hI (pow_ne_zero _ hJ),primeValuations_pow]
  simp only [highIdeals,primeValuations_idealFromValuations,Finsupp.add_apply,
    Finsupp.mapRange_apply,Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]

lemma primeProduct_dvd (T : Finset PrimeIdeal) (I : Id) :
    (∏P∈T,P.val)∣I ↔ ∀P∈T,P.val∣I := by
  constructor
  · intro h P hP
    exact (Finset.dvd_prod_of_mem _ hP).trans h
  · intro h
    exact Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ=>primeIdeal_coprime P Q hPQ) h

def completedValuationMark (_P : PrimeIdeal) (b : HighValuation) : ℂ :=
  if b.1.1+3*b.1.2≠0 then 1 else 0

lemma completedValuationMark_norm (_P : PrimeIdeal) (b : HighValuation) :
    ‖completedValuationMark _P b‖≤1 := by
  unfold completedValuationMark
  split_ifs <;> norm_num

lemma completedValuationMark_product (T : Finset PrimeIdeal) (v : PrimeIdeal→₀HighValuation) :
    (∏P∈T,completedValuationMark P (v P))=
      if (∏P∈T,P.val)∣(highIdeals v).1.1*(highIdeals v).1.2^3 then 1 else 0 := by
  rw [primeProduct_dvd]
  simp only [prime_dvd_high_completed]
  by_cases h : ∀P∈T,(v P).1.1+3*(v P).1.2≠0
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro P hP
    exact ite_eq_left (h P hP)
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨P,hP,hv⟩ := h
    apply Finset.prod_eq_zero hP
    simp only [completedValuationMark,hv,ne_eq,not_true_eq_false,ite_false]

lemma highIdealMask_mark (S : Finset Id) (D I J K L : Id) :
    highIdealMask S D I J K L=(if D∣I*J^3 then 1 else 0)*highIdealMask S 1 I J K L := by
  unfold highIdealMask completedMask
  simp only [one_dvd,true_and]
  split_ifs <;> simp_all

lemma markedIdealHighSummand_mark (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) :
    markedIdealHighSummand S D η u x w z I J K L=
      (if D∣I*J^3 then 1 else 0)*markedIdealHighSummand S 1 η u x w z I J K L := by
  rw [markedIdealHighSummand,highIdealMask_mark,markedIdealHighSummand,mul_assoc]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.MarkedEuler -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEulerFinsupp
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def excludedHighArray (S : Finset Id) (η : HeckeFamily.Character) (x w z : ℂ) (a : HighIdeal) : ℂ :=
  markedIdealHighSummand S 1 η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2

lemma excludedHighArray_one (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ) : excludedHighArray S η x w z 1=1 := by
  simp only [excludedHighArray,Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
    highIdealMask_unmarked_one S hS,bareIdealHighSummand_one,one_mul]

lemma excludedHighArray_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ) (a b : HighIdeal)
    (hc : IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2)) :
    excludedHighArray S η x w z (a*b)=excludedHighArray S η x w z a*excludedHighArray S η x w z b := by
  simp only [excludedHighArray,Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
    highIdealMask_unmarked_mul S hS a b,
    bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hc]
  ring

def excludedHighPrimeTerm (S : Finset Id) (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  excludedHighArray S η x w z ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))

lemma excludedHighArray_prod (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    excludedHighArray S η x w z (highIdeals v)=v.prod (excludedHighPrimeTerm S η x w z) :=
  highArray_val_prod _ (excludedHighArray_one S hS η x w z) (excludedHighArray_mul S hS η x w z) v

lemma markedHighArray_val (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (x w z : ℂ) (v : PrimeIdeal→₀HighValuation) :
    markedIdealHighSummand S (∏P∈T,P.val) η 1 x w z
      (highIdeals v).1.1 (highIdeals v).1.2 (highIdeals v).2.1 (highIdeals v).2.2=
        markedArray T completedValuationMark (excludedHighPrimeTerm S η x w z) v := by
  rw [markedIdealHighSummand_mark,markedArray,completedValuationMark_product]
  change _*excludedHighArray S η x w z (highIdeals v)=_
  rw [excludedHighArray_prod S hS]

theorem markedIdealHighSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b)
      (markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z) := by
  have h0 (P : PrimeIdeal) : excludedHighPrimeTerm S η x w z P 0=1 := by
    simp only [excludedHighPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero]
    exact excludedHighArray_one S hS η x w z
  have hs := (markedIdealHighSummand_summable S 1 η 1 x w z hx hw hz).norm.comp_injective highIdeals_injective
  change Summable (fun v=>‖excludedHighArray S η x w z (highIdeals v)‖) at hs
  simp only [excludedHighArray_prod S hS] at hs
  have he := marked_hasProd T completedValuationMark (excludedHighPrimeTerm S η x w z) h0 hs
    (fun P _ b=>completedValuationMark_norm P b)
  have hsum : (∑'v : PrimeIdeal→₀HighValuation,
      markedArray T completedValuationMark (excludedHighPrimeTerm S η x w z) v)=
      markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z := by
    simp only [←markedHighArray_val S hS T η x w z]
    unfold markedIdealHighSeries
    apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
      markedIdealHighSummand S (∏P∈T,P.val) η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
    intro a ha
    have hh : bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hc := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hc.2.1.1⟩,⟨a.1.2,hc.2.2.1.1⟩),(⟨a.2.1,hc.2.2.2.1.1⟩,⟨a.2.2,hc.2.2.2.2.1⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [hsum] using he

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.MarkedLocal -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def idealMarkedLocalFactor (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∑e : Fin 2,∑'l,∑'k,∑'m,
    completedValuationMark P ((e.val,l),(k,m))*highPrimeTerm η x w z P ((e.val,l),(k,m))

lemma markedPrimeTerm_summable_norm (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun b : HighValuation=>‖completedValuationMark P b*highPrimeTerm η x w z P b‖) := by
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (highPrimeTerm_summable_norm η x w z hx hw hz P)
  intro b
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (completedValuationMark_norm P b)

lemma markedPrimeTerm_tsum (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (∑'b : HighValuation,completedValuationMark P b*highPrimeTerm η x w z P b)=
      idealMarkedLocalFactor η P x w z := by
  have hs := (markedPrimeTerm_summable_norm η P x w z hx hw hz).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) : (∑'b : ℕ×ℕ,completedValuationMark P ((e,l),b)*highPrimeTerm η x w z P ((e,l),b))=
      ∑'k,∑'m,completedValuationMark P ((e,l),(k,m))*highPrimeTerm η x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [highPrimeTerm_zero_of_two_le η x w z P e _ _ _ hh,mul_zero,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

lemma selectedLocal_outside (S : Finset Id) (hS : ∀P∈S,Prime P) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (∑'b : HighValuation,ProbeEulerFinsupp.markedLocal T completedValuationMark
      (excludedHighPrimeTerm S η x w z) P b)=
      if P∈T then idealMarkedLocalFactor η P x w z else idealHighLocalFactor η P.val x w z := by
  have he (b : HighValuation) : excludedHighPrimeTerm S η x w z P b=highPrimeTerm η x w z P b := by
    simp only [excludedHighPrimeTerm,excludedHighArray,markedIdealHighSummand,
      highIdealMask_prime_outside S hS P hP,one_mul,highPrimeTerm]
  simp only [ProbeEulerFinsupp.markedLocal,he]
  by_cases hPT : P∈T
  · simp only [ite_eq_left hPT]
    exact markedPrimeTerm_tsum η P x w z hx hw hz
  · simp only [ite_eq_right hPT,one_mul]
    exact highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz P

lemma idealMarkedLocalFactor_eq_source (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    let p := primaryGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    letI : (Ideal.span {p}:Id).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hg := (supported_prime_data p hp ((span_primaryGenerator_of_supported P.val hs).symm ▸ hs)).1
    idealMarkedLocalFactor η P x w z=
      principalMarkedSeries p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm P.val:ℂ)^(-x)) ((Ideal.absNorm P.val:ℂ)^(-w))
        (coordV (Ideal.absNorm P.val) z) := by
  dsimp only
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Id).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  unfold idealMarkedLocalFactor principalMarkedSeries principalInner
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  change completedValuationMark P ((e.val,l),(k,m))*bareIdealHighSummand η 1 x w z
    (P.val^e.val) (P.val^l) (P.val^k) (P.val^m)=_
  have hterm := bareIdealHighSummand_at_prime η p hp hg.1 hg.2 hprimary hsp e.val l k m (by omega) x w z
  conv_lhs at hterm => rw [hspan]
  rw [hterm]
  by_cases ht : e.val+3*l=0
  · have he0 : e.val=0 := by omega
    have hl0 : l=0 := by omega
    simp only [completedValuationMark,ht,ne_eq,not_true_eq_false,ite_false,zero_mul]
    rw [he0,hl0]
    simpa only [hspan] using (markedTerm_zero_index p hp hg.1 (targetMonoid η p)
      (actualACube η p) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) k m).symm
  · simp only [completedValuationMark,ht,ne_eq,not_false_eq_true,ite_true,one_mul]
    simpa only [hspan] using sourcePrincipalTerm_pos p hp hg.1 (targetMonoid η p) (actualACube η p) x w z e.val l k m ht

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.MarkedRational -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def idealMarkedClosed (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val
  let R := coordR Q (actualAPhase η (primaryGenerator P.val)) x z
  markedFactor R (coordV Q z) (Q:ℂ)⁻¹ (coordK Q (HeckeFamily.idealCoeff η P.val) x w)
    (-coordD Q (HeckeFamily.idealCoeff η P.val) 1 x+coordW Q 1 w*R) 1

theorem idealMarkedLocalFactor_rational (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hx : 3/2<x.re) (hz : 1/6<z.re) :
    idealMarkedLocalFactor η P x w z=idealMarkedClosed η P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    rw [hspan]
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1 := by
    rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (actualACube η p) x z
  simp only [Complex.ofReal_natCast] at hr
  have he := principalMarkedSeries_eq p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p)
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) hV (by simpa only [hr] using hR)
  have hsource := idealMarkedLocalFactor_eq_source η P hs x w z
  dsimp only at hsource
  rw [hsource]
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (targetMonoid η p) x w
  simp only [Complex.ofReal_natCast] at hr hk
  rw [hr,←hk] at he
  simp only [actualACube_sq] at he
  convert he using 1
  · congr 2 <;> simp only [hspan,p]
  · simp only [idealMarkedClosed,coordD,coordW,star_one,mul_one,one_mul]
    simp only [hspan,p,targetMonoid_primaryGenerator η P.val hs,Complex.ofReal_natCast,neg_mul]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SpectralCoefficient -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow ProbePhase ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma rayMask_supported (a : O) (ha : Supported (Ideal.span {a})) : RayFourExpansion.rayMask a=1 := by
  let : (Ideal.span {(2:O)}).IsMaximal := by
    simpa only [cubicTwoIdeal,Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal
  let : Field (O⧸Ideal.span {(2:O)}) := Ideal.Quotient.field _
  have h2 : IsCoprime (2:O) a := by
    apply (isUnit_quotient_span_iff _ _).mp
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact ((supported_span_iff a).mp ha).2
      (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have h4 : IsCoprime (4:O) a := by
    simpa only [show (2:O)^2=4 by norm_num] using (h2.pow_left : IsCoprime ((2:O)^2) a)
  exact ite_eq_left ((isUnit_quotient_span_iff (4:O) a).mpr h4)

lemma completedCorrection_supported (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    completedCorrection I J=star (G (completedIndex I J)) := by
  rw [completedCorrection_eq_phase,rayMask_supported]
  · exact one_mul _
  · exact supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
      ((supported_span_primaryGenerator_iff J).mpr hJ)

lemma baseRowCoefficient_unit_apply (η : HeckeFamily.Character) (C : CalibrationData)
    (s : O) (hs : Supported (Ideal.span {s})) (A : O) (hA : Supported (Ideal.span {A}))
    (hcop : IsCoprime C.generator A) :
    baseRowCoefficient η C.Xi s hs A=targetMonoid η A*(C.Xi A)⁻¹*reciprocitySign A s := by
  change targetMonoid η A*star (C.Xi A)*sexticReciprocityPhase s A=_
  have hc : star (C.Xi A)=(C.Xi A)⁻¹ := (Complex.inv_eq_conj (C.Xi_norm_one A hA hcop)).symm
  rw [hc]
  congr 1
  exact congrArg (fun n : ℤ=>(n:ℂ)) (QuadraticAllOddCRT.quadraticRaySign_symm _ _)

theorem spectralSummand_source_coefficient (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : CalibrationData) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (t : ℂ) :
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J=
      completedMask S D I J *
        (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
          star (FiniteGaussPhase.angularFactor (completedIndex I J)*G (completedIndex I J))*
          targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*
          reciprocitySign (completedIndex I J) s) /
        ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)) *
        (fullIdealWeight t I*fullIdealWeight (3*t) J) := by
  have hA := supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ)
  have hb := baseRowCoefficient_unit_apply η C s hs (completedIndex I J) hA hcop
  have hangle : FiniteGaussPhase.angularFactor (completedIndex I J)=
      FiniteGaussPhase.angularFactor (primaryGenerator I)*FiniteGaussPhase.angularFactor (primaryGenerator J)^3 := by
    rw [completedIndex,angularFactor_mul,show primaryGenerator J^3=(primaryGenerator J*primaryGenerator J)*primaryGenerator J by ring,
      angularFactor_mul,angularFactor_mul]
    ring
  have hm : baseRowCoefficient η C.Xi s hs (primaryGenerator I)*
      baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3=
        targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*reciprocitySign (completedIndex I J) s := by
    rw [←map_pow,←map_mul]
    exact hb
  unfold spectralSummand CompletedGauss.columnWeight
  rw [completedCorrection_supported I J hI hJ,squarefreeGaussCoefficient_eq I hsf
    (supported_primaryGenerator_ne_zero I hI)]
  change _*(star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
      baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3/(Ideal.absNorm J:ℂ))*_=_
  rw [hangle]
  simp only [star_mul,star_pow]
  calc
    _ = completedMask S D I J*
      (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
        (star (FiniteGaussPhase.angularFactor (primaryGenerator I))*
         star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3)*star (G (completedIndex I J))*
        (baseRowCoefficient η C.Xi s hs (primaryGenerator I)*baseRowCoefficient η C.Xi s hs (primaryGenerator J)^3)) /
      ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ))*(fullIdealWeight t I*fullIdealWeight (3*t) J) := by ring
    _ = _ := by rw [hm];ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PhysicalCoefficientScaling -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem physical_spectral_coefficient_scale (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : CalibrationData) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime C.generator (completedIndex I J)) (X : ℝ) (hX : 0<X) (t : ℂ) (H : O) :
    let A := completedIndex I J
    let hA := supportedElement_ne_zero A (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*A):ℝ):ℂ)*actualCongruenceCoefficient C A s hA H =
    (Real.sqrt X:ℂ) * completedMask S D I J *
      calibratedHighCoefficient C η I (supported_primaryGenerator_ne_zero I hI) A s hA H /
      ((elementNorm A:ℂ)*(Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)) *
      (fullIdealWeight t I*fullIdealWeight (3*t) J) := by
  dsimp only
  have hA := supportedElement_ne_zero (completedIndex I J) (supported_completed _ _
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
  have he := physical_poisson_prefactor (elementNorm C.generator) (elementNorm (completedIndex I J))
    (elementNorm s) X (elementNorm_pos _ C.generator_ne_zero) (elementNorm_pos _ hA)
    (elementNorm_pos _ (supportedElement_ne_zero s hs)) hX
  rw [spectralSummand_source_coefficient S D I J η C s hs hI hJ hsf hcop t]
  simp only [elementNorm_mul,Complex.ofReal_div,Complex.ofReal_mul] at he ⊢
  unfold calibratedHighCoefficient
  have hh := congrArg (fun v : ℂ=>v*
    (idealRowHom C.generator (Ideal.span {s})/(C.tau*C.residueMonoid s))*
    (completedMask S D I J *
      (gaussTwo I (supported_primaryGenerator_ne_zero I hI)*
        star (FiniteGaussPhase.angularFactor (completedIndex I J)*ProbePhase.G (completedIndex I J))*
        targetMonoid η (completedIndex I J)*(C.Xi (completedIndex I J))⁻¹*
        ProbePhase.reciprocitySign (completedIndex I J) s)/
      ((Real.sqrt (Ideal.absNorm I):ℂ)*(Ideal.absNorm J:ℂ)))*
    (fullIdealWeight t I*fullIdealWeight (3*t) J)*
    actualCongruenceCoefficient C (completedIndex I J) s hA H) he
  convert hh using 1 <;> ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PhysicalMellinCoefficient -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma completedIndex_norm (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    elementNorm (completedIndex I J)=(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  rw [completedIndex, elementNorm_mul, elementNorm_pow]
  unfold elementNorm
  rw [(primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1,
    (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J hJ)).1]

theorem physical_mellin_coefficient (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (D I J : Ideal O) (η : HeckeFamily.Character) (s : O) (hs : Supported (Ideal.span {s}))
    (hI : Supported I) (hJ : Supported J) (hsf : Squarefree I)
    (hcop : IsCoprime (calibrationForSet S hS).generator (completedIndex I J*s))
    (X : ℝ) (hX : 0<X) (H : O) (hH : H≠0) (t z : ℂ) :
    let C := calibrationForSet S hS
    let A := completedIndex I J
    let hA := supportedElement_ne_zero A (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ))
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*A):ℝ):ℂ)*actualCongruenceCoefficient C A s hA H *
      ((K*elementNorm H/elementNorm ((C.generator*A)*s)):ℂ)^(-z) =
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*completedMask S D I J*star (C.residueMonoid H)*
      bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I hI) A s hA H *
      (fullIdealWeight (t+1-z+1/2) I*fullIdealWeight (1+3*(t+1-z)) J) := by
  dsimp only
  have hA : Supported (Ideal.span {completedIndex I J}) := supported_completed _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ)
  rw [physical_spectral_coefficient_scale S D I J η (calibrationForSet S hS) s hs hI hJ hsf
    hcop.of_mul_right_left X hX t H]
  rw [calibratedHighCoefficient_eq_bare S hS η I (supported_primaryGenerator_ne_zero I hI)
    (completedIndex I J) s hA hs hcop H]
  have hr := congrArg (fun r : ℝ => (r : ℂ)) (physical_radial_argument
    (calibrationForSet S hS).generator (completedIndex I J) s H X
    (elementNorm_pos _ (calibrationForSet S hS).generator_ne_zero).ne'
    (elementNorm_pos _ (supportedElement_ne_zero s hs)).ne')
  simp only [Complex.ofReal_div, Complex.ofReal_mul] at hr
  simp only [Complex.ofReal_mul]
  rw [hr]
  rw [completedIndex_norm I J hI hJ]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ.1)
  have hn := sourceNormPower_identity (Ideal.absNorm I) (Ideal.absNorm J) (elementNorm H) X
    hi hj (elementNorm_pos H hH) hX t z
  rw [show -(t+1-z)-1/2= -(t+1-z+1/2) by ring] at hn
  simp only [fullIdealWeight,hI.1,hJ.1,ite_false,Complex.ofReal_natCast,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow] at hn ⊢
  have he := congrArg (fun v : ℂ=>v*completedMask S D I J*
    star ((calibrationForSet S hS).residueMonoid H)*
    bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I hI) (completedIndex I J) s
      (supportedElement_ne_zero _ hA) H) hn
  convert he using 1 <;> ring_nf

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SpectralSupport -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ProbeCompleted ProbeRow SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

lemma supported_of_source_exclusions (S : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆S) (I : Ideal O) (hI : I≠0)
    (hS : ∀P∈S,¬P∣I) : Supported I := by
  refine ⟨hI,?_⟩
  intro P hP
  have hp : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hb
  exact hS P (hbad hb) (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)

lemma spectralSummand_support (S : Finset (Ideal O)) (hbad : fixedBadPrimes⊆S)
    (D I J : Ideal O) (Ψ : O→*ℂ) (t : ℂ)
    (h : spectralSummand S D Ψ t I J≠0) :
    Squarefree I ∧ Supported I ∧ Supported J := by
  have hI : I≠0 := by
    intro hz
    subst I
    exact h (by simp [spectralSummand])
  have hJ : J≠0 := by
    intro hz
    subst J
    exact h (by simp [spectralSummand])
  have hsf : Squarefree I := by
    by_contra hn
    exact h (by simp [spectralSummand,columnWeight,squarefreeGaussCoefficient,hn])
  have hm := spectralSummand_mask_nonzero S D I J Ψ t h
  have hex : ∀P∈S,¬P∣I*J^3 := by
    unfold completedMask at hm
    split_ifs at hm with hd
    · exact hd.2
    · exact False.elim (hm rfl)
  refine ⟨hsf,supported_of_source_exclusions S hbad I hI ?_,
    supported_of_source_exclusions S hbad J hJ ?_⟩
  · intro P hP hd
    exact hex P hP (dvd_mul_of_dvd_left hd _)
  · intro P hP hd
    exact hex P hP (dvd_mul_of_dvd_right (hd.trans (dvd_pow_self J (by decide : 3≠0))) _)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.MellinGuarded -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open ProbeCompleted ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def physicalMellinCoefficientTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (X : ℝ) (H : O) (t z : ℂ) : ℂ :=
  if hA : completedIndex I J≠0 then
    let K := elementNorm C.generator*elementNorm s*X
    idealRowHom C.generator (Ideal.span {s}) /
      (C.tau*C.residueMonoid s*(Real.sqrt K:ℂ)) * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ)*
      actualCongruenceCoefficient C (completedIndex I J) s hA H *
      ((K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)
  else 0

def guardedHighMellinCoefficient (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J : Ideal O) (s : O) (X : ℝ) (H : O) (x z : ℂ) : ℂ :=
  if h : Squarefree I ∧ Supported I ∧ Supported J then
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*completedMask S D I J*star (C.residueMonoid H)*
      bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I h.2.1)
        (completedIndex I J) s (supportedElement_ne_zero _ (supported_completed _ _
          ((supported_span_primaryGenerator_iff I).mpr h.2.1)
          ((supported_span_primaryGenerator_iff J).mpr h.2.2))) H *
      (fullIdealWeight (x+1/2) I*fullIdealWeight (1+3*x) J)
  else 0

theorem physicalMellinCoefficientTerm_eq_guarded (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (D I J : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (hcs : IsCoprime (calibrationForSet S hS).generator s)
    (X : ℝ) (hX : 0<X) (H : O) (hH : H≠0) (t z : ℂ) :
    physicalMellinCoefficientTerm η (calibrationForSet S hS) S D I J s hs X H t z=
      guardedHighMellinCoefficient η (calibrationForSet S hS) S D I J s X H (t+1-z) z := by
  by_cases hg : Squarefree I ∧ Supported I ∧ Supported J
  · have hA : completedIndex I J≠0 := supportedElement_ne_zero _ (supported_completed _ _
      ((supported_span_primaryGenerator_iff I).mpr hg.2.1)
      ((supported_span_primaryGenerator_iff J).mpr hg.2.2))
    rw [physicalMellinCoefficientTerm,dite_eq_left hA,guardedHighMellinCoefficient,dite_eq_left hg]
    dsimp only
    by_cases hm : completedMask S D I J=0
    · simp only [spectralSummand,hm,zero_mul,mul_zero]
    · have hc : IsCoprime (calibrationForSet S hS).generator (completedIndex I J) := by
        apply calibrationForSet_coprime_of_excluded S hS
        rw [completedIndex_eq_primaryGenerator] at hA ⊢
        rw [(primaryGenerator_spec (I*J^3) hA).1]
        unfold completedMask at hm
        split_ifs at hm with hd
        · exact hd.2
        · exact False.elim (hm rfl)
      exact physical_mellin_coefficient S hS D I J η s hs hg.2.1 hg.2.2 hg.1
        (hc.mul_right hcs) X hX H hH t z
  · have hz : spectralSummand S D (baseRowCoefficient η (calibrationForSet S hS).Xi s hs) t I J=0 := by
      by_contra hn
      exact hg (spectralSummand_support S hbad D I J _ t hn)
    rw [guardedHighMellinCoefficient,dite_eq_right hg]
    unfold physicalMellinCoefficientTerm
    split_ifs <;> simp only [hz,mul_zero,zero_mul]

theorem guardedHighMellinCoefficient_eq_high (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (D I J K : Ideal O)
    (hK : Supported K) (hKS : ∀P∈S,¬P∣K) (X : ℝ) (H : O) (x w z : ℂ) :
    guardedHighMellinCoefficient η C S D I J (primaryGenerator K) X H x z *
      fullIdealWeight w K =
    (X:ℂ)^(1/2-z)*(elementNorm H:ℂ)^(-z)*star (C.residueMonoid H)*
      markedIdealHighSummand S D η H x w z I J K 1 := by
  have h1 : ∀P∈S,¬P∣(1:Ideal O) := by
    intro P hP hd
    exact (hS P hP).not_isUnit (isUnit_of_dvd_one hd)
  have hw : fullIdealWeight (6*z) (1:Ideal O)=1 := (IdealEuler.normWeight (6*z)).map_one
  unfold guardedHighMellinCoefficient markedIdealHighSummand highIdealMask
    bareIdealHighSummand bareIdealHighCoefficient
  simp only [ite_eq_left hKS,ite_eq_left h1,mul_one,hw,primaryGenerator_one,one_pow]
  by_cases hg : Squarefree I ∧ Supported I ∧ Supported J
  · have hfull : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O) :=
      ⟨hg.1,hg.2.1,hg.2.2,hK,supported_one_ideal⟩
    rw [dite_eq_left hg,dite_eq_left hfull]
    dsimp only [completedIndex]
    ring
  · have hfull : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O)) :=
      fun h=>hg ⟨h.1,h.2.1,h.2.2.1⟩
    rw [dite_eq_right hg,dite_eq_right hfull]
    simp only [mul_zero,zero_mul]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SixthMask -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve CubicEisenstein
open HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O

lemma calibration_sixth_ideal_mask (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (L : Ideal O) :
    (calibrationForSet S hS).residueMonoid (idealGenerator L)^6=
      if ∀P∈S,¬P∣L then 1 else 0 := by
  by_cases hL : ∀P∈S,¬P∣L
  · rw [ite_eq_left hL]
    apply calibrationForSet_residue_sixth
    apply calibrationForSet_coprime_of_excluded
    simpa only [span_idealGenerator] using hL
  · rw [ite_eq_right hL]
    have hz : (calibrationForSet S hS).residueMonoid (idealGenerator L)=0 := by
      by_contra hn
      have hu := (calibrationForSet S hS).residue.apply_ne_zero_iff.mp hn
      have hc := (isUnit_quotient_span_iff (calibrationForSet S hS).generator (idealGenerator L)).mp hu
      have ho := (calibrationForSet_coprime_iff S hS (idealGenerator L)).mp hc
      apply hL
      intro P hP hd
      apply ho P hP
      apply (Ideal.dvd_iff_le.mp hd)
      have hm : idealGenerator L∈Ideal.span ({idealGenerator L}:Set O) := Ideal.subset_span (by simp)
      rw [span_idealGenerator L] at hm
      exact hm
    rw [hz,zero_pow (by decide : 6≠0)]

lemma calibration_sixth_frequency_mask (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (u : O) (L : Ideal O) :
    star ((calibrationForSet S hS).residueMonoid (u*idealGenerator L^6))=
      star ((calibrationForSet S hS).residueMonoid u)*(if ∀P∈S,¬P∣L then 1 else 0) := by
  rw [map_mul,map_pow,calibration_sixth_ideal_mask]
  split_ifs <;> simp only [mul_one,mul_zero,star_zero]

lemma sixthFrequencyWeight (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (z : ℂ) :
    frequencyWeight z (sixthFrequencyEquiv p)=
      frequencyWeight z ⟨p.1.val,p.1.property.1⟩*fullIdealWeight (6*z) p.2.val := by
  have hu : 0<elementNorm p.1.val := elementNorm_pos _ p.1.property.1
  have hl : 0<(Ideal.absNorm p.2.val:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.2.property)
  have hn : elementNorm (sixthFrequencyEquiv p).val=
      elementNorm p.1.val*(Ideal.absNorm p.2.val:ℝ)^6 := by
    unfold elementNorm
    exact_mod_cast rowMap_norm p
  simp only [frequencyWeight,fullIdealWeight,ite_eq_right p.2.property,hn,Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hu.le (pow_nonneg hl.le 6)]
  congr 1
  have he := Complex.cpow_mul_ofReal_nonneg hl.le (6:ℝ) (-z)
  simp only [Real.rpow_ofNat,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_natCast] at he
  simp only [Complex.ofReal_pow,Complex.ofReal_natCast]
  rw [←he]
  congr 1
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.Active -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentActive
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalRowCompletion CenteredMomentCanonical

def netExponent (c d : ℕ) : ℕ := (c + 5 * d) % 6

theorem local_pair_reduction (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (c d : ℕ) (x : O ⧸ P) :
    (actualSextic P hg ^ c) x * star ((actualSextic P hg ^ d) x) =
      (actualSextic P hg ^ netExponent c d) x := by
  have h6 : actualSextic P hg ^ 6 = 1 := by
    rw [← actualSextic_order_six P hg hchar]
    exact pow_orderOf_eq_one _
  have h5 : actualSextic P hg ^ 5 = (actualSextic P hg)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using h6
  rw [MulChar.star_apply', ← MulChar.mul_apply]
  congr 1
  unfold netExponent
  rw [← actualSextic_order_six P hg hchar, pow_mod_orderOf,
    pow_add, pow_mul, h5, inv_pow]

def activeSupport {ι : Type*} (B : Finset ι) (c d : ι → ℕ) : Finset ι :=
  B.filter (fun i => netExponent (c i) (d i) ≠ 0)

def principalSupport {ι : Type*} (B : Finset ι) (c d : ι → ℕ) : Finset ι :=
  B.filter (fun i => netExponent (c i) (d i) = 0)

theorem netExponent_ne_zero {ι : Type*} (B : Finset ι) (c d : ι → ℕ)
    (i : activeSupport B c d) : netExponent (c i.val) (d i.val) ≠ 0 :=
  (Finset.mem_filter.mp i.property).2

theorem netExponent_lt_six (c d : ℕ) : netExponent c d < 6 := Nat.mod_lt _ (by decide)

theorem principal_product_eq_mask {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (B : Finset ι) (z : O) :
    (∏ i ∈ B, (1 : MulChar (O ⧸ P i) ℂ) (Ideal.Quotient.mk (P i) z)) =
      rowCoprimeMask P B z := by
  by_cases h : ∃ i ∈ B, z ∈ P i
  · rw [rowCoprimeMask, ite_eq_left h]
    obtain ⟨i, hi, hz⟩ := h
    apply Finset.prod_eq_zero hi
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
  · rw [rowCoprimeMask, ite_eq_right h]
    apply Finset.prod_eq_one
    intro i hi
    apply MulChar.one_apply
    let : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
    apply isUnit_iff_ne_zero.mpr
    exact fun hz => h ⟨i, hi, Ideal.Quotient.eq_zero_iff_mem.mp hz⟩

variable {ι : Type*}

theorem common_ideal_pair_active (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0) (z : O) :
    idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i)) =
      rowCoprimeMask P (principalSupport B c d) z *
        finiteSexticRow (fun i : activeSupport B c d => P i.val)
          (fun i => hg i.val) (fun i => netExponent (c i.val) (d i.val)) z := by
  let f := fun i => (actualSextic (P i) (hg i) ^ netExponent (c i) (d i))
    (Ideal.Quotient.mk (P i) z)
  have hlocal : idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i)) = ∏ i ∈ B, f i := by
    simp only [map_prod, map_pow, star_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [idealRowHom_prime z (P i) (hg i),
      ← MulChar.pow_apply' _ (hc i hi), ← MulChar.pow_apply' _ (hd i hi)]
    exact local_pair_reduction (P i) (hg i) (hchar i) (c i) (d i) _
  have hzero : (∏ i ∈ B.filter (fun i => netExponent (c i) (d i) = 0), f i) =
      rowCoprimeMask P (principalSupport B c d) z := by
    rw [← principal_product_eq_mask]
    apply Finset.prod_congr rfl
    intro i hi
    have he := (Finset.mem_filter.mp hi).2
    simp only [f, he, pow_zero]
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not B
    (fun i => netExponent (c i) (d i) = 0) f, hzero]
  congr 1
  exact (Finset.prod_coe_sort (s := activeSupport B c d) (f := f)).symm

theorem activePrimes_pairwise_coprime (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (B : Finset ι) (c d : ι → ℕ) :
    Pairwise (Function.onFun IsCoprime (fun i : activeSupport B c d => P i.val)) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  exact fun he => hij (Subtype.ext (hinj he))

theorem active_gauss_norm (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) (B : Finset ι) (c d : ι → ℕ) :
    ‖canonicalNormalizedGauss (fun i : activeSupport B c d => P i.val)
      (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
      (fun i => netExponent (c i.val) (d i.val))‖ = 1 :=
  norm_canonicalNormalizedGauss (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => netExponent (c i.val) (d i.val))
    (netExponent_ne_zero B c d) (fun _i => netExponent_lt_six _ _)

open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem common_ideal_pair_poisson (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    let Q := fun i : activeSupport B c d => P i.val
    let row := finiteSexticRow Q (fun i => hg i.val)
      (fun i => netExponent (c i.val) (d i.val))
    let r := finitePrimeModulus Q
    (∑' z : O, (idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i))) *
      W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K : ℂ) * canonicalNormalizedGauss Q
        (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
        (fun i => netExponent (c i.val) (d i.val)) / (‖eisEmbedding r‖ : ℂ)) *
      ∑ E ∈ (principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row e /
          (‖eisEmbedding e‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (K * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding r‖ ^ 2)) := by
  simp_rw [common_ideal_pair_active P hg hchar B c d hc hd]
  exact canonical_masked_radial_poisson_collected P hinj (principalSupport B c d)
    (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => netExponent (c i.val) (d i.val))
    (netExponent_ne_zero B c d) (fun i => netExponent_lt_six _ _) W K hK

end SevenEighths.CenteredMomentActive
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstMixed -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstMixed
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem frequencyReduction_comp (d n M : O) (hd : d∣n) (hn : n∣M) (x : Residue M) :
    frequencyReduction d n hd (frequencyReduction n M hn x)=frequencyReduction d M (hd.trans hn) x := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [frequencyReduction_mk]

theorem three_factor_mixed_fourier (a b c : O) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : IsCoprime a (b*c)) (hbc : IsCoprime b c)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue c)]
    [Fintype (Residue (b*c))] [Fintype (Residue (a*(b*c)))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (G : Residue c → ℂ)
    (h : Residue (a*(b*c))) :
    (∑ x : Residue (a*(b*c)),
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
      χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
      G (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)*
        quotientTrace (a*(b*c)) (mul_ne_zero ha (mul_ne_zero hb hc)) (h*x)) =
      χa (Ideal.Quotient.mk _ (b*c))*χb (Ideal.Quotient.mk _ (a*c))*
        residueGauss a ha χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) h)*
        residueGauss b hb χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) h)*
        (∑ y : Residue c,G (Ideal.Quotient.mk _ (a*b)*y)*
          quotientTrace c hc (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) h*y)) := by
  let F : Residue (b*c) → ℂ := fun y =>
    χb (frequencyReduction b (b*c) (dvd_mul_right _ _) y)*
      G (frequencyReduction c (b*c) (dvd_mul_left _ _) y)
  let h' := frequencyReduction (b*c) (a*(b*c)) (dvd_mul_left _ _) h
  have he (x : Residue (a*(b*c))) :
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
        F (frequencyReduction (b*c) (a*(b*c)) (dvd_mul_left _ _) x) =
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
        χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
        G (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x) := by
    dsimp only [F]
    rw [frequencyReduction_comp,frequencyReduction_comp]
    ring
  simp_rw [← he]
  rw [ProbePhysical.coprime_mixed_fourier a (b*c) ha (mul_ne_zero hb hc) habc χa F h]
  have hf (y : Residue (b*c)) : F (Ideal.Quotient.mk _ a*y)=
      χb (Ideal.Quotient.mk _ a)*
        (χb (frequencyReduction b (b*c) (dvd_mul_right _ _) y)*
          G (Ideal.Quotient.mk _ a*frequencyReduction c (b*c) (dvd_mul_left _ _) y)) := by
    simp only [F,map_mul,frequencyReduction_mk]
    ring
  simp_rw [hf,mul_assoc]
  rw [← Finset.mul_sum]
  have hh := ProbePhysical.coprime_mixed_fourier b c hb hc hbc χb
    (fun y => G (Ideal.Quotient.mk _ a*y)) h'
  simp only [mul_assoc] at hh
  rw [hh]
  simp only [h',frequencyReduction_comp,map_mul,mul_assoc]
  ring

end SevenEighths.CenteredMomentFirstMixed

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstReduced -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstReduced
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstMixed CenteredMomentActive
local notation "O" => ActualEisensteinCubic.O

def tripleRow (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (z : O) : ℂ :=
  χa (Ideal.Quotient.mk _ z)*χb (Ideal.Quotient.mk _ z)*G (Ideal.Quotient.mk _ z)

def tripleResidue (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (x : Residue (a*(b*r))) : ℂ :=
  χa (frequencyReduction a _ (dvd_mul_right _ _) x)*
    χb (frequencyReduction b _ (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
    G (frequencyReduction r _ (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)

@[simp] theorem tripleResidue_mk (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ) (z : O) :
    tripleResidue a b r χa χb G (Ideal.Quotient.mk _ z)=tripleRow a b r χa χb G z := by
  simp only [tripleResidue,tripleRow,frequencyReduction_mk]

theorem tripleRow_mul (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ)
    (hG : ∀ x y,G (x*y)=G x*G y) (x y : O) :
    tripleRow a b r χa χb G (x*y)=tripleRow a b r χa χb G x*tripleRow a b r χa χb G y := by
  simp only [tripleRow,map_mul,hG]
  ring

def tripleFourier (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (h : O) : ℂ :=
  ∑' x : Residue (a*(b*r)),tripleResidue a b r χa χb G x*
    quotientTrace (a*(b*r)) (mul_ne_zero ha (mul_ne_zero hb hr)) (Ideal.Quotient.mk _ h*x)

theorem tripleRow_radial_summable (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => tripleRow a b r χa χb G z*W (‖eisEmbedding z‖^2/K)) := by
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  have hh := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a*(b*r)})) (tripleResidue a b r χa χb G)
  simpa only [tripleResidue_mk,scaledRadialTest_apply] using hh

theorem tripleRow_poisson (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O,tripleRow a b r χa χb G z*W (‖eisEmbedding z‖^2/K)) =
      ((K/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r ha hb hr χa χb G h*
          paperRadialFourier W (K*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2) := by
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  have hh := actual_radial_paper_poisson_trace W K hK (a*(b*r))
    (mul_ne_zero ha (mul_ne_zero hb hr)) (tripleResidue a b r χa χb G)
  simpa only [tripleResidue_mk,tripleFourier,quotientTrace,tsum_fintype,Complex.real_smul] using hh

theorem masked_triple_poisson {α : Type*} (P : α → Ideal O)
    [∀ i,(P i).IsMaximal] (hinj : Function.Injective P) (S : Finset α)
    (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x y,G (x*y)=G x*G y)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O,rowCoprimeMask P S z*tripleRow a b r χa χb G z*W (‖eisEmbedding z‖^2/K)) =
      ∑ E ∈ S.powerset,
        let e := primeSubsetGenerator P E
        let k := K/‖eisEmbedding e‖^2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E,P i):ℂ)*tripleRow a b r χa χb G e*
          (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
            tripleFourier a b r ha hb hr χa χb G h*
              paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2)) := by
  rw [tsum_masked_radial_dilations P hinj S _ (tripleRow_mul a b r χa χb G hG) W K
    (tripleRow_radial_summable a b r ha hb hr χa χb G W K hK)]
  apply Finset.sum_congr rfl
  intro E hE
  rw [tripleRow_poisson a b r ha hb hr χa χb G W _ (primeSubset_reducedScale_pos P E hK)]

theorem principalSexticRow_mul {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (j : ι → ℕ) (r : O) (hr : Ideal.span {r}=∏ i,P i) (x y : Residue r) :
    principalSexticRow P hcop hg j r hr (x*y)=
      principalSexticRow P hcop hg j r hr x*principalSexticRow P hcop hg j r hr y := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul,principalSexticRow_mk P hcop hg j r hr (x*y),
    principalSexticRow_mk P hcop hg j r hr x,principalSexticRow_mk P hcop hg j r hr y,
    finiteSexticRow_mul P hg j x y]

theorem common_residual_reduced_poisson {ι : Type*}
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i) (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (B : Finset ι) (c d : ι → ℕ) (hc : ∀ i∈B,c i≠0) (hd : ∀ i∈B,d i≠0)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    let Q := fun i : activeSupport B c d => P i.val
    let hj := fun i : activeSupport B c d => netExponent (c i.val) (d i.val)
    let r := finitePrimeModulus Q
    let G := principalSexticRow Q (activePrimes_pairwise_coprime P hinj B c d)
      (fun i => hg i.val) hj r (span_finitePrimeModulus Q)
    (∑' z : O,χa (Ideal.Quotient.mk _ z)*χb (Ideal.Quotient.mk _ z)*
      (CanonicalRowCompletion.idealRowHom z (∏ i∈B,P i^c i)*
        star (CanonicalRowCompletion.idealRowHom z (∏ i∈B,P i^d i)))*
      W (‖eisEmbedding z‖^2/K)) =
      ∑ E ∈ (principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        let k := K/‖eisEmbedding e‖^2
        (UniqueFactorizationMonoid.moebius (∏ i∈E,P i):ℂ)*tripleRow a b r χa χb G e*
          (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
            tripleFourier a b r ha hb (finitePrimeModulus_ne_zero Q) χa χb G h*
              paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2)) := by
  dsimp only
  rw [← masked_triple_poisson P hinj (principalSupport B c d) a b _ ha hb
    (finitePrimeModulus_ne_zero _) χa χb _
    (principalSexticRow_mul _ _ _ _ _ _) W K hK]
  apply tsum_congr
  intro z
  rw [common_ideal_pair_active P hg hchar B c d hc hd]
  simp only [tripleRow,principalSexticRow_mk (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => netExponent (c i.val) (d i.val)) _ (span_finitePrimeModulus _) z]
  ring

end SevenEighths.CenteredMomentFirstReduced

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstActiveFourier -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstActiveFourier
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstMixed CenteredMomentFirstReduced
local notation "O" => ActualEisensteinCubic.O

theorem shifted_active_fourier {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6) (v h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    (∑' x : Residue r,G (Ideal.Quotient.mk _ v*x)*
      quotientTrace r (finitePrimeModulus_ne_zero P) (Ideal.Quotient.mk _ h*x)) =
      finiteSexticRow P hg j v*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j := by
  dsimp only
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i,P i) := Fintype.ofEquiv (Residue (finitePrimeModulus P)) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  rw [tsum_fintype]
  simp_rw [CenteredMomentFirstReduced.principalSexticRow_mul P hcop hg j
    (finitePrimeModulus P) (span_finitePrimeModulus P),
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P),mul_assoc]
  rw [← Finset.mul_sum,canonical_principal_gauss_transform P hcop hg hchar j hj0 hj6,
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)]
  change finiteSexticRow P hg j v*(star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j)=_
  ring

theorem tripleFourier_active {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    tripleFourier a b r ha hb (finitePrimeModulus_ne_zero P) χa χb G h =
      χa (Ideal.Quotient.mk _ (b*r))*χb (Ideal.Quotient.mk _ (a*r))*
        residueGauss a ha χa (Ideal.Quotient.mk _ h)*residueGauss b hb χb (Ideal.Quotient.mk _ h)*
        (finiteSexticRow P hg j (a*b)*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j) := by
  dsimp only
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let := finite_quotient_span (mul_ne_zero hb (finitePrimeModulus_ne_zero P))
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb (finitePrimeModulus_ne_zero P)))
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (b*finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (a*(b*finitePrimeModulus P))) := Fintype.ofFinite _
  unfold tripleFourier tripleResidue
  rw [tsum_fintype,three_factor_mixed_fourier a b (finitePrimeModulus P) ha hb
    (finitePrimeModulus_ne_zero P) har hbr]
  simp only [frequencyReduction_mk]
  have hs := shifted_active_fourier P hcop hg hchar j hj0 hj6 (a*b) h
  dsimp only at hs
  rw [tsum_fintype] at hs
  rw [hs]

theorem tripleFourier_active_norm_le {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    ‖tripleFourier a b r ha hb (finitePrimeModulus_ne_zero P) χa χb G h‖ ≤
      ‖eisEmbedding r‖*‖residueGauss a ha χa (Ideal.Quotient.mk _ h)‖*
        ‖residueGauss b hb χb (Ideal.Quotient.mk _ h)‖ := by
  dsimp only
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  rw [tripleFourier_active P hcop hg hchar j hj0 hj6 a b ha hb har hbr]
  simp only [norm_mul,norm_star,norm_canonicalGaussSum P hcop hg hchar j hj0 hj6]
  have hχa := QuadraticInitialBound.norm_finite_character_le_one χa (Ideal.Quotient.mk _ (b*finitePrimeModulus P))
  have hχb := QuadraticInitialBound.norm_finite_character_le_one χb (Ideal.Quotient.mk _ (a*finitePrimeModulus P))
  have hv := QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j (a*b)
  have hh := QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j h
  calc
    _ ≤ 1*1*‖residueGauss a ha χa (Ideal.Quotient.mk _ h)‖*
      ‖residueGauss b hb χb (Ideal.Quotient.mk _ h)‖*(1*1*‖eisEmbedding (finitePrimeModulus P)‖) := by
        gcongr
    _ = _ := by ring

end SevenEighths.CenteredMomentFirstActiveFourier

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.PrimaryCharacter -/

section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentPrimaryCharacter
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentPrimary CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def rawPrimaryHom (r : O) (χ : MulChar (Residue r) ℂ) : O →* ℂ where
  toFun n := primaryIdealCharacter r χ (Ideal.span {n})
  map_one' := by simp [← Ideal.one_eq_top]
  map_mul' x y := by rw [← Ideal.span_singleton_mul_span_singleton,map_mul]

def maskedPrimaryHom (r : O) (χ : MulChar (Residue r) ℂ) : O →* ℂ :=
  coprimalityMask (3:O)*rawPrimaryHom r χ

theorem maskedPrimaryHom_unit_mul (r : O) (χ : MulChar (Residue r) ℂ) (u : Oˣ) (n : O) :
    maskedPrimaryHom r χ ((u:O)*n)=maskedPrimaryHom r χ n := by
  change (if IsCoprime (3:O) ((u:O)*n) then (1:ℂ) else 0)*
      primaryIdealCharacter r χ (Ideal.span {(u:O)*n}) =
    (if IsCoprime (3:O) n then (1:ℂ) else 0)*primaryIdealCharacter r χ (Ideal.span {n})
  rw [isCoprime_mul_unit_left_right u.isUnit,Ideal.span_singleton_mul_left_unit u.isUnit]

theorem maskedPrimaryHom_ramified (r : O) (χ : MulChar (Residue r) ℂ) (n : O) (hn : λ₀∣n) :
    maskedPrimaryHom r χ n=0 := by
  have h3 : λ₀∣(3:O) := (dvd_pow_self λ₀ (by decide : 2≠0)).trans ActualEisensteinCubic.lambda_sq_dvd_three
  have hc : ¬IsCoprime (3:O) n := fun hc =>
    PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (hc.isUnit_of_dvd' h3 hn)
  change (if IsCoprime (3:O) n then (1:ℂ) else 0)*_=0
  rw [ite_eq_right hc,zero_mul]

theorem maskedPrimaryHom_primary (r : O) (χ : MulChar (Residue r) ℂ) (n : O)
    (hn : λ₀^2∣n-1) : maskedPrimaryHom r χ n=χ (Ideal.Quotient.mk _ n) := by
  change (if IsCoprime (3:O) n then (1:ℂ) else 0)*
    χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator (Ideal.span {n})))=_
  rw [ite_eq_left (CubicEisenstein.primary_coprime_three n hn).symm,one_mul,
    CompletedGauss.primaryGenerator_span n (CubicJacobiGlobal.primary_ne_zero n hn) hn]

theorem maskedPrimaryHom_periodic (r : O) (χ : MulChar (Residue r) ℂ) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {3*r}) (maskedPrimaryHom r χ) := by
  let F : O →* ℂ := χ.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {r})).toMonoidHom
  apply periodic_of_primary _ _ _ F _ (maskedPrimaryHom_unit_mul r χ)
    (maskedPrimaryHom_ramified r χ) (maskedPrimaryHom_primary r χ)
  · apply Ideal.span_singleton_le_span_singleton.mpr
    exact ActualEisensteinCubic.lambda_sq_dvd_three.trans (dvd_mul_right _ _)
  · intro x y hxy
    apply congrArg χ
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ((dvd_mul_left r 3).trans (Ideal.mem_span_singleton.mp hxy))

def primaryCharacter (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) : Character :=
  rowCharacter (Ideal.span {3*r})
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (by norm_num) hr))
    (maskedPrimaryHom r χ) (maskedPrimaryHom_periodic r χ)
    (fun u => by simpa only [mul_one,map_one] using maskedPrimaryHom_unit_mul r χ u 1)

@[simp] theorem primaryCharacter_modulus (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) :
    (primaryCharacter r hr χ).modulus=Ideal.span {3*r} := rfl

theorem primaryCharacter_primary (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) (n : O)
    (hn : λ₀^2∣n-1) : elementCoeff (primaryCharacter r hr χ) n=χ (Ideal.Quotient.mk _ n) := by
  rw [primaryCharacter,elementCoeff_rowCharacter,maskedPrimaryHom_primary r χ n hn]
  split_ifs with hc
  · rfl
  · symm
    apply MulChar.map_nonunit
    intro hu
    apply hc
    apply isUnit_residue_of_coprime
    apply (CubicEisenstein.primary_coprime_three n hn).symm.mul_left
    exact (CubicEisenstein.isUnit_quotient_span_iff r n).mp hu

theorem primaryCharacter_all (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) (n : O) :
    elementCoeff (primaryCharacter r hr χ) n=maskedPrimaryHom r χ n := by
  by_cases hn : λ₀∣n
  · rw [primaryCharacter,elementCoeff_rowCharacter,maskedPrimaryHom_ramified r χ n hn]
    split_ifs <;> rfl
  · have hg := (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff n).mpr hn
    have hs := CompletedGauss.primaryGenerator_spec (Ideal.span {n}) hg
    obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs.1.symm
    have hp : λ₀^2∣(u:O)*n-1 := by
      have hp' : λ₀^2∣CompletedGauss.primaryGenerator (Ideal.span {n})-1 := hs.2
      rwa [mul_comm,hu]
    rw [← elementCoeff_unit_mul (primaryCharacter r hr χ) u n,
      ← maskedPrimaryHom_unit_mul r χ u n,primaryCharacter_primary r hr χ _ hp,
      maskedPrimaryHom_primary r χ _ hp]

theorem primaryCharacter_ideal (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (primaryCharacter r hr χ) I=
      χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator I)) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := CompletedGauss.primaryGenerator_spec I hn
  calc
    _ = elementCoeff (primaryCharacter r hr χ) (CompletedGauss.primaryGenerator I) := by
      rw [← idealCoeff_span _ hn,hs.1]
    _ = _ := primaryCharacter_primary r hr χ _ hs.2

theorem primaryCharacter_modulus_norm (r : O) (hr : r≠0) (χ : MulChar (Residue r) ℂ) :
    (primaryCharacter r hr χ).modulus.absNorm=
      (Ideal.span {(3:O)}).absNorm*(Ideal.span {r}).absNorm := by
  rw [primaryCharacter_modulus,← Ideal.span_singleton_mul_span_singleton,map_mul]

end SevenEighths.CenteredMomentPrimaryCharacter

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.Primitive -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentPrimitive
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

def primitiveCharacter {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) :
    MulChar (Residue (finitePrimeModulus P)) ℂ :=
  crtCharacter ((Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
    (IdealGaussCRT.quotientProdEquivPi P hcop)) (fun i => actualSextic (P i) (hg i) ^ j i)

theorem primitiveCharacter_apply {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) (x : Residue (finitePrimeModulus P)) :
    primitiveCharacter P hcop hg j x =
      principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) x := rfl

@[simp] theorem primitiveCharacter_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ) (x : O) :
    primitiveCharacter P hcop hg j (Ideal.Quotient.mk _ x) =
      finiteSexticRow P hg j x := by
  exact (primitiveCharacter_apply P hcop hg j _).trans
    (principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) x)

theorem primitive_gauss_transform {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) (h : O) :
    residueGauss (finitePrimeModulus P) (finitePrimeModulus_ne_zero P)
      (primitiveCharacter P hcop hg j) (Ideal.Quotient.mk _ h) =
      star (finiteSexticRow P hg j h) * canonicalGaussSum P hcop hg j := by
  let r := finitePrimeModulus P
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (Residue r) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (Residue r) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  simp only [residueGauss, tsum_fintype, primitiveCharacter_apply]
  rw [canonical_principal_gauss_transform P hcop hg hchar j hj0 hj6
    (finitePrimeModulus P) (span_finitePrimeModulus P)]
  exact congrArg (fun z : ℂ => star z * canonicalGaussSum P hcop hg j)
    (principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) h)

lemma sqrt_absNorm (r : O) :
    Real.sqrt (Ideal.absNorm (Ideal.span {r}) : ℝ) = ‖eisEmbedding r‖ := by
  rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]

theorem normalized_primitive_gauss_norm_le_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) (h : O) :
    ‖normalizedResidueGauss (finitePrimeModulus P) (finitePrimeModulus_ne_zero P)
      (primitiveCharacter P hcop hg j) (Ideal.Quotient.mk _ h)‖ ≤ 1 := by
  rw [normalizedResidueGauss, primitive_gauss_transform P hcop hg hchar j hj0 hj6,
    sqrt_absNorm, mul_div_assoc]
  change ‖star (finiteSexticRow P hg j h) * canonicalNormalizedGauss P hcop hg j‖ ≤ 1
  rw [norm_mul, norm_star, norm_canonicalNormalizedGauss P hcop hg hchar j hj0 hj6, mul_one]
  exact QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j h

end SevenEighths.CenteredMomentPrimitive
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.Bridge -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentBridge
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentFirstPoisson

def productCharacter (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) :
    MulChar (Residue (a * b)) ℂ where
  toFun x := χa ((principalCRT a b hcop x).1) * χb ((principalCRT a b hcop x).2)
  map_one' := by simp
  map_mul' := by intro x y; simp [map_mul]; ring
  map_nonunit' := by
    intro x hx
    have hn : ¬IsUnit (principalCRT a b hcop x) := fun h =>
      hx ((isUnit_map_iff (principalCRT a b hcop) x).mp h)
    rw [Prod.isUnit_iff] at hn
    by_cases h : IsUnit (principalCRT a b hcop x).1
    · rw [χb.map_nonunit (fun hb => hn ⟨h, hb⟩), mul_zero]
    · rw [χa.map_nonunit h, zero_mul]

theorem productCharacter_apply (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (x : Residue (a * b)) :
    productCharacter a b hcop χa χb x =
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        χb (frequencyReduction b (a * b) (dvd_mul_left b a) x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [productCharacter, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    principalCRT_mk, frequencyReduction_mk]

@[simp] theorem productCharacter_mk (a b : O) (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (x : O) :
    productCharacter a b hcop χa χb (Ideal.Quotient.mk _ x) =
      χa (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x) := by
  rw [productCharacter_apply, frequencyReduction_mk, frequencyReduction_mk]

theorem productCharacter_gauss (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (h : Residue (a * b)) :
    residueGauss (a * b) (mul_ne_zero ha hb) (productCharacter a b hcop χa χb) h =
      χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
        residueGauss a ha χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        residueGauss b hb χb (frequencyReduction b (a * b) (dvd_mul_left b a) h) := by
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let := finite_quotient_span (mul_ne_zero ha hb)
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  simpa only [residueGauss, tsum_fintype, productCharacter_apply] using
    coprime_character_fourier a b ha hb hcop χa χb h

theorem triple_pair_gauss (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (j : O) :
    residueGauss (r * (a * b)) (mul_ne_zero hr (mul_ne_zero ha hb))
      (productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹))
      (Ideal.Quotient.mk _ j) =
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      (residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
  let := finite_quotient_span hb
  rw [productCharacter_gauss r (a * b) hr (mul_ne_zero ha hb),
    frequencyReduction_mk, frequencyReduction_mk,
    productCharacter_mk, productCharacter_gauss a b ha hb, frequencyReduction_mk,
    frequencyReduction_mk, residueGauss_inverse, ← map_neg]
  simp only [map_mul, star_mul, MulChar.star_apply']
  ring

theorem triple_pair_poisson (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
      star (χb (Ideal.Quotient.mk _ z))) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      ∑' j : O, (residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        residueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
        paperRadialFourier W
          (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  let χ := productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹)
  have hm : r * (a * b) ≠ 0 := mul_ne_zero hr (mul_ne_zero ha hb)
  let := finite_quotient_span hm
  let := finite_quotient_span hb
  let : Fintype (Residue (r * (a * b))) := Fintype.ofFinite _
  have hχ (z : O) : χ (Ideal.Quotient.mk _ z) =
      ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
        star (χb (Ideal.Quotient.mk _ z)) := by
    simp only [χ, productCharacter_mk, MulChar.star_apply', mul_assoc]
  have hp := actual_radial_paper_poisson_trace W K hK (r * (a * b)) hm χ
  change (∑' z : O, χ (Ideal.Quotient.mk _ z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
    (K / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) •
    ∑' j : O, (∑ x : Residue (r * (a * b)),
      χ x * quotientTrace (r * (a * b)) hm (Ideal.Quotient.mk _ j * x)) *
      paperRadialFourier W
        (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) at hp
  simp only [hχ] at hp
  rw [hp]
  have hcoeff (j : O) : (∑ x : Residue (r * (a * b)),
      χ x * quotientTrace (r * (a * b)) hm (Ideal.Quotient.mk _ j * x)) =
      residueGauss (r * (a * b)) hm χ (Ideal.Quotient.mk _ j) := by
    simp only [residueGauss, tsum_fintype]
  simp_rw [hcoeff]
  simp_rw [χ, triple_pair_gauss r a b hr ha hb hrab hab ξ χa χb]
  simp_rw [mul_assoc, tsum_mul_left]
  rw [Complex.real_smul]

theorem masked_triple_pair_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι)
    (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, rowCoprimeMask P S z *
      (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
        star (χb (Ideal.Quotient.mk _ z))) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ∑ E ∈ S.powerset,
        let e := primeSubsetGenerator P E
        let Ke := K / ‖eisEmbedding e‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        (ξ (Ideal.Quotient.mk _ e) * χa (Ideal.Quotient.mk _ e) *
          star (χb (Ideal.Quotient.mk _ e))) *
        ((Ke / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
        (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
          star (χb (Ideal.Quotient.mk _ (r * a)))) *
        ∑' j : O, (residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
          residueGauss a ha χa (Ideal.Quotient.mk _ j) *
          star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
          paperRadialFourier W
            (Ke * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  let χ := productCharacter r (a * b) hrab ξ (productCharacter a b hab χa χb⁻¹)
  have hm : r * (a * b) ≠ 0 := mul_ne_zero hr (mul_ne_zero ha hb)
  let := finite_quotient_span hm
  let := finite_quotient_span hb
  let : Fintype (Residue (r * (a * b))) := Fintype.ofFinite _
  let row := fun z : O => ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
    star (χb (Ideal.Quotient.mk _ z))
  have hχ (z : O) : χ (Ideal.Quotient.mk _ z) = row z := by
    simp only [χ, row, productCharacter_mk, MulChar.star_apply', mul_assoc]
  have hsum : Summable (fun z : O => row z * W (‖eisEmbedding z‖ ^ 2 / K)) := by
    have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
      (Ideal.Quotient.mk (Ideal.span {r * (a * b)})) χ
    simpa only [hχ, scaledRadialTest_apply] using hs
  have hmul (x y : O) : row (x * y) = row x * row y := by
    simp only [row, map_mul, star_mul]
    ring
  rw [tsum_masked_radial_dilations P hinj S row hmul W K hsum]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  rw [triple_pair_poisson r a b hr ha hb hrab hab ξ χa χb W
    (K / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)
    (primeSubset_reducedScale_pos P E hK)]
  ring

theorem normalized_triple_pair_poisson
    (r a b : O) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hrab : IsCoprime r (a * b)) (hab : IsCoprime a b)
    (ξ : MulChar (Residue r) ℂ) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O, (ξ (Ideal.Quotient.mk _ z) * χa (Ideal.Quotient.mk _ z) *
      star (χb (Ideal.Quotient.mk _ z))) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {r}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {b}) : ℝ) : ℂ))) *
      (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
        star (χb (Ideal.Quotient.mk _ (r * a)))) *
      ∑' j : O, (normalizedResidueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) *
        paperRadialFourier W
          (K * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  have hnr : (‖eisEmbedding r‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hr))
  have hna : (‖eisEmbedding a‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))
  have hnb : (‖eisEmbedding b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hb))
  have hpoint (j : O) : residueGauss r hr ξ (Ideal.Quotient.mk _ j) *
      residueGauss a ha χa (Ideal.Quotient.mk _ j) *
      star (residueGauss b hb χb (Ideal.Quotient.mk _ (-j))) =
      ((‖eisEmbedding r‖ : ℂ) * (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ)) *
      (normalizedResidueGauss r hr ξ (Ideal.Quotient.mk _ j) *
        normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ j) *
        star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-j)))) := by
    simp only [normalizedResidueGauss, CenteredMomentPrimitive.sqrt_absNorm,
      star_div₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
  rw [triple_pair_poisson r a b hr ha hb hrab hab ξ χa χb W K hK]
  simp_rw [hpoint, mul_assoc, tsum_mul_left, CenteredMomentPrimitive.sqrt_absNorm]
  simp only [map_mul, norm_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul]
  field_simp

end SevenEighths.CenteredMomentBridge
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.Initial -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentInitial
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentPrimitive CenteredMomentBridge

variable {ι : Type*}

abbrev activeModulus (P : ι → Ideal O) (B : Finset ι) (c d : ι → ℕ) : O :=
  finitePrimeModulus (fun i : CenteredMomentActive.activeSupport B c d => P i.val)

def commonCharacter (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (B : Finset ι) (c d : ι → ℕ) : MulChar (Residue (activeModulus P B c d)) ℂ :=
  primitiveCharacter (fun i : CenteredMomentActive.activeSupport B c d => P i.val)
    (CenteredMomentActive.activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => CenteredMomentActive.netExponent (c i.val) (d i.val))

theorem activeModulus_ne_zero (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (B : Finset ι) (c d : ι → ℕ) : activeModulus P B c d ≠ 0 :=
  finitePrimeModulus_ne_zero _

theorem activeModulus_coprime (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (B : Finset ι) (c d : ι → ℕ) (v : O)
    (hcop : ∀ i ∈ B, IsCoprime (P i) (Ideal.span {v})) :
    IsCoprime (activeModulus P B c d) v := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [activeModulus, span_finitePrimeModulus]
  apply IsCoprime.prod_left
  intro i _
  exact hcop i.val (Finset.mem_filter.mp i.property).1

theorem allocated_pair_factor (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) (z : O) :
    idealRowHom z ((∏ i ∈ B, P i ^ c i) * Ideal.span {a}) *
      star (idealRowHom z ((∏ i ∈ B, P i ^ d i) * Ideal.span {b})) =
      rowCoprimeMask P (CenteredMomentActive.principalSupport B c d) z *
      (commonCharacter P hinj hg B c d (Ideal.Quotient.mk _ z) *
        supportedModulusCharacter a ha (Ideal.Quotient.mk _ z) *
        star (supportedModulusCharacter b hb (Ideal.Quotient.mk _ z))) := by
  calc
    _ = (idealRowHom z (∏ i ∈ B, P i ^ c i) *
        star (idealRowHom z (∏ i ∈ B, P i ^ d i))) *
        (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) := by
      rw [map_mul, map_mul, star_mul]
      ring
    _ = _ := by
      rw [CenteredMomentActive.common_ideal_pair_active P hg hchar B c d hc hd]
      simp only [commonCharacter, primitiveCharacter_mk, supportedModulusCharacter_mk]
      ring

theorem allocated_pair_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hcop : ∀ i ∈ B, IsCoprime (P i) (Ideal.span {a * b})) (hab : IsCoprime a b)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    let r := activeModulus P B c d
    let ξ := commonCharacter P hinj hg B c d
    let χa := supportedModulusCharacter a ha
    let χb := supportedModulusCharacter b hb
    (∑' z : O, (idealRowHom z ((∏ i ∈ B, P i ^ c i) * Ideal.span {a}) *
      star (idealRowHom z ((∏ i ∈ B, P i ^ d i) * Ideal.span {b}))) *
      W (‖eisEmbedding z‖ ^ 2 / K)) =
      ∑ E ∈ (CenteredMomentActive.principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        let Ke := K / ‖eisEmbedding e‖ ^ 2
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        (ξ (Ideal.Quotient.mk _ e) * χa (Ideal.Quotient.mk _ e) *
          star (χb (Ideal.Quotient.mk _ e))) *
        ((Ke / ‖eisEmbedding (r * (a * b))‖ ^ 2 : ℝ) : ℂ) *
        (ξ (Ideal.Quotient.mk _ (a * b)) * χa (Ideal.Quotient.mk _ (r * b)) *
          star (χb (Ideal.Quotient.mk _ (r * a)))) *
        ∑' j : O, (residueGauss r (activeModulus_ne_zero P B c d) ξ (Ideal.Quotient.mk _ j) *
          residueGauss a (supported_element_ne_zero a ha) χa (Ideal.Quotient.mk _ j) *
          star (residueGauss b (supported_element_ne_zero b hb) χb (Ideal.Quotient.mk _ (-j)))) *
          paperRadialFourier W
            (Ke * ‖eisEmbedding j‖ ^ 2 / ‖eisEmbedding (r * (a * b))‖ ^ 2) := by
  simp_rw [allocated_pair_factor P hinj hg hchar B c d hc hd a b ha hb]
  exact masked_triple_pair_poisson P hinj (CenteredMomentActive.principalSupport B c d)
    (activeModulus P B c d) a b (activeModulus_ne_zero P B c d)
    (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
    (activeModulus_coprime P B c d (a * b) hcop) hab
    (commonCharacter P hinj hg B c d) (supportedModulusCharacter a ha)
    (supportedModulusCharacter b hb) W K hK

theorem common_gauss_norm_le_one (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ) (h : O) :
    ‖normalizedResidueGauss (activeModulus P B c d) (activeModulus_ne_zero P B c d)
      (commonCharacter P hinj hg B c d) (Ideal.Quotient.mk _ h)‖ ≤ 1 :=
  normalized_primitive_gauss_norm_le_one
    (fun i : CenteredMomentActive.activeSupport B c d => P i.val)
    (CenteredMomentActive.activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => CenteredMomentActive.netExponent (c i.val) (d i.val))
    (CenteredMomentActive.netExponent_ne_zero B c d)
    (fun _i => CenteredMomentActive.netExponent_lt_six _ _) h

end SevenEighths.CenteredMomentInitial
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.Rankin -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter
namespace SevenEighths.CenteredMomentRankin
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def primeMass (P : Ideal O) (δ : ℝ) : ℝ := ((Ideal.absNorm P:ℝ)^δ-1)⁻¹

theorem prime_norm_ge_two (P : Ideal O) (hp : Prime P) : 2 ≤ Ideal.absNorm P := by
  have h0 := Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero
  have h1 : Ideal.absNorm P ≠ 1 := by
    intro hn
    exact hp.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp hn))
  omega

theorem primeMass_nonneg (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ primeMass P δ := by
  apply inv_nonneg.mpr
  have hn : (1:ℝ) < Ideal.absNorm P := by exact_mod_cast (prime_norm_ge_two P hp)
  exact (sub_pos.mpr (Real.one_lt_rpow hn hδ)).le

theorem primeMass_le_fixed (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) :
    primeMass P δ ≤ ((2:ℝ)^δ-1)⁻¹ := by
  apply inv_anti₀ (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hδ))
  exact sub_le_sub_right (Real.rpow_le_rpow (by norm_num)
    (by exact_mod_cast prime_norm_ge_two P hp) hδ.le) 1

theorem uniform_primeMass_product (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset (Ideal O), (∀ P ∈ S,Prime P) →
      (∏ P ∈ S,primeMass P δ) ≤ C := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2:ℝ)))
  let small : Finset (Ideal O) := (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset
  let B : ℝ := max 1 (((2:ℝ)^δ-1)⁻¹)
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨B^small.card,pow_pos (zero_lt_one.trans_le hB) _,?_⟩
  intro S hp
  have hs (P : Ideal O) (hP : P ∈ S∩small) : primeMass P δ ≤ B :=
    (primeMass_le_fixed P (hp P (Finset.mem_inter.mp hP).1) δ hδ).trans (le_max_right _ _)
  have hl (P : Ideal O) (hP : P ∈ S\small) : primeMass P δ ≤ 1 := by
    have hn : N < Ideal.absNorm P := by
      by_contra hn
      apply (Finset.mem_sdiff.mp hP).2
      simpa only [small,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using le_of_not_gt hn
    have hpow := hN (Ideal.absNorm P) hn.le
    apply inv_le_one_of_one_le₀
    linarith
  have he : S=(S∩small)∪(S\small) := by
    ext P
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have hdis : Disjoint (S∩small) (S\small) := Finset.disjoint_left.mpr
    (fun P hP hQ => (Finset.mem_sdiff.mp hQ).2 (Finset.mem_inter.mp hP).2)
  rw [he,Finset.prod_union hdis]
  have hleft : (∏ P ∈ S∩small,primeMass P δ) ≤ B^small.card := by
    calc
      _ ≤ ∏ _P ∈ S∩small,B := Finset.prod_le_prod₀
        (fun P hP => primeMass_nonneg P (hp P (Finset.mem_inter.mp hP).1) δ hδ) hs
      _ = B^(S∩small).card := by simp
      _ ≤ _ := pow_le_pow_right₀ hB (Finset.card_le_card Finset.inter_subset_right)
  have hright : (∏ P ∈ S\small,primeMass P δ) ≤ 1 :=
    Finset.prod_le_one₀ (fun P hP => primeMass_nonneg P (hp P (Finset.mem_sdiff.mp hP).1) δ hδ) hl
  exact (mul_le_mul hleft hright (Finset.prod_nonneg
    (fun P hP => primeMass_nonneg P (hp P (Finset.mem_sdiff.mp hP).1) δ hδ)) (by positivity)).trans_eq (mul_one _)

theorem local_power_sum (P : Ideal O) (hp : Prime P) (δ : ℝ) (hδ : 0 < δ) (K : ℕ) :
    (∑ n ∈ Finset.range K,((Ideal.absNorm P:ℝ)^(n+1))^(-δ)) ≤ primeMass P δ := by
  let q : ℝ := (Ideal.absNorm P:ℝ)^δ
  have hNP : (1:ℝ)<Ideal.absNorm P := by exact_mod_cast prime_norm_ge_two P hp
  have hq : 1 < q := Real.one_lt_rpow hNP hδ
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hr0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hr1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hsum := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left q⁻¹).summable.sum_le_tsum
    (Finset.range K) (fun n _ => mul_nonneg hr0 (pow_nonneg hr0 n))
  rw [((hasSum_geometric_of_lt_one hr0 hr1).mul_left q⁻¹).tsum_eq] at hsum
  have he (n : ℕ) : ((Ideal.absNorm P:ℝ)^(n+1))^(-δ)=q⁻¹*(q⁻¹)^n := by
    rw [← Real.rpow_natCast_mul (by linarith : (0:ℝ)≤Ideal.absNorm P),mul_comm,
      Real.rpow_mul_natCast (by linarith : (0:ℝ)≤Ideal.absNorm P),Real.rpow_neg (by linarith),pow_succ]
    dsimp only [q]
    ring
  simp_rw [he]
  apply hsum.trans_eq
  change q⁻¹*(1-q⁻¹)⁻¹=(q-1)⁻¹
  field_simp

end SevenEighths.CenteredMomentRankin

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RankinCount -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinCount
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentRankin
local notation "O" => ActualEisensteinCubic.O

def powerCode (R : Finset (Ideal O)) (I : Ideal O) (P : R) : ℕ :=
  (normalizedFactors I).count (P:Ideal O)-1

theorem powerCode_reconstruct (R : Finset (Ideal O)) (I : Ideal O) (hI : I ≠ 0)
    (hR : primeSupport I=R) :
    I=∏ P : R,(P:Ideal O)^(powerCode R I P+1) := by
  have he (P : R) : powerCode R I P+1=(normalizedFactors I).count (P:Ideal O) := by
    have hp : (P:Ideal O) ∈ primeSupport I := hR ▸ P.property
    have hc := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp)
    dsimp only [powerCode]
    omega
  simp_rw [he]
  calc
    I=(normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
    _=∏ P ∈ (normalizedFactors I).toFinset,P^(normalizedFactors I).count P := Finset.prod_multiset_count _
    _=∏ P : R,(P:Ideal O)^(normalizedFactors I).count (P:Ideal O) := by
      rw [Finset.prod_coe_sort R (fun P : Ideal O => P^(normalizedFactors I).count P)]
      change _=∏ P ∈ R,P^(normalizedFactors I).count P
      rw [← hR]
      rfl

theorem powerCode_injOn (R : Finset (Ideal O)) (S : Finset (Ideal O))
    (hS : ∀ I ∈ S,I ≠ 0) (hR : ∀ I ∈ S,primeSupport I=R) :
    Set.InjOn (powerCode R) S := by
  intro I hI J hJ he
  rw [powerCode_reconstruct R I (hS I hI) (hR I hI),powerCode_reconstruct R J (hS J hJ) (hR J hJ),he]

theorem ideal_mass_eq (R : Finset (Ideal O)) (I : Ideal O) (hI : I ≠ 0)
    (hR : primeSupport I=R) (δ : ℝ) :
    (Ideal.absNorm I:ℝ)^(-δ)=
      ∏ P : R,((Ideal.absNorm (P:Ideal O):ℝ)^(powerCode R I P+1))^(-δ) := by
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)^(-δ))
    (powerCode_reconstruct R I hI hR)
  simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow] at he
  rw [he]
  exact (Real.finsetProd_rpow _ _ (fun _ _ => pow_nonneg (Nat.cast_nonneg _) _) _).symm

theorem fixed_support_mass (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : Finset (Ideal O)),
      (∀ P ∈ R,Prime P) → (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I=R) →
      (∑ I ∈ S,(Ideal.absNorm I:ℝ)^(-δ)) ≤ C := by
  obtain ⟨C,hC,hprod⟩ := uniform_primeMass_product δ hδ
  refine ⟨C,hC,?_⟩
  intro R S hR hS hsupport
  let K : ℕ := S.sup (fun I => Finset.univ.sup (powerCode R I))+1
  let mass : (R → ℕ) → ℝ := fun v => ∏ P : R,((Ideal.absNorm (P:Ideal O):ℝ)^(v P+1))^(-δ)
  have hm (v : R → ℕ) : 0 ≤ mass v := Finset.prod_nonneg
    (fun _ _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)
  have hsub : S.image (powerCode R) ⊆ Fintype.piFinset (fun _P : R => Finset.range K) := by
    intro v hv
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hv
    apply Fintype.mem_piFinset.mpr
    intro P
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Finset.le_sup (f := powerCode R I) (Finset.mem_univ P)).trans
      (Finset.le_sup (f := fun I => Finset.univ.sup (powerCode R I)) hI))
  calc
    _ = ∑ v ∈ S.image (powerCode R),mass v := by
      rw [Finset.sum_image (powerCode_injOn R S hS hsupport)]
      apply Finset.sum_congr rfl
      intro I hI
      exact ideal_mass_eq R I (hS I hI) (hsupport I hI) δ
    _ ≤ ∑ v ∈ Fintype.piFinset (fun _P : R => Finset.range K),mass v :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => hm v)
    _ = ∏ P : R,∑ n ∈ Finset.range K,((Ideal.absNorm (P:Ideal O):ℝ)^(n+1))^(-δ) := by
      exact (Finset.prod_univ_sum (fun _P : R => Finset.range K)
        (fun P n => ((Ideal.absNorm (P:Ideal O):ℝ)^(n+1))^(-δ))).symm
    _ ≤ ∏ P : R,primeMass P δ := Finset.prod_le_prod₀
      (fun _ _ => Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _))
      (fun P _ => local_power_sum P (hR P P.property) δ hδ K)
    _ ≤ C := by
      have he := Finset.prod_coe_sort R (fun P => primeMass P δ)
      rw [he]
      exact hprod R hR

theorem fixed_support_count (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R S : Finset (Ideal O)),
      (∀ P ∈ R,Prime P) → (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I=R) →
      ∀ X : ℝ,0 < X → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ X) →
      (S.card:ℝ) ≤ C*X^δ := by
  obtain ⟨C,hC,hmass⟩ := fixed_support_mass δ hδ
  refine ⟨C,hC,?_⟩
  intro R S hR hS hs X hX hN
  have hterm (I : Ideal O) (hI : I ∈ S) : (1:ℝ) ≤ X^δ*(Ideal.absNorm I:ℝ)^(-δ) := by
    have hn : (0:ℝ)<Ideal.absNorm I := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
    have hr := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hn.le (hN I hI) hδ.le)
      (Real.rpow_nonneg hn.le (-δ))
    simpa only [← Real.rpow_add hn,add_neg_cancel,Real.rpow_zero] using hr
  calc
    _ = ∑ _I ∈ S,(1:ℝ) := by simp
    _ ≤ ∑ I ∈ S,X^δ*(Ideal.absNorm I:ℝ)^(-δ) := Finset.sum_le_sum (fun I hI => hterm I hI)
    _ = X^δ*∑ I ∈ S,(Ideal.absNorm I:ℝ)^(-δ) := (Finset.mul_sum _ _ _).symm
    _ ≤ X^δ*C := mul_le_mul_of_nonneg_left (hmass R S hR hS hs) (Real.rpow_nonneg hX.le _)
    _ = _ := mul_comm _ _

end SevenEighths.CenteredMomentRankinCount

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RankinSubset -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinSubset
open IdealMobiusDivisorSum CenteredMomentRankinCount
local notation "O" => ActualEisensteinCubic.O

theorem supported_power_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (Q : Ideal O),Q ≠ 0 → ∀ S : Finset (Ideal O),
      (∀ I ∈ S,I ≠ 0) → (∀ I ∈ S,primeSupport I ⊆ primeSupport Q) →
      ∀ X : ℝ,0 < X → (∀ I ∈ S,(Ideal.absNorm I:ℝ) ≤ X) →
      (S.card:ℝ) ≤ C*X^a*(Ideal.absNorm Q:ℝ)^ε := by
  obtain ⟨C,hC,hcount⟩ := fixed_support_count a ha
  obtain ⟨D,hD,hsub⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Q hQ S hS hs X hX hN
  have hf : ∀ I ∈ S,primeSupport I ∈ (primeSupport Q).powerset :=
    fun I hI => Finset.mem_powerset.mpr (hs I hI)
  have he := Finset.card_eq_sum_card_fiberwise hf
  have hfiber (R : Finset (Ideal O)) (hR : R ∈ (primeSupport Q).powerset) :
      ((S.filter (fun I => primeSupport I=R)).card:ℝ) ≤ C*X^a := by
    apply hcount R _ (fun P hP => support_prime ((Finset.mem_powerset.mp hR) hP))
      (fun I hI => hS I (Finset.mem_filter.mp hI).1)
      (fun I hI => (Finset.mem_filter.mp hI).2) X hX
      (fun I hI => hN I (Finset.mem_filter.mp hI).1)
  calc
    _ = ∑ R ∈ (primeSupport Q).powerset,((S.filter (fun I => primeSupport I=R)).card:ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _R ∈ (primeSupport Q).powerset,C*X^a := Finset.sum_le_sum hfiber
    _ = (2:ℝ)^(primeSupport Q).card*(C*X^a) := by simp
    _ ≤ (D*(Ideal.absNorm Q:ℝ)^ε)*(C*X^a) :=
      mul_le_mul_of_nonneg_right (hsub Q hQ) (mul_nonneg hC.le (Real.rpow_nonneg hX.le _))
    _ = _ := by ring

theorem supported_power_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (Q : Ideal O),Q ≠ 0 → ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S,v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1 ⊆ primeSupport Q ∧ primeSupport v.2 ⊆ primeSupport Q) →
      ∀ X Y : ℝ,0 < X → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1:ℝ) ≤ X ∧ (Ideal.absNorm v.2:ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X^a*Y^a*(Ideal.absNorm Q:ℝ)^ε := by
  obtain ⟨C,hC,hcount⟩ := supported_power_count a (ε/2) ha (by positivity)
  refine ⟨C^2,pow_pos hC _,?_⟩
  intro Q hQ S hS hs X Y hX hY hN
  have hfst : ((S.image Prod.fst).card:ℝ) ≤ C*X^a*(Ideal.absNorm Q:ℝ)^(ε/2) := by
    refine hcount Q hQ _ ?_ ?_ X hX ?_
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hS v hv).1
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hs v hv).1
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hN v hv).1
  have hsnd : ((S.image Prod.snd).card:ℝ) ≤ C*Y^a*(Ideal.absNorm Q:ℝ)^(ε/2) := by
    refine hcount Q hQ _ ?_ ?_ Y hY ?_
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hS v hv).2
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hs v hv).2
    · intro I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact (hN v hv).2
  have hin : S ⊆ (S.image Prod.fst) ×ˢ (S.image Prod.snd) := by
    intro v hv
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hv,Finset.mem_image_of_mem _ hv⟩
  have hn : (0:ℝ) < Ideal.absNorm Q := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  calc
    _ ≤ ((S.image Prod.fst).card:ℝ)*((S.image Prod.snd).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hin).trans_eq (Finset.card_product _ _)
    _ ≤ (C*X^a*(Ideal.absNorm Q:ℝ)^(ε/2))*(C*Y^a*(Ideal.absNorm Q:ℝ)^(ε/2)) :=
      mul_le_mul hfst hsnd (Nat.cast_nonneg _) (by positivity)
    _ = C^2*X^a*Y^a*((Ideal.absNorm Q:ℝ)^(ε/2)*(Ideal.absNorm Q:ℝ)^(ε/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

end SevenEighths.CenteredMomentRankinSubset

end

end OAI

end

