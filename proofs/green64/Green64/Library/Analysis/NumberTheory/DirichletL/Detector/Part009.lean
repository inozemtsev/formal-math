module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part019
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Detector / Part009

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsCentralQuotient -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma unramifiedClosed_central_lower (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖unramifiedClosed Q A eta v x w z‖ := by
  have hQ0 : 0<Q := by linarith
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (10*e)
    (by linarith) hA heta hv (by positivity) (by rw [hx];linarith)
    (by rw [hz]) (by rw [hw];linarith) (by rw [hx,hw];linarith)
  have hp : Q^(-1-min (10*e) (1/50:ℝ))≤Q^(-1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by
      have hm : 0≤ min (10*e) (1/50:ℝ) := by positivity
      linarith)
  have hi : Q^(-1:ℝ)≤1/480 := by
    rw [Real.rpow_neg_one,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) hQ
  have ht := norm_sub_le (1:ℂ) (unramifiedClosed Q A eta v x w z)
  have ht' := norm_add_le (1-unramifiedClosed Q A eta v x w z)
    (unramifiedClosed Q A eta v x w z)
  rw [sub_add_cancel,norm_one,norm_sub_rev] at ht'
  nlinarith

lemma unramifiedSelected_central_quotient (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖unramifiedSelected Q A eta v x w z/unramifiedClosed Q A eta v x w z+star v‖≤
      1440*Q^(-(51/100:ℝ)) := by
  have hh := unramifiedClosed_central_lower Q a e A eta v x w z hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  have hn : unramifiedClosed Q A eta v x w z≠0 := by
    intro hz;rw [hz,norm_zero] at hh;norm_num at hh
  have hp : 0<‖unramifiedClosed Q A eta v x w z‖ := by linarith
  have hb := unramifiedSelected_central_error Q a e A eta v x w z
    (by linarith) ha ha1 he he1 hA heta hv hx hw hz
  have hid : unramifiedSelected Q A eta v x w z/unramifiedClosed Q A eta v x w z+star v=
      (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)/
      unramifiedClosed Q A eta v x w z := by field_simp
  rw [hid,norm_div]
  apply (div_le_iff₀ hp).mpr
  have ht : 0≤Q^(-(51/100:ℝ)) := Real.rpow_nonneg (by linarith) _
  nlinarith
end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedActual -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma elementCoeff_zero_or_norm_one (eta : HeckeFamily.Character) (p : O) :
    HeckeFamily.elementCoeff eta p=0 ∨ ‖HeckeFamily.elementCoeff eta p‖=1 := by
  by_cases h : HeckeFamily.elementCoeff eta p=0
  · exact Or.inl h
  · right
    let : Finite (O ⧸ eta.modulus) := Ring.HasFiniteQuotients.finiteQuotient eta.modulus_ne_bot
    let : Fintype (O ⧸ eta.modulus) := Fintype.ofFinite _
    have hu : IsUnit (Ideal.Quotient.mk eta.modulus p) := eta.residue.apply_ne_zero_iff.mp h
    obtain ⟨u,hu⟩ := hu
    change ‖eta.residue (Ideal.Quotient.mk eta.modulus p)‖=1
    rw [←hu]
    exact FiniteRayExpansion.norm_char_unit eta.residue u

def actualUnramifiedSelected (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (x w z : ℂ) : ℂ :=
  unramifiedSelected (Ideal.absNorm (Ideal.span {p})) (actualAPhase eta p)
    (HeckeFamily.elementCoeff eta p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u)) x w z

theorem actualUnramifiedSelected_bound (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hu : IsCoprime u p)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (x w z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖actualUnramifiedSelected eta p u hg x w z‖≤961 := by
  have hv := Complex.norm_eq_one_of_pow_eq_one (ProbePhysical.actualSextic_unit_six p u hg hc hu) (by decide : (6:ℕ)≠0)
  unfold actualUnramifiedSelected
  rcases elementCoeff_zero_or_norm_one eta p with heta|heta
  · have hA : actualAPhase eta p=0 := by simp [actualAPhase,heta]
    rw [heta,hA]
    exact (unramifiedSelected_zero_bound _ _ x w z hQ hv.le hw hz).trans (by norm_num)
  · exact unramifiedSelected_bound _ _ _ _ x w z hQ (actualAPhase_norm_le_one eta p) heta hv hx hw hz

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SelectedPrimeSums -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

lemma finite_ideal_count (S : Finset (Ideal O)) (H : ℝ) (hH : 0≤H)
    (hS : ∀I∈S,I≠0) (hN : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (S.card:ℝ)≤128*H := by
  by_cases hh : 1≤H
  · exact DescentFiberCost.finite_ideal_count_real S H hh hS hN
  · have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hI
      have hp : (1:ℝ)≤Ideal.absNorm I := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
      have := hN I hI
      linarith
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

lemma ramified_card_bound (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ, 0<C ∧ ∀ (U : Ideal O), U≠0 → ∀S : Finset (Ideal O),
      ((S.filter (fun P=>P∣U)).card:ℝ)≤C*(Ideal.absNorm U:ℝ)^eps := by
  obtain ⟨C,hC,hb⟩ := IdealDivisorBound.ideal_divisor_small_power eps heps
  refine ⟨C,hC,?_⟩
  intro U hU S
  apply (show ((S.filter (fun P=>P∣U)).card:ℝ)≤(IdealMobiusDivisorSum.idealDivisors U).card from ?_).trans (hb U hU)
  exact_mod_cast Finset.card_le_card (show S.filter (fun P=>P∣U)⊆IdealMobiusDivisorSum.idealDivisors U from by
    intro P hP
    exact (IdealMobiusDivisorSum.mem_idealDivisors hU).mpr (Finset.mem_filter.mp hP).2)

def annularPower (a b r : ℝ) : ℝ := max (a^r) (b^r)

lemma annularPower_nonneg (a b r : ℝ) (ha : 0<a) : 0≤annularPower a b r :=
  (Real.rpow_nonneg ha.le _).trans (le_max_left _ _)

lemma annular_rpow (a b P q r : ℝ) (ha : 0<a) (hb : 0<b) (hP : 0<P)
    (hqa : a*P≤q) (hqb : q≤b*P) : q^r≤annularPower a b r*P^r := by
  have hq : 0<q := (mul_pos ha hP).trans_le hqa
  by_cases hr : 0≤ r
  · calc
      q^r≤(b*P)^r := Real.rpow_le_rpow hq.le hqb hr
      _=b^r*P^r := Real.mul_rpow hb.le hP.le
      _≤annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hP.le _)
  · calc
      q^r≤(a*P)^r := Real.rpow_le_rpow_of_nonpos (mul_pos ha hP) hqa (by linarith)
      _=a^r*P^r := Real.mul_rpow ha.le hP.le
      _≤annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hP.le _)

theorem annular_slot_majorant (eps a b r d : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) :
    ∃C : ℝ, 0<C ∧ ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀S : Finset (Ideal O), (∀I∈S,I≠0) →
      (∀I∈S,a*P≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤b*P) →
      (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1))
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨D,hD,hdiv⟩ := ramified_card_bound eps heps
  let A := annularPower a b (r-1)
  let B := annularPower a b (r-1+d)
  have hA : 0≤A := annularPower_nonneg a b _ ha
  have hB : 0≤B := annularPower_nonneg a b _ ha
  refine ⟨1+128*b*A+D*B,by positivity,?_⟩
  intro U hU P hP S hS hSP
  have hP0 : 0<P := by linarith
  have hU1 : (1:ℝ)≤Ideal.absNorm U := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU)
  have hUpow : 1≤(Ideal.absNorm U:ℝ)^eps := Real.one_le_rpow hU1 heps.le
  have hq (I : Ideal O) (hI : I∈S) : 0<(Ideal.absNorm I:ℝ) :=
    (mul_pos ha hP0).trans_le (hSP I hI).1
  have hc := finite_ideal_count S (b*P) (by positivity) hS (fun I hI=>(hSP I hI).2)
  have heP : P*P^(r-1)=P^r := by
    calc
      _=P^(1:ℝ)*P^(r-1) := by rw [Real.rpow_one]
      _=P^r := by rw [←Real.rpow_add hP0];congr 1;ring
  have hfirst : (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1))≤128*b*A*P^r := by
    calc
      _≤∑_I∈S,A*P^(r-1) := Finset.sum_le_sum (fun I hI=>annular_rpow a b P _ _ ha hb hP0 (hSP I hI).1 (hSP I hI).2)
      _=(S.card:ℝ)*(A*P^(r-1)) := by simp
      _≤(128*(b*P))*(A*P^(r-1)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=128*b*A*(P*P^(r-1)) := by ring
      _=128*b*A*P^r := by rw [heP]
  have hsecond : (∑I∈S.filter (fun I=>I∣U),(Ideal.absNorm I:ℝ)^(r-1+d))≤
      D*B*(Ideal.absNorm U:ℝ)^eps*P^r := by
    have hpP : P^(r-1+d)≤P^r := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
    calc
      _≤∑_I∈S.filter (fun I=>I∣U),B*P^(r-1+d) := by
        apply Finset.sum_le_sum
        intro I hI
        exact annular_rpow a b P _ _ ha hb hP0 (hSP I (Finset.mem_filter.mp hI).1).1 (hSP I (Finset.mem_filter.mp hI).1).2
      _=((S.filter (fun I=>I∣U)).card:ℝ)*(B*P^(r-1+d)) := by simp
      _≤(D*(Ideal.absNorm U:ℝ)^eps)*(B*P^r) := by
        gcongr
        exact hdiv U hU S
      _=D*B*(Ideal.absNorm U:ℝ)^eps*P^r := by ring
  have hsum : (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1))≤
      (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1))+
        ∑I∈S.filter (fun I=>I∣U),(Ideal.absNorm I:ℝ)^(r-1+d) := by
    rw [Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro I hI
    split_ifs
    · rw [←Real.rpow_add (hq I hI)]
      exact le_add_of_nonneg_left (by positivity)
    · simp only [mul_one,add_zero,le_refl]
  apply hsum.trans
  have hup : 128*b*A*P^r≤128*b*A*(Ideal.absNorm U:ℝ)^eps*P^r := by
    nlinarith [mul_nonneg (show 0≤128*b*A*P^r by positivity) (show 0≤(Ideal.absNorm U:ℝ)^eps-1 by linarith)]
  nlinarith [mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤Ideal.absNorm U) eps) (Real.rpow_nonneg hP0.le r)]

theorem weighted_slot_bound (eps a b r d B K : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) (hB : 0≤B) (hK : 0≤K) :
    ∃C : ℝ, 0<C ∧ ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀(S : Finset (Ideal O)), (∀I∈S,I≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤B) →
    ∀(G : Ideal O→ℂ), (∀I∈S,‖G I‖≤K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑I∈S,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖)
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmajor⟩ := annular_slot_majorant eps a b r d heps ha hb hd
  refine ⟨(B*K+1)*C,by positivity,?_⟩
  intro U hU P hP S hS W hWS hWB G hG z hz
  have hP0 : 0<P := by linarith
  let T := S.filter (fun I=>W ((Ideal.absNorm I:ℝ)/P)≠0)
  have hTS : T⊆S := Finset.filter_subset _ _
  have hbounds (I : Ideal O) (hI : I∈T) : a*P≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤b*P := by
    have ht := hWS (show (Ideal.absNorm I:ℝ)/P∈Function.support W from (Finset.mem_filter.mp hI).2)
    exact ⟨(le_div_iff₀ hP0).mp ht.1,(div_le_iff₀ hP0).mp ht.2⟩
  have he : (∑I∈S,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖)=
      ∑I∈T,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖ := by
    symm
    apply Finset.sum_subset hTS
    intro I hI hn
    have hw : W ((Ideal.absNorm I:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
    simp only [hw,zero_mul,norm_zero]
  rw [he]
  have hpoint (I : Ideal O) (hI : I∈T) :
      ‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖≤
        (B*K)*((Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) := by
    have hN : (0:ℝ)<Ideal.absNorm I := (mul_pos ha hP0).trans_le (hbounds I hI).1
    have hc : ‖(Ideal.absNorm I:ℂ)^(z-1)‖=(Ideal.absNorm I:ℝ)^(r-1) := by
      simpa only [Complex.ofReal_natCast,Complex.sub_re,Complex.one_re,hz] using
        Complex.norm_cpow_eq_rpow_re_of_pos hN (z-1)
    simp only [norm_mul,hc]
    calc
      _≤B*(Ideal.absNorm I:ℝ)^(r-1)*(K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) := by
        gcongr
        · exact hWB _
        · exact hG I (hTS hI)
      _=_ := by ring
  have hmain := hmajor U hU P hP T (fun I hI=>hS I (hTS hI)) hbounds
  calc
    _≤∑I∈T,(B*K)*((Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) :=
      Finset.sum_le_sum hpoint
    _=(B*K)*∑I∈T,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) :=
      (Finset.mul_sum _ _ _).symm
    _≤(B*K)*(C*(Ideal.absNorm U:ℝ)^eps*P^r) := mul_le_mul_of_nonneg_left hmain (mul_nonneg hB hK)
    _≤((B*K+1)*C)*(Ideal.absNorm U:ℝ)^eps*P^r := by
      nlinarith [mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by positivity : (0:ℝ)≤Ideal.absNorm U) eps))
        (Real.rpow_nonneg hP0.le r)]

end SevenEighths.ProbeSelectedPrimeSums
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SelectedPrimeIndexed -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

lemma weighted_slot_bound_indexed (eps a b r d B K : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) (hB : 0≤B) (hK : 0≤K) :
    ∃C : ℝ, 0<C ∧ ∀{ι : Type*} (f : ι→Ideal O), Function.Injective f →
    ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀(S : Finset ι), (∀i∈S,f i≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤B) →
    ∀(G : ι→ℂ), (∀i∈S,‖G i‖≤K*(if f i∣U then (Ideal.absNorm (f i):ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑i∈S,‖W ((Ideal.absNorm (f i):ℝ)/P)*(Ideal.absNorm (f i):ℂ)^(z-1)*G i‖)
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmain⟩ := weighted_slot_bound eps a b r d B K heps ha hb hd hB hK
  refine ⟨C,hC,?_⟩
  intro ι f hf U hU P hP S hS W hWS hWB G hG z hz
  let G' : Ideal O→ℂ := Function.extend f G (fun _=>0)
  have he (i : ι) : G' (f i)=G i := hf.extend_apply G (fun _=>0) i
  have hI (I : Ideal O) (hI : I∈S.image f) : I≠0 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact hS i hi
  have hg (I : Ideal O) (hI : I∈S.image f) :
      ‖G' I‖≤K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    rw [he]
    exact hG i hi
  have hh := hmain U hU P hP (S.image f) hI W hWS hWB G' hg z hz
  rw [Finset.sum_image hf.injOn] at hh
  simpa only [he] using hh

end SevenEighths.ProbeSelectedPrimeSums
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.TraceCharacter -/

section

namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap

namespace SevenEighths.TraceCharacter

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic EisensteinEmbedding ConcreteTraceCRT
open EisensteinSchwartzPoisson FiniteFourier

def traceCharacter (c : O) (hc : c ≠ 0) : AddChar (O ⧸ Ideal.span {c}) ℂ :=
  eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc

theorem traceCharacter_mk (c : O) (hc : c ≠ 0) (x : O) :
    traceCharacter c hc (Ideal.Quotient.mk (Ideal.span {c}) x) =
      ShortDraftTrace.breveE (eisEmbedding x / (eisEmbedding c * eisLam)) := by
  simp only [traceCharacter, eisTraceModChar, IdealGaussCRT.traceModChar_mk]

theorem traceCharacter_eq_paperE (c : O) (hc : c ≠ 0) (x : O) :
    traceCharacter c hc (Ideal.Quotient.mk (Ideal.span {c}) x) =
      paperE (eisEmbedding x / eisEmbedding c) :=
  eisTraceModChar_eq_paperE c hc x

theorem traceCharacter_isPrimitive (c : O) (hc : c ≠ 0) :
    (traceCharacter c hc).IsPrimitive :=
  GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

theorem residue_card :
    Fintype.card (O ⧸ Ideal.span {c}) = Ideal.absNorm (Ideal.span {c}) := by
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

def gaussScalar (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  gaussSum χ (traceCharacter c (NeZero.ne c))

theorem transform_nonunit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) (ha : ¬ IsUnit a) :
    (∑ x : O ⧸ Ideal.span {c}, χ x * traceCharacter c (NeZero.ne c) (a * x)) = 0 :=
  gaussSum_mulShift_nonunit_eq_zero χ hχ (traceCharacter c (NeZero.ne c)) ha

theorem transform_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) :
    (∑ x : O ⧸ Ideal.span {c}, χ x * traceCharacter c (NeZero.ne c) (a * x)) =
      χ⁻¹ a * gaussScalar c χ :=
  transform_primitive_character χ hχ (traceCharacter c (NeZero.ne c)) a

theorem paper_transform_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (h : O) :
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      paperE (eisEmbedding (GaussianShiftedPartition.representative c x) *
        eisEmbedding h / eisEmbedding c)) =
      χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) * gaussScalar c χ := by
  simpa only [traceCharacter, eisTraceModChar_frequency] using
    transform_eq c χ hχ (Ideal.Quotient.mk (Ideal.span {c}) h)

theorem gaussScalar_norm_sq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ ^ 2 = (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  simpa only [gaussScalar, residue_card c] using
    primitive_gaussSum_norm_sq χ hχ (traceCharacter c (NeZero.ne c))
      (traceCharacter_isPrimitive c (NeZero.ne c))

theorem gaussScalar_norm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ = Real.sqrt (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  rw [← gaussScalar_norm_sq c χ hχ, Real.sqrt_sq (norm_nonneg _)]

theorem gaussScalar_norm_embedding (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ = ‖eisEmbedding c‖ := by
  rw [gaussScalar_norm c χ hχ, ← eisEmbedding_norm_sq_eq_absNorm_span,
    Real.sqrt_sq (norm_nonneg _)]

theorem gaussScalar_ne_zero (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : gaussScalar c χ ≠ 0 :=
  primitive_gaussSum_ne_zero χ hχ (traceCharacter c (NeZero.ne c))
    (traceCharacter_isPrimitive c (NeZero.ne c))

def normalizedGauss (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  gaussScalar c χ / (‖eisEmbedding c‖ : ℂ)

theorem normalizedGauss_norm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : ‖normalizedGauss c χ‖ = 1 := by
  rw [normalizedGauss, norm_div, gaussScalar_norm_embedding c χ hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))]

theorem character_expansion (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) :
    χ a = (∑ x : O ⧸ Ideal.span {c}, χ⁻¹ x * traceCharacter c (NeZero.ne c) (a * x)) /
      gaussScalar c χ⁻¹ :=
  primitive_character_expansion χ hχ (traceCharacter c (NeZero.ne c))
    (traceCharacter_isPrimitive c (NeZero.ne c)) a

theorem primitive_paper_poisson (f : 𝓢(ℂ, ℂ))
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (gaussScalar c χ / (Ideal.absNorm (Ideal.span {c}) : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  have hp := actual_eisenstein_paper_poisson_trace f c (NeZero.ne c) χ
  change _ = (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      traceCharacter c (NeZero.ne c) (Ideal.Quotient.mk (Ideal.span {c}) h * x)) *
        paperFourier f (eisEmbedding h / eisEmbedding c) at hp
  simp_rw [transform_eq c χ hχ] at hp
  rw [hp, ← tsum_mul_left]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    eisEmbedding_norm_sq_eq_absNorm_span, Complex.ofReal_natCast]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

theorem primitive_radial_paper_poisson (W : 𝓢(ℝ, ℂ)) (scale : ℝ)
    (hscale : 0 < scale) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * gaussScalar c χ / (Ideal.absNorm (Ideal.span {c}) : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (Ideal.span {c}) : ℝ)) := by
  have hp := actual_radial_paper_poisson_trace W scale hscale c (NeZero.ne c) χ
  change _ = (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      traceCharacter c (NeZero.ne c) (Ideal.Quotient.mk (Ideal.span {c}) h * x)) *
        paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [transform_eq c χ hχ, eisEmbedding_norm_sq_eq_absNorm_span c] at hp
  rw [hp, ← tsum_mul_left]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

theorem primitive_radial_paper_poisson_normalized (W : 𝓢(ℝ, ℂ)) (scale : ℝ)
    (hscale : 0 < scale) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * normalizedGauss c χ / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  have hp := primitive_radial_paper_poisson c W scale hscale χ hχ
  rw [← eisEmbedding_norm_sq_eq_absNorm_span c] at hp
  have hnorm : (Ideal.absNorm (Ideal.span {c}) : ℂ) = (‖eisEmbedding c‖ : ℂ) ^ 2 := by
    exact_mod_cast (eisEmbedding_norm_sq_eq_absNorm_span c).symm
  rw [hnorm] at hp
  rw [hp]
  congr 1
  rw [normalizedGauss]
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))
  field_simp

end SevenEighths.TraceCharacter

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.TraceConductor -/

section

namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap Classical

namespace SevenEighths.TraceConductor

abbrev O := ActualEisensteinCubic.O

open FiniteFourier CharacterTransport ConcretePrimeRowBridge
open ConcreteTraceCRT EisensteinSchwartzPoisson

structure PrimitivePresentation (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ) where
  generator : O
  generator_ne_zero : generator ≠ 0
  character : MulChar (O ⧸ Ideal.span {generator}) ℂ
  primitive : IsPrimitiveOnIdeals character
  modulus_le : M ≤ Ideal.span {generator}
  norm_le : Ideal.absNorm (Ideal.span {generator}) ≤ M.absNorm
  source_mask : ∀ a : O, χ (Ideal.Quotient.mk M a) =
    if IsUnit (Ideal.Quotient.mk M a) then
      character (Ideal.Quotient.mk (Ideal.span {generator}) a) else 0

theorem exists_primitivePresentation (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ) : Nonempty (PrimitivePresentation M χ) := by
  let : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  obtain ⟨K, φ, hMK, hK, hφ, hnorm, hmask⟩ :=
    ConductorPresentation.exists_primitive_presentation M χ
  let c := idealGenerator K
  let e : (O ⧸ Ideal.span {c}) ≃+* (O ⧸ K) :=
    Ideal.quotEquivOfEq (span_idealGenerator K)
  let θ := pullback e φ
  refine ⟨{
    generator := c
    generator_ne_zero := idealGenerator_ne_zero K hK
    character := θ
    primitive := primitive_pullback e φ hφ
    modulus_le := ?_
    norm_le := ?_
    source_mask := ?_ }⟩
  · simpa only [c, span_idealGenerator] using hMK
  · simpa only [c, span_idealGenerator] using hnorm
  · intro a
    simpa only [θ, pullback_apply, e, Ideal.quotEquivOfEq_mk] using hmask a

def primitivePresentation (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ) : PrimitivePresentation M χ :=
  Classical.choice (exists_primitivePresentation M hM χ)

namespace PrimitivePresentation

variable {M : Ideal O} {χ : MulChar (O ⧸ M) ℂ}

def conductor (P : PrimitivePresentation M χ) : Ideal O := Ideal.span {P.generator}

theorem conductor_ne_bot (P : PrimitivePresentation M χ) : P.conductor ≠ ⊥ := by
  intro h
  exact P.generator_ne_zero (Ideal.span_singleton_eq_bot.mp h)

def gauss (P : PrimitivePresentation M χ) : ℂ := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.gaussScalar P.generator P.character

theorem gauss_norm (P : PrimitivePresentation M χ) :
    ‖P.gauss‖ = Real.sqrt (P.conductor.absNorm : ℝ) := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.gaussScalar_norm P.generator P.character P.primitive

theorem gauss_ne_zero (P : PrimitivePresentation M χ) : P.gauss ≠ 0 := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.gaussScalar_ne_zero P.generator P.character P.primitive

def fourier (P : PrimitivePresentation M χ) (a : O ⧸ P.conductor) : ℂ := by
  let : Finite (O ⧸ Ideal.span {P.generator}) := finite_quotient_span P.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {P.generator}) := Fintype.ofFinite _
  exact transform (TraceCharacter.traceCharacter P.generator P.generator_ne_zero) P.character a

theorem fourier_eq (P : PrimitivePresentation M χ) (a : O ⧸ P.conductor) :
    P.fourier a = P.character⁻¹ a * P.gauss := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.transform_eq P.generator P.character P.primitive a

theorem fourier_nonunit (P : PrimitivePresentation M χ) (a : O ⧸ P.conductor)
    (ha : ¬ IsUnit a) : P.fourier a = 0 := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.transform_nonunit P.generator P.character P.primitive a ha

theorem source_sum_eq_masked (P : PrimitivePresentation M χ) (f : O → ℂ) :
    (∑' a : O, χ (Ideal.Quotient.mk M a) * f a) =
      ∑' a : O, (if IsUnit (Ideal.Quotient.mk M a) then
        P.character (Ideal.Quotient.mk P.conductor a) else 0) * f a := by
  apply tsum_congr
  intro a
  rw [P.source_mask]
  rfl

def normalizedGauss (P : PrimitivePresentation M χ) : ℂ := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.normalizedGauss P.generator P.character

theorem normalizedGauss_norm (P : PrimitivePresentation M χ) :
    ‖P.normalizedGauss‖ = 1 := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.normalizedGauss_norm P.generator P.character P.primitive

theorem paper_poisson (P : PrimitivePresentation M χ) (f : 𝓢(ℂ, ℂ)) :
    (∑' z : O, P.character (Ideal.Quotient.mk P.conductor z) * f (eisEmbedding z)) =
      (P.gauss / (P.conductor.absNorm : ℂ)) *
        ∑' h : O, P.character⁻¹ (Ideal.Quotient.mk P.conductor h) *
          paperFourier f (eisEmbedding h / eisEmbedding P.generator) := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.primitive_paper_poisson P.generator f P.character P.primitive

theorem radial_paper_poisson (P : PrimitivePresentation M χ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, P.character (Ideal.Quotient.mk P.conductor z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * P.normalizedGauss / (‖eisEmbedding P.generator‖ : ℂ)) *
        ∑' h : O, P.character⁻¹ (Ideal.Quotient.mk P.conductor h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding P.generator‖ ^ 2) := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.primitive_radial_paper_poisson_normalized
    P.generator W scale hscale P.character P.primitive

end PrimitivePresentation

end SevenEighths.TraceConductor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.GaussianTheta -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical FourierTransform

namespace SevenEighths.GaussianTheta

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic EisensteinEmbedding ConcreteTraceCRT EisensteinSchwartzPoisson

def gaussian (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (‖z‖ : ℂ) ^ 2)

def coordinate (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * omega3

theorem omega3_re : omega3.re = -(1 / 2 : ℝ) := by norm_num [omega3]

theorem coordinate_norm_sq (x y : ℝ) :
    ‖coordinate x y‖ ^ 2 = RankTwoEisShift.Q x y := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [coordinate, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, omega3_re, omega3_im, zero_mul, zero_add,
    add_zero, sub_zero]
  unfold RankTwoEisShift.Q
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem exists_coordinate (w : ℂ) : ∃ x y : ℝ, w = coordinate x y := by
  let v := (basisEquiv omega3 omega3_im_ne_zero).symm w
  refine ⟨v.re, v.im, ?_⟩
  have h := (basisEquiv omega3 omega3_im_ne_zero).apply_symm_apply w
  simpa only [basisEquiv_apply, coordinate, mul_comm] using h.symm

theorem coordinate_dual_phase (x y : ℝ) (p : ℤ × ℤ) :
    paperE (coordinate x y * eisEmbedding (dualFrequencyEquiv p)) =
      RankTwoEisShift.dualPhase p.1 p.2 x y := by
  rw [paperE_eq_exp, dualFrequencyEquiv_coordinates]
  simp only [coordinate, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, omega3_re, omega3_im,
    zero_mul, zero_add, add_zero, sub_zero, complexPoint]
  unfold RankTwoEisShift.dualPhase
  congr 1
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  push_cast
  field_simp
  ring

theorem gaussian_coordinate_shift (a x y : ℝ) (p : ℤ × ℤ) :
    gaussian a (eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) +
      coordinate x y) = RankTwoEisShift.shifted a x y p := by
  have he : eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) + coordinate x y =
      coordinate ((p.1 : ℝ) + x) ((p.2 : ℝ) + y) := by
    rw [eisEmbedding_eval]
    simp only [coordinate, Complex.ofReal_add, Complex.ofReal_intCast]
    ring
  rw [he]
  unfold gaussian RankTwoEisShift.shifted
  rw [← Complex.ofReal_pow, coordinate_norm_sq]
  congr 1
  push_cast
  ring

theorem gaussian_dual_coordinate (a : ℝ) (p : ℤ × ℤ) :
    gaussian a (eisEmbedding (dualFrequencyEquiv p)) =
      Complex.exp (((-Real.pi * a * RankTwoPoisson.eisQ (p.1, -p.2) : ℝ) : ℂ)) := by
  unfold gaussian
  rw [← Complex.ofReal_pow, dualFrequencyEquiv_norm_sq]
  unfold RankTwoPoisson.eisQ
  congr 1
  push_cast
  ring

theorem shifted_prefactor (a : ℝ) (ha : 0 < a) :
    (1 / (a : ℂ) ^ (1 / 2 : ℂ)) *
      (1 / (((3 * a / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) =
      ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) := by
  have h := EisensteinGaussianPrefactor.complex_eta_times_prefactor a 1 ha (by norm_num)
  simp only [mul_one] at h
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  apply (mul_left_cancel₀ ha0)
  rw [← mul_assoc, h]
  push_cast
  field_simp

theorem shifted_lattice_poisson (a : ℝ) (ha : 0 < a) (w : ℂ) :
    (∑' z : O, gaussian a (eisEmbedding z + w)) =
      ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) *
        ∑' h : O, paperE (w * eisEmbedding h) *
          gaussian (4 / (3 * a)) (eisEmbedding h) := by
  obtain ⟨x, y, rfl⟩ := exists_coordinate w
  have hp := RankTwoEisShift.shifted_eisenstein_gaussian_poisson ha x y
  rw [shifted_prefactor a ha] at hp
  change (∑' p : ℤ × ℤ, RankTwoEisShift.shifted a x y p) =
    ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) * ∑' p : ℤ × ℤ,
      Complex.exp (((-Real.pi * (4 / (3 * a)) * RankTwoPoisson.eisQ (p.1, -p.2) : ℝ) : ℂ)) *
        RankTwoEisShift.dualPhase p.1 p.2 x y at hp
  calc
    _ = ∑' p : ℤ × ℤ, gaussian a
        (eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) + coordinate x y) :=
      (latticeCoordEquiv.symm.tsum_eq _).symm
    _ = ∑' p : ℤ × ℤ, RankTwoEisShift.shifted a x y p := by
      apply tsum_congr
      exact gaussian_coordinate_shift a x y
    _ = _ := by
      rw [hp]
      congr 1
      rw [← dualFrequencyEquiv.tsum_eq]
      apply tsum_congr
      intro p
      rw [coordinate_dual_phase, gaussian_dual_coordinate]
      exact mul_comm _ _

theorem gaussian_mul (a : ℝ) (z w : ℂ) :
    gaussian a (z * w) = gaussian (a * ‖z‖ ^ 2) w := by
  unfold gaussian
  rw [norm_mul]
  congr 1
  push_cast
  ring

theorem gaussian_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun z : O => gaussian a (eisEmbedding z)) := by
  exact eis_gaussian_summable ha

theorem paperE_norm (z : ℂ) : ‖paperE z‖ = 1 := by
  rw [paperE_eq_exp, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem weighted_gaussian_summable {R : Type*} [Fintype R]
    (q : O → R) (P : R → ℂ) (a : ℝ) (ha : 0 < a) :
    Summable (fun z : O => P (q z) * gaussian a (eisEmbedding z)) := by
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun r _ => norm_nonneg (P r)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((gaussian_summable a ha).norm.mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP _) (norm_nonneg _)

theorem gaussian_coset_poisson (a : ℝ) (ha : 0 < a) (c : O) (hc : c ≠ 0) (r : O) :
    (∑' z : O, gaussian a (eisEmbedding (r + c * z))) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        ∑' h : O, paperE (eisEmbedding r * eisEmbedding h / eisEmbedding c) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  have hc' := eisEmbedding_ne_zero hc
  have hscale : 0 < a * ‖eisEmbedding c‖ ^ 2 :=
    mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hc'))
  have he (z : O) : eisEmbedding (r + c * z) =
      eisEmbedding c * (eisEmbedding z + eisEmbedding r / eisEmbedding c) := by
    rw [map_add, map_mul]
    field_simp
    ring
  simp_rw [he, gaussian_mul]
  rw [shifted_lattice_poisson _ hscale]
  congr 1
  apply tsum_congr
  intro h
  congr 2
  ring

theorem finite_gaussian_phase_sum {R : Type*} [Fintype R]
    (a : ℝ) (ha : 0 < a) (b : R → ℂ) (P : R → ℂ) (K : ℂ) :
    (∑ r : R, P r * (K * ∑' h : O,
      paperE (b r * eisEmbedding h) * gaussian a (eisEmbedding h))) =
      K * ∑' h : O, (∑ r : R, P r * paperE (b r * eisEmbedding h)) *
        gaussian a (eisEmbedding h) := by
  have hs (r : R) : Summable (fun h : O =>
      P r * (paperE (b r * eisEmbedding h) * gaussian a (eisEmbedding h))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [norm_mul, paperE_norm, one_mul] using (gaussian_summable a ha).norm
  simp_rw [mul_left_comm (P _) K, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r _ => (hs r).mul_left K)]
  apply tsum_congr
  intro h
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

theorem periodic_gaussian_poisson (P : O ⧸ Ideal.span {c} → ℂ)
    (a : ℝ) (ha : 0 < a) :
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        ∑' h : O, (∑ r : O ⧸ Ideal.span {c}, P r *
          TraceCharacter.traceCharacter c (NeZero.ne c)
            (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c})) P (fun z => gaussian a (eisEmbedding z))
    (weighted_gaussian_summable _ P a ha)]
  have hfiber (r : O ⧸ Ideal.span {c}) :=
    GaussianFiberEquiv.fiber_tsum c (NeZero.ne c) r
      (GaussianShiftedPartition.representative c r)
      (GaussianShiftedPartition.representative_spec c r)
      (fun z => gaussian a (eisEmbedding z))
  simp_rw [hfiber, gaussian_coset_poisson a ha c (NeZero.ne c)]
  have hd : 0 < 4 / (3 * (a * ‖eisEmbedding c‖ ^ 2)) := by
    exact div_pos (by norm_num) (mul_pos (by norm_num)
      (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))))))
  have h := finite_gaussian_phase_sum (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) hd
    (fun r => eisEmbedding (GaussianShiftedPartition.representative c r) / eisEmbedding c) P
    (((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ))
  simp_rw [TraceCharacter.traceCharacter, eisTraceModChar_frequency]
  convert h using 1 <;>
    congr 1 <;> (try ext r) <;>
    simp only [div_mul_eq_mul_div]

theorem primitive_gaussian_poisson (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (a : ℝ) (ha : 0 < a) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        TraceCharacter.gaussScalar c χ *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  have hp := periodic_gaussian_poisson c χ a ha
  simp_rw [TraceCharacter.transform_eq c χ hχ] at hp
  rw [hp]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

def parameter (t : ℝ) : ℝ := 2 * t / (Real.sqrt 3 * ‖eisEmbedding c‖)

def theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) : ℂ :=
  ∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
    gaussian (parameter c t) (eisEmbedding z)

theorem parameter_pos (t : ℝ) (ht : 0 < t) : 0 < parameter c t := by
  unfold parameter
  exact div_pos (mul_pos (by norm_num) ht)
    (mul_pos (Real.sqrt_pos.mpr (by norm_num))
      (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))))

theorem theta_summable (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 0 < t) :
    Summable (fun z : O => χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      gaussian (parameter c t) (eisEmbedding z)) :=
  weighted_gaussian_summable _ χ _ (parameter_pos c t ht)

theorem parameter_dual (t : ℝ) (ht : 0 < t) :
    4 / (3 * (parameter c t * ‖eisEmbedding c‖ ^ 2)) = parameter c (1 / t) := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  unfold parameter
  field_simp
  ring_nf
  norm_num [Real.sq_sqrt]

theorem parameter_prefactor (t : ℝ) (ht : 0 < t) :
    2 / (Real.sqrt 3 * (parameter c t * ‖eisEmbedding c‖ ^ 2)) =
      1 / (‖eisEmbedding c‖ * t) := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  unfold parameter
  field_simp

theorem theta_functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) (ht : 0 < t) :
    theta c χ t = (TraceCharacter.normalizedGauss c χ / (t : ℂ)) *
      theta c χ⁻¹ (1 / t) := by
  have hp := primitive_gaussian_poisson c χ hχ (parameter c t) (parameter_pos c t ht)
  rw [parameter_dual c t ht, parameter_prefactor c t ht] at hp
  change theta c χ t =
    (((1 / (‖eisEmbedding c‖ * t) : ℝ) : ℂ) * TraceCharacter.gaussScalar c χ) *
      theta c χ⁻¹ (1 / t) at hp
  rw [hp]
  congr 1
  unfold TraceCharacter.normalizedGauss
  push_cast
  ring

def constantTerm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ := χ 0

omit [NeZero c] in
theorem constantTerm_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    constantTerm c χ = if IsUnit c then 1 else 0 := by
  unfold constantTerm
  by_cases hu : IsUnit c
  · rw [ite_eq_left hu]
    have h10 : (1 : O ⧸ Ideal.span {c}) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [Ideal.span_singleton_eq_top.mpr hu]
      trivial
    rw [← h10, map_one]
  · rw [ite_eq_right hu]
    apply MulChar.map_nonunit
    intro hz
    have h10 := (isUnit_zero_iff.mp hz).symm
    have h1 : (1 : O) ∈ Ideal.span {c} := Ideal.Quotient.eq_zero_iff_mem.mp h10
    exact hu (Ideal.span_singleton_eq_top.mp ((Ideal.eq_top_iff_one _).mpr h1))

omit [NeZero c] in
theorem theta_zero_term (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) :
    χ (Ideal.Quotient.mk (Ideal.span {c}) (0 : O)) *
      gaussian (parameter c t) (eisEmbedding 0) = constantTerm c χ := by
  simp [gaussian, constantTerm]

theorem theta_inversion (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) (ht : 0 < t) :
    theta c χ (1 / t) = (TraceCharacter.normalizedGauss c χ * (t : ℂ)) * theta c χ⁻¹ t := by
  have h := theta_functional_equation c χ hχ (1 / t) (one_div_pos.mpr ht)
  simpa only [one_div, Complex.ofReal_inv, inv_inv, div_inv_eq_mul, one_mul] using h

theorem theta_root_nonzero (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) : TraceCharacter.normalizedGauss c χ ≠ 0 := by
  have h := TraceCharacter.normalizedGauss_norm c χ hχ
  intro hz
  rw [hz, norm_zero] at h
  exact zero_ne_one h

theorem embedding_unit_norm (u : Oˣ) : ‖eisEmbedding (u : O)‖ = 1 := by
  have h := eisEmbedding_norm_sq_eq_absNorm_span (u : O)
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (u : O))]

omit [NeZero c] in

theorem theta_mul_global_unit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (u : Oˣ) :
    theta c χ t = χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) * theta c χ t := by
  have h := u.mulLeft.tsum_eq (fun z : O =>
    χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (eisEmbedding z))
  calc
    theta c χ t = ∑' z : O,
        χ (Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * z)) *
          gaussian (parameter c t) (eisEmbedding ((u : O) * z)) := h.symm
    _ = χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) * theta c χ t := by
      rw [theta, ← tsum_mul_left]
      apply tsum_congr
      intro z
      simp only [map_mul, gaussian, norm_mul, embedding_unit_norm, one_mul, mul_assoc]

omit [NeZero c] in

theorem theta_eq_zero_of_global_unit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ)
    (u : Oˣ) (hu : χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) ≠ 1) :
    theta c χ t = 0 :=
  eq_zero_of_mul_eq_self_left hu (theta_mul_global_unit c χ t u).symm

omit [NeZero c] in
theorem global_unit_invariant_of_theta_ne_zero
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : theta c χ t ≠ 0) :
    ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1 := by
  intro u
  by_contra hu
  exact ht (theta_eq_zero_of_global_unit c χ t u hu)

end SevenEighths.GaussianTheta

end

end OAI

end

