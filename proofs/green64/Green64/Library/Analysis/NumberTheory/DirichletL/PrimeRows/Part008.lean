module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part009
public import Green64.Library.OAI.NumberTheory.DirichletL.PrimeRows.CentralRowCost
public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeRows.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part014
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part013
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part012

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / PrimeRows / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CentralSlotSum -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem central_regular_slot_sum (eps c d B : ℝ) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
      (hT : ∀P∈T,Supported P.val ∧ (480:ℝ)≤P.val.absNorm ∧ IsCoprime P.val η.modulus)
      (Y : ℝ),1≤Y → ∀(W : ℝ→ℂ),Function.support W⊆Set.Icc c d →
      (∀y,‖W y‖≤B) → ∀(a e : ℝ) (x w z : ℂ),
      (51/100:ℝ)≤a → a≤1 → 0<e → e≤1/1000 →
      x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 →
      (∀P∈T,198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
      (∑P:T,‖W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralRegularError η u P.val (hT P.val P.property).1 x w z‖)≤
      C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*Y^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed
    eps c d (-(4/25:ℝ)) 1 B 1440 heps hc hd (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro η u T hT Y hY W hWS hWB a e x w z ha ha1 he he1 hx hw hz hsmall
  let f : T→Ideal O := fun P=>P.val.val
  have hf : Function.Injective f := fun P Q h=>Subtype.ext (Subtype.ext h)
  let E : T→ℂ := fun P=>centralRegularError η u P.val (hT P.val P.property).1 x w z
  let G : T→ℂ := fun P=>((f P).absNorm:ℂ)^(1/2:ℂ)*E P
  have hnorm (P : T) : ‖G P‖≤1440*(if f P∣Ideal.span {u.val} then ((f P).absNorm:ℝ)^(1:ℝ) else 1) := by
    have hQ : (480:ℝ)≤(f P).absNorm := (hT P.val P.property).2.1
    have hQ0 : (0:ℝ)<(f P).absNorm := by linarith
    have hQ1 : (1:ℝ)≤(f P).absNorm := by linarith
    have hb := (central_actual_local_bounds η u P.val (hT P.val P.property).1
      (hT P.val P.property).2.2 a e x w z hQ (hsmall P.val P.property) ha ha1 he he1 hx hw hz).2.1
    have hn : ‖((f P).absNorm:ℂ)^(1/2:ℂ)‖=((f P).absNorm:ℝ)^(1/2:ℝ) := by
      rw [show ((f P).absNorm:ℂ)=(((f P).absNorm:ℝ):ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hQ0];norm_num
    dsimp only [G]
    rw [norm_mul,hn]
    calc
      _ ≤ ((f P).absNorm:ℝ)^(1/2:ℝ)*(1440*(if f P∣Ideal.span {u.val} then
          ((f P).absNorm:ℝ)^(1/2:ℝ) else ((f P).absNorm:ℝ)^(-(51/100:ℝ)))) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hQ0.le _)
      _ ≤ _ := by
        by_cases hp : f P∣Ideal.span {u.val}
        · simp only [ite_eq_left hp]
          rw [mul_left_comm,←Real.rpow_add hQ0]
          norm_num
        · simp only [ite_eq_right hp,mul_one]
          rw [mul_left_comm,←Real.rpow_add hQ0]
          have hh : ((f P).absNorm:ℝ)^((1/2:ℝ)-(51/100:ℝ))≤1 := by
            exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : (1/2:ℝ)-51/100≤0)).trans_eq (Real.rpow_zero _)
          norm_num only [show (1/2:ℝ)+-(51/100:ℝ)=(1/2:ℝ)-(51/100:ℝ) by ring]
          nlinarith
  have hb := hbound f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _=>P.val.property.ne_zero) W hWS hWB G (fun P _=>hnorm P)
    (z-1/2) (by simp only [Complex.sub_re];rw [hz];norm_num)
  have heq (P : T) :
      W (((f P).absNorm:ℝ)/Y)*((f P).absNorm:ℂ)^((z-1/2)-1)*G P=
      W (((f P).absNorm:ℝ)/Y)*((f P).absNorm:ℂ)^(z-1)*E P := by
    have hn : ((f P).absNorm:ℂ)≠0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero
    dsimp only [G]
    rw [←mul_assoc,mul_assoc (W _) ,←Complex.cpow_add _ _ hn]
    rw [show (z - 1 / 2) - 1 + 1 / 2 = z - 1 by ring]
  simpa only [heq] using hb
end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CentralAllSlots -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralAllSlots
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ProbeCentralRepeatedProduct
open ProbeCentralRepeatedSubset ProbeCentralBranchProduct
local notation "O" => HeckeFamily.O

def phaseSlot (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal) (W : ℝ→ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  ∑P:T,W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*(-star (idealRowHom u.val P.val.val))

theorem actual_three_branch_slots (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset ProbePhysical.PrimeIdeal) (hs : ∀j P,P∈T j→Supported P.val),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀p : Fin N→ℝ,(∀j,1≤p j) → (∀j,‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j) →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ‖∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u P.val (hs j P.val P.property) x w z‖ ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by
  obtain ⟨Cr,hCr,hregular⟩ := central_regular_slot_sum eps c d B heps hc hd hB
  obtain ⟨Ct,hCt,hrepeated⟩ := actual_repeated_subset N e eps c d B he he1 heps hc hd hB
  refine ⟨Ct*(Cr+2)^N,by positivity,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi p hp hphase
  let L := ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖
  let U : ℝ := (Ideal.span {u.val}:Ideal O).absNorm
  let R := Ct*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*U^eps
  let A : Fin N→ℂ := fun j=>phaseSlot u (T j) (W j) (Y j) z
  let E : Fin N→ℂ := fun j=>∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
    centralRegularError η u P.val (hs j P.val P.property) x w z
  let F : Fin N→ℂ := fun j=>∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
    centralRepeatedTerm η u P.val (hs j P.val P.property) x w z
  let yy : Fin N→ℝ := fun j=>(Y j)^(-(4/25:ℝ))
  have hU : 1≤U := by dsimp [U];exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hUp : 1≤U^eps := Real.one_le_rpow hU heps.le
  have hR : 0≤R := by dsimp [R];exact mul_nonneg (mul_nonneg hCt.le (rowCost_nonneg _ _ _ _ _ _ _)) (Real.rpow_nonneg (zero_le_one.trans hU) _)
  have hyy (j : Fin N) : 0≤yy j := Real.rpow_nonneg (zero_le_one.trans (hY j)) _
  have hE (j : Fin N) : ‖E j‖≤yy j*(Cr*U^eps) := by
    have hb := hregular η u (T j) (fun P hP=>⟨hs j P hP,hQ j P hP,hη j P hP⟩)
      (Y j) (hY j) (W j) (hWS j) (hW j) a e x w z ha ha1 he he1.le hx hw hz (hsmall j)
    exact (norm_sum_le _ _).trans (hb.trans_eq (by dsimp [yy,U];ring))
  have hF (J : Finset (Fin N)) : L*(∏j∈J,‖F j‖)≤R*(∏j∈J,yy j) := by
    have hb := hrepeated S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall
      W Y hY hWS hW x w z hx hw hz hwi J
    have hp' : (∏j:J,‖F j.val‖)≤∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*
        (P.val.val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖ := by
      apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
      intro j _
      exact norm_sum_le _ _
    have hh := (mul_le_mul_of_nonneg_left hp' (show 0≤L from norm_nonneg _)).trans hb
    rw [Finset.prod_coe_sort J (fun j=>‖F j‖),
      Finset.prod_coe_sort J (fun j=>(Y j)^(-(4/25:ℝ)))] at hh
    exact hh
  have hb := three_branch_bound L R (Cr*U^eps) A E F yy p (norm_nonneg _) hR (by positivity) hyy hp hphase hE hF
  have heq : (∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralNormalizedSlot η u P.val (hs j P.val P.property) x w z)=∏j,(A j+E j+F j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [A,E,F,phaseSlot,centralNormalizedSlot_split,mul_add,Finset.sum_add_distrib]
  rw [heq]
  apply hb.trans
  have hcoef : (Cr*U^eps+2)^N≤(Cr+2)^N*U^(eps*N) := by
    have hh : Cr*U^eps+2≤(Cr+2)*U^eps := by nlinarith
    have hp' := pow_le_pow_left₀ (show 0≤Cr*U^eps+2 by positivity) hh N
    rw [mul_pow] at hp'
    have heq : (U^eps)^N=U^(eps*N) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hU)]
    rwa [heq] at hp'
  have hyprod : 0≤∏j,yy j := Finset.prod_nonneg (fun j _=>hyy j)
  have hpprod : 0≤∏j,p j := Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))
  calc
    _ ≤ R*((Cr+2)^N*U^(eps*N))*(∏j,yy j)*(∏j,p j) := by gcongr
    _ = _ := by
      dsimp [R,yy]
      have hh : U^eps*U^(eps*N)=U^(eps*(N+1)) := by rw [←Real.rpow_add (zero_lt_one.trans_le hU)];congr 1;ring
      calc
        _ = Ct*(Cr+2)^N*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*(U^eps*U^(eps*N))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by ring
        _ = _ := by rw [hh]
end SevenEighths.ProbeCentralAllSlots

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CentralTargetCost -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical HeckeReciprocalGrowth HeckeDeletionBounds
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

lemma presentationComplexity_norm_bound (χ : Character) (H : ℝ) :
    presentationComplexity χ H≤2*(χ.modulus.absNorm:ℝ)^2*(3+|H|)^2 := by
  have hd : radical χ.modulus∣χ.modulus := by
    unfold radical SmoothMobiusCorrection.primeProduct
    rw [SmoothMobiusCorrection.prod_primeSet χ.modulus (fun J : Ideal O=>J)]
    exact IdealMobiusDivisorSum.support_product_dvd χ.modulus_ne_bot (Finset.Subset.refl _)
  have hn : ((radical χ.modulus).absNorm:ℝ)≤χ.modulus.absNorm := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)) (map_dvd Ideal.absNorm hd)
  unfold presentationComplexity HeckeLogarithmic.complexity
  calc
    _ ≤ (χ.modulus.absNorm:ℝ)*(2*χ.modulus.absNorm*(3+|H|)^2) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by ring

lemma target_complexity_norm_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (H : ℝ) (hH : 0≤H) :
    presentationComplexity ((targetRow η u).excludePrimes S hS) H≤
      2*((fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u)^2*(3+H)^2 := by
  have hn : (((targetRow η u).excludePrimes S hS).modulus.absNorm:ℝ)≤
      (fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u := by
    unfold rowNorm
    exact_mod_cast (by simpa only [fixedConductorConstant,mul_assoc,mul_comm,mul_left_comm] using
      targetRow_excluded_conductor S hS η u)
  apply (presentationComplexity_norm_bound _ H).trans
  rw [abs_of_nonneg hH]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by positivity) (by unfold rowNorm;positivity)).mpr hn) (by norm_num)

lemma target_complexity_power_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (H eps : ℝ) (hH : 0≤H) (heps : 0≤eps) :
    (presentationComplexity ((targetRow η u).excludePrimes S hS) H)^eps≤
      (2*(fixedConductorConstant S:ℝ)^2)^eps*(η.modulus.absNorm:ℝ)^(2*eps)*
        rowNorm u^(2*eps)*(3+H)^(2*eps) := by
  have hb := Real.rpow_le_rpow (show 0≤presentationComplexity ((targetRow η u).excludePrimes S hS) H by
    unfold presentationComplexity HeckeLogarithmic.complexity;positivity)
    (target_complexity_norm_bound S hS η u H hH) heps
  apply hb.trans_eq
  rw [show 2*((fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u)^2*(3+H)^2=
    (2*(fixedConductorConstant S:ℝ)^2)*(η.modulus.absNorm:ℝ)^2*rowNorm u^2*(3+H)^2 by ring]
  rw [Real.mul_rpow (by unfold rowNorm;positivity) (by positivity),
    Real.mul_rpow (by positivity) (by unfold rowNorm;positivity),Real.mul_rpow (by positivity) (by positivity)]
  rw [←Real.rpow_two (η.modulus.absNorm:ℝ),←Real.rpow_two (rowNorm u),←Real.rpow_two (3+H),
    ←Real.rpow_mul (by positivity : (0:ℝ)≤η.modulus.absNorm),
    ←Real.rpow_mul (rowNorm_ge_one u |>.trans' (by norm_num : (0:ℝ)≤1)),
    ←Real.rpow_mul (by linarith : 0≤3+H)]

theorem centralRemainingScalar_arithmetic_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(3*eps)*(3+H)^(2*eps) := by
  obtain ⟨C,hC,hbound⟩ := centralRemainingScalar_bound e eps he he' heps
  have hF : 0<(fixedConductorConstant S:ℝ) := by exact_mod_cast fixedConductorConstant_pos S hS.prime
  refine ⟨C*(2*(fixedConductorConstant S:ℝ)^2)^eps,by positivity,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hh : 0≤H := (abs_nonneg _).trans hxi
  have hb := hbound S hS hfirst η u ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  apply hb.trans
  have hc := target_complexity_power_bound S hS.prime η u H eps hh heps.le
  have hn : 0< rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  calc
    _ ≤ C*rowNorm u^eps*((2*(fixedConductorConstant S:ℝ)^2)^eps*(η.modulus.absNorm:ℝ)^(2*eps)*
        rowNorm u^(2*eps)*(3+H)^(2*eps)) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by
      rw [show 3*eps=eps+2*eps by ring,Real.rpow_add hn]
      ring

theorem central_remaining_rowCost_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps H≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*(3+H)^(2+4*eps) := by
  obtain ⟨C0,hC0,h0⟩ := centralRemainingScalar_arithmetic_bound e eps he he' heps S hS hfirst
  obtain ⟨C1,hC1,h1⟩ := central_rowCost_bound S hS.prime e eps he heps
  refine ⟨C0*C1,mul_pos hC0 hC1,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hh : 0≤H := (abs_nonneg _).trans hxi
  have hn : 0< rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hL : 0<3+H := by linarith
  have h0' := h0 η u ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have h1' := h1 u a H ha ha1 hh
  apply (mul_le_mul h0' h1' (ProbeCentralRepeatedProduct.rowCost_nonneg S hS.prime u a e eps H)
    (by positivity)).trans_eq
  have hnp : rowNorm u^(3*eps)*rowNorm u^(a-1/2+12*e+4*eps)=
      rowNorm u^(a-1/2+12*e+7*eps) := by rw [←Real.rpow_add hn];congr 1;ring
  have hlp : (3+H)^(2*eps)*(3+H)^(2+2*eps)=(3+H)^(2+4*eps) := by
    rw [←Real.rpow_add hL];congr 1;ring
  calc
    _ = C0*C1*(η.modulus.absNorm:ℝ)^(2*eps)*
        (rowNorm u^(3*eps)*rowNorm u^(a-1/2+12*e+4*eps))*
        ((3+H)^(2*eps)*(3+H)^(2+2*eps)) := by ring
    _ = _ := by rw [hnp,hlp]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CentralPrimeSum -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralPrimeSum
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralAllSlots
local notation "O" => HeckeFamily.O

theorem actual_central_prime_sum (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset ProbePhysical.PrimeIdeal) (hPS : ∀j P,P∈T j→P.val∉S),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 →
      |x.im|≤(3*i+2:ℕ)*T0 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀p : Fin N→ℝ,(∀j,1≤p j) → (∀j,‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j) →
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
        (fun j=>hPS j (P j).val (P j).property) W Y x w z‖ ≤
      C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*
        (3+(3*i+2:ℕ)*T0)^(2+4*eps)*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by
  obtain ⟨Ca,hCa,hall⟩ := actual_three_branch_slots N e eps c d B he he1 heps hc hd hB
  obtain ⟨Cb,hCb,hcost⟩ := central_remaining_rowCost_bound e eps he he1 heps S hS hfirst
  refine ⟨Ca*Cb,mul_pos hCa hCb,?_⟩
  intro u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hPS hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hxi hwi p hp hphase
  let hs : ∀j P,P∈T j→Supported P.val := fun j P hP=>outside_prime_supported S hS.bad P (hPS j P hP)
  have hinj (P : ∀j,T j) : Function.Injective (fun j=>(P j).val) := by
    intro j l hh
    change (P j).val=(P l).val at hh
    by_contra hne
    exact Finset.disjoint_left.mp (hdis j l hne) (P j).property (by rw [hh];exact (P l).property)
  have ha' := hall S hS.prime hmax hS.bad u hu η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall
    W Y hY hWS hW x w z hx hw hz hwi p hp hphase
  have hc' := hcost η u twists T0 a ((3*i+2:ℕ)*T0) i hT0 ha ha1 le_rfl hbin x w z hx hw hz hxi
  have hN : 0< rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hy : 0≤∏j,(Y j)^(-(4/25:ℝ)) := Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (zero_le_one.trans (hY j)) _)
  have hpp : 0≤∏j,p j := Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))
  rw [calibrated_prime_slots_separate S hS hmax η u T hPS hinj W Y a e x w z
    hfirst ha ha1 he he1.le hx hw hz hQ hη hsmall,centralRowScalar_split,norm_mul,norm_mul]
  have hn := mul_le_mul_of_nonneg_left ha' (norm_nonneg (centralRemainingScalar S hS η u x w z))
  have hc'' := mul_le_mul_of_nonneg_right hc'
    (show 0≤Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) by positivity)
  have hpow : rowNorm u^(a-1/2+12*e+7*eps)*rowNorm u^(eps*(N+1))=
      rowNorm u^(a-1/2+12*e+eps*(N+8)) := by
    rw [←Real.rpow_add hN]
    congr 1
    ring
  calc
    _ = ‖centralRemainingScalar S hS η u x w z‖*
      (‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w‖*
        ‖∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*centralNormalizedSlot η u P.val (hs j P.val P.property) x w z‖) := by ring
    _ ≤ ‖centralRemainingScalar S hS η u x w z‖*
      (Ca*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*T0)*
        rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := hn
    _ = (‖centralRemainingScalar S hS η u x w z‖*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*T0))*
      (Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by ring
    _ ≤ (Cb*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*(3+(3*i+2:ℕ)*T0)^(2+4*eps))*
      (Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := hc''
    _ = _ := by
      calc
        _ = Ca*Cb*(η.modulus.absNorm:ℝ)^(2*eps)*(rowNorm u^(a-1/2+12*e+7*eps)*rowNorm u^(eps*(N+1)))*
          (3+(3*i+2:ℕ)*T0)^(2+4*eps)*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by ring
        _ = _ := by rw [hpow]
end SevenEighths.ProbeCentralPrimeSum

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CubeCalibration -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma centralCubeIntegral_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=0 := by
  simp [centralCubeIntegral,continuedRowOnLines,continuedPhysicalRowKernel,hc]

lemma cubeWeightedRow_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z a e H : ℝ) :
    cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H=0 := by
  funext t
  simp [cubeWeightedRow,weightedRowOnLines,calibratedTupleValue,hc]

theorem finiteCentralCubeRows_filter_calibration {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e : ℝ) (a H : FreeRow→ℝ) :
    finiteCentralCubeRows S hS hmax η (R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0))
      T hT W Yp W0 W1 X Y Z e a H=
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H := by
  unfold finiteCentralCubeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp [hc,centralCubeIntegral_calibration_zero S hS hmax _ _ η u hc]
  · simp [hc]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CentralSupportedSplit -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def supportedFloorRows (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) : Finset FreeRow :=
  R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0 ∧ grid u=0)

def supportedNonfloorRows (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) : Finset FreeRow :=
  R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0 ∧ grid u≠0)

@[simp] lemma mem_supportedFloorRows (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) (u : FreeRow) :
    u∈supportedFloorRows S hmax R grid ↔ u∈R ∧ (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ grid u=0 :=
  Finset.mem_filter

@[simp] lemma mem_supportedNonfloorRows (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) (u : FreeRow) :
    u∈supportedNonfloorRows S hmax R grid ↔ u∈R ∧ (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ grid u≠0 :=
  Finset.mem_filter

lemma nonfloor_grid_positive (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) (u : FreeRow)
    (hu : u∈supportedNonfloorRows S hmax R grid) (e : ℝ) (he : 0<e) :
    51/100<(51/100:ℝ)+e*grid u := by
  have hg : 0<(grid u:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ((mem_supportedNonfloorRows S hmax R grid u).mp hu).2.2
  linarith [mul_pos he hg]

theorem finiteCentralCubeRows_supported_split {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀j P,P∈T j→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e : ℝ) (grid : FreeRow→ℕ) (H : FreeRow→ℝ) :
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H=
      finiteCentralCubeRows S hS hmax η (supportedFloorRows S hmax R grid) T hT W Yp W0 W1 X Y Z e (fun _=>51/100) H+
      finiteCentralCubeRows S hS hmax η (supportedNonfloorRows S hmax R grid) T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H := by
  have hfilter := finiteCentralCubeRows_filter_calibration S hS hmax η R T hT W Yp W0 W1 X Y Z e
    (fun u=>51/100+e*grid u) H
  refine hfilter.symm.trans ?_
  let Rs := R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0)
  have hfloor : Rs.filter (fun u=>grid u=0)=supportedFloorRows S hmax R grid := by
    simp only [Rs, Finset.filter_filter, supportedFloorRows]
  have hn : Rs.filter (fun u=>¬grid u=0)=supportedNonfloorRows S hmax R grid := by
    simp only [Rs, Finset.filter_filter, supportedNonfloorRows]
  have hsplit : finiteCentralCubeRows S hS hmax η Rs T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H=
      finiteCentralCubeRows S hS hmax η (supportedFloorRows S hmax R grid) T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H+
      finiteCentralCubeRows S hS hmax η (supportedNonfloorRows S hmax R grid) T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H := by
    unfold finiteCentralCubeRows
    rw [←hfloor,←hn]
    exact (Finset.sum_filter_add_sum_filter_not Rs (fun u=>grid u=0) _).symm
  refine hsplit.trans ?_
  refine congrArg₂ (fun x y : ℂ => x + y) ?_ rfl
  unfold finiteCentralCubeRows
  apply Finset.sum_congr rfl
  intro u hu
  have hg := ((mem_supportedFloorRows S hmax R grid u).mp hu).2.2
  simp only [hg,Nat.cast_zero,mul_zero,add_zero]

lemma normalized_nonfloor_error (A F Cfloor Cnon N : ℂ) (E B : ℝ)
    (hE : ‖A/N-F-(Cfloor+Cnon)/N‖≤E) (hB : ‖Cfloor/N‖≤B) :
    ‖A/N-F-Cnon/N‖≤E+B := by
  calc
    _ = ‖(A/N-F-(Cfloor+Cnon)/N)+Cfloor/N‖ := by congr 1;ring
    _ ≤ ‖A/N-F-(Cfloor+Cnon)/N‖+‖Cfloor/N‖ := norm_add_le _ _
    _ ≤ E+B := add_le_add hE hB

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CubeBinPartition -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (i k : ℕ) : Finset FreeRow :=
  R.filter (fun u=>idx u=i ∧ grid u=k)

@[simp] lemma mem_cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (i k : ℕ) (u : FreeRow) :
    u∈cubeBinRows R idx grid i k ↔ u∈R ∧ idx u=i ∧ grid u=k := by simp [cubeBinRows]

lemma sum_cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u≤n ∧ grid u≤ m) (f : FreeRow→ℂ) :
    (∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),∑u∈cubeBinRows R idx grid i k,f u)=∑u∈R,f u := by
  have hm : ∀u∈R,(idx u,grid u)∈(Finset.range (n+1)).product (Finset.range (m+1)) := by
    intro u hu
    simpa only [Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] using
      And.intro (Nat.lt_succ_of_le (hlabel u hu).1) (Nat.lt_succ_of_le (hlabel u hu).2)
  have hs := Finset.sum_fiberwise_of_maps_to hm f
  simpa only [Finset.product_eq_sprod,Finset.sum_product,Prod.mk.injEq,cubeBinRows] using hs

theorem finiteCentralCubeRows_bin_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B : ℝ) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u≤n ∧ grid u≤ m) :
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*B)=
    ∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),
      finiteCentralCubeRows S hS hmax η (cubeBinRows R idx grid i k) T hT W Yp W0 W1 X Y Z e
        (fun _=>51/100+e*k) (fun _=>(3*i+1:ℕ)*B) := by
  unfold finiteCentralCubeRows
  rw [←sum_cubeBinRows R idx grid n m hlabel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro u hu
  rcases (mem_cubeBinRows R idx grid i k u).mp hu with ⟨hu,hi,hk⟩
  simp only [hi,hk]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CubeCommonProfile -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def cubeArithmeticSum {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (a e : ℝ) (t : HeightSpace) : ℂ :=
  ∑u∈R,frequencyWeight ((17/50:ℂ)+t.1.2*Complex.I) ⟨u.val,u.property.1⟩*
    ∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hT i _ (P i).property) W Yp
      (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      ((17/50:ℂ)+t.1.2*Complex.I)

theorem cube_sum_eq_common_profile {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) (t : HeightSpace) :
    (∑u∈R,∑P:(∀i,T i),cubeWeightedRow S hS hmax (fun i=>(P i).val)
      (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z a e H t)=
    {v : HeightSpace | (|v.1.1|≤H ∧ |v.2|≤H) ∧ |v.1.2|≤H}.indicator
      (fun v=>sourceMellinWeight W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+v.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+v.2*Complex.I)
        ((17/50:ℂ)+v.1.2*Complex.I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e v) t := by
  by_cases ht : (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H
  · simp [cubeWeightedRow,ht,weightedRowOnLines,cubeArithmeticSum,
      Finset.mul_sum,mul_assoc]
  · simp [cubeWeightedRow,ht]

theorem cube_common_profile_integral {K : ℕ} {ι : Type*} [Fintype ι]
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1' : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}.indicator
      (fun t=>sourceMellinWeight W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
        ((17/50:ℂ)+t.1.2*Complex.I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
    Integrable F heightMeasure ∧
      finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure) := by
  have hh := finiteCentralCubeRows_eq_integral e he he' S hS hmax hfirst η R hR T hT
    (fun _=>a) (fun _=>B) (fun _=>H) (fun _=>i) ψ
    (fun u hu=>⟨ha,ha1,hB,hH,hbin u hu⟩) W Yp W0 W1 a0 b0 a1 b1 ha0 ha1' hW0 hW1 X Y Z hX hY hZ
  dsimp only at hh ⊢
  simpa only [cube_sum_eq_common_profile] using hh

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma cubeArithmeticSum_norm {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (a e : ℝ) (t : HeightSpace)
    (A : FreeRow→ℝ)
    (hA : ∀u∈R,‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
      (fun j=>hT j _ (P j).property) W Yp
      (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      ((17/50:ℂ)+t.1.2*Complex.I)‖≤A u) :
    ‖cubeArithmeticSum S hS hmax η R T hT W Yp a e t‖≤
      ∑u∈R,rowNorm u^(-(17/50:ℝ))*A u := by
  unfold cubeArithmeticSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu=>?_)
  rw [norm_mul,frequencyWeight_ideal_norm]
  have hz : (((17/50:ℂ)+t.1.2*Complex.I).re:ℝ)=17/50 := by simp
  rw [hz]
  exact mul_le_mul_of_nonneg_left (hA u hu) (Real.rpow_nonneg (by positivity) _)

theorem actual_common_cube_norm (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι]
      (e a B H : ℝ) (i : ℕ),0<e → e<1/1000 → 51/100≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
    ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
    FirstTail (4*e) S → ∀(η : Character) (R : Finset FreeRow), (∀u∈R,u.val≠1) →
    ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
      (ψ : FreeRow→ι→Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e) →
    ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (X Y Z : ℝ),0<X → 0<Y → 0<Z →
    ∀A : FreeRow→ℝ,(∀u∈R,0≤A u) →
      (∀t : HeightSpace,(|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H → ∀u∈R,
        ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>hT j _ (P j).property) W Yp
          (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
          ((17/50:ℂ)+t.1.2*Complex.I)‖≤A u) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)‖≤
        C*(X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e))*
          (∑u∈R,rowNorm u^(-(17/50:ℝ))*A u) := by
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    0 2 (17/50) (17/50) (-1) 1 (by norm_num) 0
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)^3‖*D,mul_pos (norm_pos_iff.mpr (by
    apply pow_ne_zero
    exact_mod_cast (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))) hD,?_⟩
  intro K ι _ e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp X Y Z hX hY hZ A hA hb
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  let V : HeightSpace→ℂ := fun t=>sourceMellinWeight W0 W1 X Y Z
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
    ((17/50:ℂ)+t.1.2*Complex.I)
  let F := E.indicator (fun t=>V t*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
  let mass : ℝ := ∑u∈R,rowNorm u^(-(17/50:ℝ))*A u
  have hm : 0≤ mass := Finset.sum_nonneg fun u hu=>mul_nonneg (Real.rpow_nonneg (by unfold rowNorm;positivity) _) (hA u hu)
  let scale : ℝ := X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e)
  have hs : 0≤ scale := by dsimp [scale];positivity
  have hv (t : HeightSpace) : ‖V t‖=scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ := by
    have hxre : (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I).re=a+16*e := by simp
    have hwre : (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I).re=1-a-6*e := by simp
    have hzre : ((17/50:ℂ)+t.1.2*Complex.I).re=17/50 := by simp
    dsimp [V]
    rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ,hxre,hwre,hzre]
    have hs0 : X^(1/2-(17/50:ℝ))*Z^((a+16*e)+17/50-1)*Y^((1-a-6*e)-1)=scale := by
      rw [show (1/2-17/50:ℝ)=4/25 by norm_num,
        show (a+16*e)+17/50-1=a+16*e-33/50 by ring,
        show (1-a-6*e)-1=-a-6*e by ring]
    rw [hs0]
    simp [onLines]
  have hp := hprofile (a+16*e) (by constructor <;> linarith) (17/50) ⟨le_rfl,le_rfl⟩
    (1-a-6*e) (by constructor <;> linarith)
  simp only [pow_zero,one_mul] at hp
  have hg : Integrable (fun t=>scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass) heightMeasure :=
    (hp.1.const_mul scale).mul_const mass
  have hf := cube_common_profile_integral e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR
    T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  change Integrable F heightMeasure ∧ _ at hf
  have hb' (t : HeightSpace) : ‖F t‖≤ scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass := by
    by_cases ht : t∈E
    · dsimp only [F]
      rw [Set.indicator_of_mem ht,norm_mul,hv]
      exact mul_le_mul_of_nonneg_left (cubeArithmeticSum_norm S hS hmax η R T hT W Yp a e t A (hb t ht)) (by positivity)
    · dsimp only [F]
      rw [Set.indicator_of_notMem ht,norm_zero]
      positivity
  rw [hf.2,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(∫t,scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (integral_mono hf.1.norm hg hb')) (norm_nonneg _)
    _ = ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*(∫t,‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ ∂heightMeasure)*mass) := by
      rw [integral_mul_const,integral_const_mul]
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*D*mass) := by gcongr;exact hp.2
    _ = _ := by dsimp [scale,mass];ring

theorem actual_common_cube_aggregate_norm (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι]
      (e a B H : ℝ) (i : ℕ),0<e → e<1/1000 → 51/100≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
    ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
    FirstTail (4*e) S → ∀(η : Character) (R : Finset FreeRow), (∀u∈R,u.val≠1) →
    ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
      (ψ : FreeRow→ι→Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e) →
    ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (X Y Z : ℝ),0<X → 0<Y → 0<Z →
    ∀A : ℝ,0≤A →
      (∀t : HeightSpace,(|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H →
        ‖cubeArithmeticSum S hS hmax η R T hT W Yp a e t‖≤A) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)‖≤
        C*(X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e))*
          A := by
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    0 2 (17/50) (17/50) (-1) 1 (by norm_num) 0
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)^3‖*D,mul_pos (norm_pos_iff.mpr (by
    apply pow_ne_zero
    exact_mod_cast (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))) hD,?_⟩
  intro K ι _ e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp X Y Z hX hY hZ A hA hb
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  let V : HeightSpace→ℂ := fun t=>sourceMellinWeight W0 W1 X Y Z
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
    ((17/50:ℂ)+t.1.2*Complex.I)
  let F := E.indicator (fun t=>V t*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
  let mass : ℝ := A
  have hm : 0≤ mass := hA
  let scale : ℝ := X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e)
  have hs : 0≤ scale := by dsimp [scale];positivity
  have hv (t : HeightSpace) : ‖V t‖=scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ := by
    have hxre : (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I).re=a+16*e := by simp
    have hwre : (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I).re=1-a-6*e := by simp
    have hzre : ((17/50:ℂ)+t.1.2*Complex.I).re=17/50 := by simp
    dsimp [V]
    rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ,hxre,hwre,hzre]
    have hs0 : X^(1/2-(17/50:ℝ))*Z^((a+16*e)+17/50-1)*Y^((1-a-6*e)-1)=scale := by
      rw [show (1/2-17/50:ℝ)=4/25 by norm_num,
        show (a+16*e)+17/50-1=a+16*e-33/50 by ring,
        show (1-a-6*e)-1=-a-6*e by ring]
    rw [hs0]
    simp [onLines]
  have hp := hprofile (a+16*e) (by constructor <;> linarith) (17/50) ⟨le_rfl,le_rfl⟩
    (1-a-6*e) (by constructor <;> linarith)
  simp only [pow_zero,one_mul] at hp
  have hg : Integrable (fun t=>scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass) heightMeasure :=
    (hp.1.const_mul scale).mul_const mass
  have hf := cube_common_profile_integral e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR
    T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  change Integrable F heightMeasure ∧ _ at hf
  have hb' (t : HeightSpace) : ‖F t‖≤ scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass := by
    by_cases ht : t∈E
    · dsimp only [F]
      rw [Set.indicator_of_mem ht,norm_mul,hv]
      exact mul_le_mul_of_nonneg_left (hb t ht) (by positivity)
    · dsimp only [F]
      rw [Set.indicator_of_notMem ht,norm_zero]
      positivity
  rw [hf.2,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(∫t,scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (integral_mono hf.1.norm hg hb')) (norm_nonneg _)
    _ = ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*(∫t,‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ ∂heightMeasure)*mass) := by
      rw [integral_mul_const,integral_const_mul]
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*D*mass) := by gcongr;exact hp.2
    _ = _ := by dsimp [scale,mass];ring
end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CentralDyadicWeight -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma dyadic_weighted_rows_card (α r C U B : ℝ) (hC : 0≤C) (hU : 0<U)
    (R : Finset FreeRow) (hcard : (R.card:ℝ)≤B)
    (hR : ∀u∈R,U≤ rowNorm u ∧ rowNorm u≤2*U)
    (F : FreeRow→ℝ) (hF : ∀u∈R,F u≤C*rowNorm u^α)
    (z : ℂ) (hz : z.re=r) :
    (∑u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u)≤
      B*C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r) := by
  have hA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 (α-r) (by norm_num)
  calc
    _ ≤ ∑u∈R,C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r) := by
      apply Finset.sum_le_sum
      intro u hu
      have hN : 0< rowNorm u := hU.trans_le (hR u hu).1
      rw [frequencyWeight_ideal_norm,hz]
      change rowNorm u^(-r)*F u≤_
      calc
        _ ≤ rowNorm u^(-r)*(C*rowNorm u^α) :=
          mul_le_mul_of_nonneg_left (hF u hu) (Real.rpow_nonneg hN.le _)
        _ = C*rowNorm u^(α-r) := by
          rw [show α-r=(-r)+α by ring,Real.rpow_add hN]; ring
        _ ≤ _ := by
          have hb := ProbeSelectedPrimeSums.annular_rpow 1 2 U (rowNorm u) (α-r)
            (by norm_num) (by norm_num) hU (by simpa using (hR u hu).1) (hR u hu).2
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC
    _ = (R.card:ℝ)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r)) := by simp
    _ ≤ B*(C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

lemma annular_power_uniform (p pmax : ℝ) (hp : p≤pmax) :
    ProbeSelectedPrimeSums.annularPower 1 2 p≤ max 1 ((2:ℝ)^pmax) := by
  unfold ProbeSelectedPrimeSums.annularPower
  rw [Real.one_rpow]
  exact max_le_max le_rfl (Real.rpow_le_rpow_of_exponent_le (by norm_num) hp)

def mixedSourceExponent (a v d R q : ℝ) : ℝ :=
  ProbeCentralExponent.sourceExponent a v R q+(d-v)*R

lemma mixed_physical_exponent (Z a v d R q e eps loss mesh : ℝ) (N : ℕ)
    (hZ : 0<Z) :
    ((Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e))*
      ((Z^d)^R*(Z^v)^(a-1/2+12*e+eps*(N+8)-17/50)*Z^(-2/75+q/6+mesh/6+loss))=
    Z^(mixedSourceExponent a v d R q+ProbeCentralExponent.realLoss N v e eps loss mesh) := by
  rw [ProbeCentralExponent.physical_scale_identity Z a e hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  unfold mixedSourceExponent ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
  ring

lemma mixed_source_slack (a v d R q μ Rmax : ℝ)
    (hR : 0≤R) (hRmax : R≤Rmax) (hμ : 0≤μ) (hd : d-v≤μ) :
    mixedSourceExponent a v d R q≤ProbeCentralExponent.sourceExponent a v R q+μ*Rmax := by
  have h1 := mul_le_mul_of_nonneg_right hd hR
  have h2 := mul_le_mul_of_nonneg_left hRmax hμ
  unfold mixedSourceExponent
  linarith

lemma dyad_conductor_margin (Z v margin : ℝ) (hZ : 0<Z) (hmargin : 2≤Z^margin)
    (R : Finset FreeRow) (hR : ∀u∈R,rowNorm u≤2*Z^v) :
    ∀u∈R,rowNorm u≤Z^((v+2*margin)-margin) := by
  intro u hu
  calc
    rowNorm u≤2*Z^v := hR u hu
    _ ≤ Z^margin*Z^v := mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring
end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CentralMixedMargins -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeDetectorRowCount ProbeCentralExponent

lemma balanced_count_range (δ x Δ loss : ℝ) (hδ : 0≤δ) (hd : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8)
    (hl : 0≤loss) (hl' : loss≤1/32) :
    let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
    1-δ≤R ∧ R≤3/2 := by
  have ht := balanced_cutoff_bounds hδ hd hx hx'
  have hp0 := mul_nonneg (show 0≤5/6-δ by linarith) (show 0≤Endpoint.balancedCutoff δ (1/2-x)-1 by linarith)
  have hp1 := mul_le_mul_of_nonneg_left ht.2 (show 0≤5/6-δ by linarith)
  dsimp only
  unfold Endpoint.balancedRowCount
  constructor <;> nlinarith

lemma balanced_mixed_margin (δ x Δ loss ζ μ v d : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hl : 0≤loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ) :
    let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
    mixedSourceExponent ((1+δ)/2) v d R (δ*x)-(3/16+Δ)≤
      -49/440640-(51/64)*Δ+(13/16)*loss+2*ζ+(3/2)*μ := by
  dsimp only
  let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
  have hr := balanced_count_range δ x Δ loss hδ hd hx hx' hΔ hΔ' hl hl'
  have hlo : 0≤R+δ/2-17/50 := by dsimp [R]; linarith [hr.1]
  have hhi : R+δ/2-17/50≤2 := by dsimp [R]; linarith [hr.2]
  have hm := balanced_source_margin δ x R Δ loss ζ v hδ hd hx hx' le_rfl hζ hv hlo hhi
  have hs := mixed_source_slack ((1+δ)/2) v d R (δ*x) μ (3/2)
    (by dsimp [R];linarith [hr.1]) hr.2 hμ hdv
  linarith

lemma high_mixed_margin (δ q Δ loss ζ μ v d : ℝ)
    (hδ : 5/6≤δ) (hd : δ≤1) (hq : q≤δ/2)
    (hl : 0≤loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ) :
    mixedSourceExponent ((1+δ)/2) v d (1-δ+loss) q-(3/16+Δ)≤
      -1/48-δ/16-Δ+(13/16)*loss+2*ζ+μ := by
  have hlo : 0≤(1-δ+loss)+δ/2-17/50 := by linarith
  have hhi : (1-δ+loss)+δ/2-17/50≤2 := by linarith
  have hm := high_source_margin δ (1-δ+loss) q Δ loss ζ v hq le_rfl hζ hv hlo hhi
  have hs := mixed_source_slack ((1+δ)/2) v d (1-δ+loss) q μ 1
    (by linarith) (by linarith) hμ hdv
  linarith

lemma balanced_mixed_saving (δ x Δ loss ζ μ v d other saving : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hl : 0≤loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ)
    (hbudget : (13/16)*loss+2*ζ+(3/2)*μ+other+saving≤49/440640) :
    mixedSourceExponent ((1+δ)/2) v d
      (Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss) (δ*x)+other≤3/16+Δ-saving := by
  have hm := balanced_mixed_margin δ x Δ loss ζ μ v d hδ hd hx hx' hΔ hΔ' hl hl' hζ hv hμ hdv
  linarith
end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison
open PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem actual_ray_normalizer_inverse {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0<c) (hcb : c≤b)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hellsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c b) (hp : ∀j y,0≤W j y) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧ ‖normer⁻¹‖≤C*Z^nu := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let cs := sourceResidueConstant W0 W1 (∏P∈S,P)
  refine ⟨‖cs⁻¹‖+1,by positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply Set.Subset.trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_ray_mass_and_normalizer M H hH S W c b hc hcb hsupp hW hcompact hpos hp hne ell hell nu hnu,
    eventually_gt_atTop (0:ℝ)] with Z hmass hZ
  dsimp only
  refine ⟨ProbePrincipalNormalizer.signed_source_normalizer_ne_zero (∏P∈S,P)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 Finset.univ
    (fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
    (residueWeights W (fun j=>Z^(ell j))) Z (1/6) hZ (fun j _=>hmass.1 j),?_⟩
  have hb : ‖(sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (1/6)
        (slotMass (fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
          (residueWeights W (fun j=>Z^(ell j)))) : ℂ))⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,Complex.norm_real]
    simpa only [hellsum,Real.norm_eq_abs,mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _))

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowNormalized -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open Filter
namespace SevenEighths.ProbePhysical
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem original_normalized_compensatedPhysicalProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer‖≤
        C*Z^(3/16+loss) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin K) : Function.support (WC j)⊆Set.Icc a b := by
    intro y hy
    apply Set.Ioo_subset_Icc_self (hsupp j _)
    intro hz
    exact hy (by dsimp [WC];rw [hz];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hW1' : Function.support W1⊆Set.Icc a1 (max b1 (a1+1)) := by
    intro y hy
    exact ⟨(hW1 hy).1,(hW1 hy).2.trans (le_max_left _ _)⟩
  have hab1 : a1< max b1 (a1+1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨Cn,hCn,hnorm⟩ := ProbeHighRowFamily.actual_ray_normalizer_inverse M H hH S hS a b ha hab
    ell hell hsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 (loss/2) (by positivity)
  intro η
  obtain ⟨Cp,hCp,hprobe⟩ := original_ray_compensatedPhysicalProbe_low_loss S hS hmax ell
    (fun j=>(hell j).le) hinj hsum.le (RayQuotient.identityClass M H) a b B (loss/2)
    ha hab (by positivity) WC hWC hWCB W0 W1 a0 b0 a1 (max b1 (a1+1))
    (SchwartzMap.seminorm ℝ 0 0 W0) (SchwartzMap.seminorm ℝ 0 0 W1)
    ha0 ha1 hab1 (by positivity) (by positivity) hW0 hW1' (W0.smooth (⊤ : ℕ∞)) (W1.smooth (⊤ : ℕ∞))
    (SchwartzMap.norm_le_seminorm ℝ W0) (SchwartzMap.norm_le_seminorm ℝ W1) η
  refine ⟨Cp*Cn,by positivity,?_⟩
  filter_upwards [hprobe,hnorm,eventually_gt_atTop (0:ℝ)] with Z hp hn hZ
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  calc
    _≤(Cp*Z^(3/16+loss/2))*(Cn*Z^(loss/2)) :=
      mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    _=(Cp*Cn)*Z^(3/16+loss) := by
      rw [mul_mul_mul_comm,←Real.rpow_add hZ]
      congr 2
      ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

def normalizedProbe {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j=>Z^(ell j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=>canonicalSlotSupport (T j)) (fun j y=>(W j y:ℂ)) Yp
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ))

lemma isBigO_rpow_of_eventual_norm_bound (f : ℝ→ℂ) (r : ℝ)
    (h : ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,‖f Z‖≤C*Z^r) :
    f=O[atTop](fun Z : ℝ=>Z^r) := by
  obtain ⟨C,hC,hb⟩ := h
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with Z hb hZ
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hZ r)] using hb

theorem normalizedProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,normalizedProbe M H S hmax ell a b W W0 W1 η=O[atTop](fun Z : ℝ=>Z^(3/16+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := original_normalized_compensatedPhysicalProbe_low M H hH S hS hmax
    a b B loss ha hab hloss ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  apply isBigO_rpow_of_eventual_norm_bound
  exact ⟨C,hC,hb.mono (fun Z h=>h.2)⟩

theorem actual_source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) :
    (∀I,idealCoeff (η.excludePrimes S hS.prime) I=
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ|7/8<s.re} ∧
    (∀s : ℂ,7/8<s.re→‖sourceCorrection η S s-1‖≤1/2) := by
  exact ⟨excludePrimes_mask η S hS.prime,
    (sourceCorrection_differentiable η S hS).analyticOnNhd (Complex.isOpen_re_gt _),
    sourceCorrection_bound η S hS⟩

end SevenEighths.ProbeFinalAssembly
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CubePrimeThresholds -/

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbeRaySlots
local notation "O" => HeckeFamily.O

theorem central_pool_good_eventually (η : Character) (e c b dmin rmin : ℝ)
    (he : 0<e) (hc : 0<c) (hcb : c≤b) (hd : 0<dmin) (hr : 0< rmin) :
    ∀ᶠ Z : ℝ in atTop,∀(C : Set (Ideal O)) (S : Finset (Ideal O)) (d r : ℝ),dmin≤d → rmin≤ r →
      ∀P∈pool C S c b ((Z^d)^r),P.val∉S ∧ IsCoprime P.val η.modulus ∧
        (480:ℝ)≤P.val.absNorm ∧ 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2 := by
  obtain ⟨Q0,hQ0,hsmall⟩ := ProbeEuler.central_correction_threshold e he
  have ht := (tendsto_rpow_atTop (mul_pos hd hr)).const_mul_atTop hc
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop Q0),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ))] with Z hZ hQ hη
  intro C S d r hdd hrr P hP
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _
  have hle : c*Z^(dmin*rmin)≤ c*(Z^d)^r := by
    rw [←Real.rpow_mul hZp.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ
      (mul_le_mul hdd hrr hr.le (hd.trans_le hdd).le)) hc.le
  have hl := (pool_norm_bounds C S hc.le hcb hD P hP).1
  have hq : Q0≤(P.val.absNorm:ℝ) := hQ.trans (hle.trans (by linarith))
  exact ⟨(mem_pool C S c b _ P).mp hP |>.2.2.2,
    prime_coprime_of_norm_gt η P (hη.trans_le (hle.trans (by linarith))),hQ0.trans hq,hsmall _ hq⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CubeScale -/

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem cube_height_budget_eventually (n : ℕ) (τ dmin cost : ℝ)
    (hτ : 0<τ) (hc : 0≤ cost) (hgap : 2*τ<dmin*cost) :
    ∀ᶠ Z : ℝ in atTop,∀i : ℕ,i≤n → ∀d : ℝ,dmin≤d →
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^cost := by
  have habs := HeckeDyadic.constant_absorbed_eventually
    ((3*(n:ℝ)+5)^2) (dmin*cost-2*τ) (by linarith)
  filter_upwards [habs,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro i hi d hd
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpow : 1≤Z^τ := Real.one_le_rpow hZ hτ.le
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  have hx : 3+(3*i+2:ℕ)*Z^τ≤(3*(n:ℝ)+5)*Z^τ := by
    push_cast
    nlinarith
  calc
    _ ≤ ((3*(n:ℝ)+5)*Z^τ)^2 := by
      apply sq_le_sq₀ (by positivity) (by positivity) |>.mpr hx
    _ = (3*(n:ℝ)+5)^2*Z^(2*τ) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_two,←Real.rpow_mul hZp.le]
      congr 1
      ring
    _ ≤ Z^(dmin*cost-2*τ)*Z^(2*τ) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(dmin*cost) := by rw [←Real.rpow_add hZp];congr 1;ring
    _ ≤ (Z^d)^cost := by
      rw [←Real.rpow_mul hZp.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd hc)

theorem ray_cube_conductor_eventually (M : Ideal O) (ν : ℝ) (hν : 0<ν) :
    ∀ᶠ Z : ℝ in atTop,∀(u : FreeRow) (d : ℝ),rowNorm u≤Z^(d-ν) →
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^d := by
  have hh := HeckeDyadic.constant_absorbed_eventually
    ((conductorConstant*M.absNorm:ℕ):ℝ) ν hν
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hC hZ
  intro u d hu
  calc
    _ = ((conductorConstant*M.absNorm:ℕ):ℝ)*rowNorm u := by simp [rowNorm]
    _ ≤ Z^ν*Z^(d-ν) := mul_le_mul hC hu (by unfold rowNorm;positivity) (Real.rpow_nonneg hZ.le _)
    _ = Z^d := by rw [←Real.rpow_add hZ];congr 1;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CentralHeightCost -/

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem cube_height_power_eventually (n : ℕ) (τ p loss : ℝ)
    (hτ : 0<τ) (hp : 0≤p) (hgap : τ*p<loss) :
    ∀ᶠ Z : ℝ in atTop,∀i : ℕ,i≤n → (3+(3*i+2:ℕ)*Z^τ)^p≤Z^loss := by
  have hh := HeckeDyadic.constant_absorbed_eventually ((3*(n:ℝ)+5)^p)
    (loss-τ*p) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro i hi
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpow : 1≤Z^τ := Real.one_le_rpow hZ hτ.le
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  have hx : 3+(3*i+2:ℕ)*Z^τ≤(3*(n:ℝ)+5)*Z^τ := by push_cast;nlinarith
  calc
    _ ≤ ((3*(n:ℝ)+5)*Z^τ)^p := Real.rpow_le_rpow (by positivity) hx hp
    _ = (3*(n:ℝ)+5)^p*Z^(τ*p) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hZp.le _),←Real.rpow_mul hZp.le]
    _ ≤ Z^(loss-τ*p)*Z^(τ*p) := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^loss := by rw [←Real.rpow_add hZp];congr 1;ring

theorem central_remaining_rowCost_scale (e eps τ loss : ℝ) (n : ℕ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps) (hτ : 0<τ)
    (hgap : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,∀(η : Character) (u : FreeRow)
      {ι : Type*} [Fintype ι] (ψ : ι→Character) (a : ℝ) (i : ℕ),i≤n →
      51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*Z^τ)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤(3*i+2:ℕ)*Z^τ →
      ‖centralRemainingScalar S hS η u x w z‖*
        ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*Z^τ)≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*Z^loss := by
  obtain ⟨C,hC,hbound⟩ := central_remaining_rowCost_bound e eps he he' heps S hS hfirst
  refine ⟨C,hC,?_⟩
  filter_upwards [cube_height_power_eventually n τ (2+4*eps) loss hτ (by positivity) hgap,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))] with Z hheight hZ
  intro η u ι _ ψ a i hi ha ha1 hbin x w z hx hw hz hxi
  have hb := hbound η u ψ (Z^τ) a ((3*i+2:ℕ)*Z^τ) i hZ ha ha1 le_rfl hbin x w z hx hw hz hxi
  exact hb.trans (mul_le_mul_of_nonneg_left (hheight i hi) (by unfold rowNorm;positivity))

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CubePhaseBins -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbeRayCharacterFamily
open HeckePrimeAmplitudeBins ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_phase_bins_on_cube (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (hmax : ∀P∈S,P.IsMaximal)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hAB : A≤B)
    (hWs : Function.support W⊆Ioo A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ cost mesh δ ν : ℝ) (n : ℕ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hν : 0<ν) (hheight : 2*τ<dmin*cost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀(η : Character) (u : FreeRow),Z^δ≤ rowNorm u →
      (ProbePhysical.calibrationForSet S hmax).residueMonoid u.val≠0 →
      rowNorm u≤Z^(d-ν) →
    ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u
        (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse)) (3*(i+1:ℕ)*Z^τ)<a+2*e →
    ∀(r : ℝ) (t : ProbeMellinBoundary.HeightSpace),rmin≤ r → r≤R →
      ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
    let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
    let D := (Z^d)^r
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H u.val W B D z
    let g := amplitude D (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤D^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) ∧
      ‖∑P∈pool (RayQuotient.identityClass M H) S A B D,
        W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val))‖≤D^(z.re-1/2+g+mesh) := by
  have hb := ProbeRayPhaseBins.actual_phase_bins M H hH S hS hbad W A B hA hAB hWs hW
    R dmin dmax rmin τ ε e κ cost mesh (33/50) (33/50) δ
    hR hdmin hdmax hrmin hτ hε he he' hκ hcost hmesh hδ hbudget hgap
  filter_upwards [hb,cube_height_budget_eventually n τ dmin cost hτ hcost hheight,
    ray_cube_conductor_eventually M ν hν,eventually_gt_atTop (0:ℝ)] with Z hb hh hc hZ
  intro d hd hd' hU hT η u hu hcal hrow a i hi ha ha' hbin r t hr hr' ht
  have hs := calibration_nonzero_supported S hmax hbad u.val hcal
  have hpow : 0≤Z^τ := Real.rpow_nonneg hZ.le _
  have hbuffer : ((3*i+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*i+2:ℕ)*Z^τ := by
    push_cast
    nlinarith
  have hfreq := (cube_buffered_heights t ((3*i+1:ℕ)*Z^τ) (Z^τ) i ht hpow hbuffer).2.2
  have hb' := hb d hd hd' hU hT η u hu hs (hc u d hrow) a i ha ha' hbin r
    ((17/50:ℂ)+t.1.2*Complex.I) hr hr'
    (by norm_num) (by norm_num) (by simpa using hfreq) (hh i hi d hd)
  exact hb'

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

