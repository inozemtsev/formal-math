module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part019
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part028
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part015
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part018
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part026
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part014
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part023
public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part029

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace SevenEighths.CenteredMomentSecondExceptionalFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentPartitionNorm
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedWidth
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondRadicalColumns
open CenteredMomentSecondReducedPredicate CenteredMomentSecondLiveBlock CenteredMomentSecondBlockSupport
open CenteredMomentSecondPhysicalBlock CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentRestrictedEnergy CenteredMomentSectorLocalization RayFourExpansion
open CenteredExceptionalProfile CenteredMomentReflectedSource
local notation "O" => HeckeFamily.O

theorem span_thirty_six_norm : (Ideal.span {(36:O)}).absNorm=1296 := by
  have h := ActualEisensteinCubic.rational_modulus_card 36 (by norm_num)
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
  exact h

theorem reflected_modulus_bound (τ:Character) :
    (reflected τ).modulus.absNorm≤1296*τ.modulus.absNorm := by
  have h := HeckePrimeScale.product_modulus_bound τ (HeckeUnitRows.character (-1:Oˣ))
  change (reflected τ).modulus.absNorm≤τ.modulus.absNorm*(Ideal.span {(36:O)}).absNorm at h
  simpa only [span_thirty_six_norm,mul_comm] using h

theorem common_subproduct_dvd_left (C D:Ideal O) (hC:Supported C)
    (hCD:primeSupport C=primeSupport D) (S:Finset (CommonIndex C D)) :
    (∏P∈S,P.val)∣C := by
  have h₁ := Finset.prod_dvd_prod_of_subset S Finset.univ
    (fun P:CommonIndex C D=>P.val) (Finset.subset_univ S)
  have h₂ : (∏P:CommonIndex C D,P.val)∣
      ∏P:CommonIndex C D,Ideal.span {commonPrime C D P}^leftExponent C D P := by
    apply Finset.prod_dvd_prod_of_dvd
    intro P _
    rw [commonPrime_span C D hC]
    exact dvd_pow_self _ (Nat.ne_zero_of_lt (leftExponent_pos C D P))
  rw [left_ideal_product C D hC hCD] at h₂
  exact h₁.trans h₂

theorem common_subproduct_dvd_right (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (S:Finset (CommonIndex C D)) :
    (∏P∈S,P.val)∣D := by
  have h₁ := Finset.prod_dvd_prod_of_subset S Finset.univ
    (fun P:CommonIndex C D=>P.val) (Finset.subset_univ S)
  have h₂ : (∏P:CommonIndex C D,P.val)∣
      ∏P:CommonIndex C D,Ideal.span {commonPrime C D P}^rightExponent C D P := by
    apply Finset.prod_dvd_prod_of_dvd
    intro P _
    rw [commonPrime_span C D hC]
    exact dvd_pow_self _ (Nat.ne_zero_of_lt (rightExponent_pos C D P))
  rw [right_ideal_product C D hC hD hCD] at h₂
  exact h₁.trans h₂

theorem selected_nonunit_product (C D:Ideal O) (hC:Supported C)
    (U:Finset (CommonIndex C D)) :
    (∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}=
      ∏P∈U∪nonunitPartitionSet C D U,P.val := by
  have hd : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hP hV
    exact (Finset.mem_sdiff.mp hV).2 hP
  rw [Finset.prod_union hd,nonunitFrequencyGenerator_span]
  simp only [unitIdeal,commonPrime_span C D hC]

theorem selected_nonunit_dvd (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D)) :
    ((∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}∣C) ∧
    ((∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}∣D) := by
  rw [selected_nonunit_product C D hC]
  exact ⟨common_subproduct_dvd_left C D hC hCD _,
    common_subproduct_dvd_right C D hC hD hCD _⟩

theorem selected_nonunit_norm (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D)) :
    (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm≤C.absNorm ∧
    (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm≤D.absNorm := by
  obtain ⟨h₁,h₂⟩ := selected_nonunit_dvd C D hC hD hCD U
  constructor
  · simpa only [map_mul] using Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)) (map_dvd Ideal.absNorm h₁)
  · simpa only [map_mul] using Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)) (map_dvd Ideal.absNorm h₂)

structure Family (η:Character) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (τ:RayCharacter→Character) : Prop where
  element_eq : ∀χ n,elementCoeff (τ χ) n=
    rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n
  height_eq : ∀χ I,Supported I→(IsCoprime C I ∨ IsCoprime D I)→∀t,
    heightCoeff (τ χ) t I=heightCoeff η t I*
      idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
      rayCharacter χ (primaryGenerator I)
  physical_budget : ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U R rows W K n≠0→∀χ,
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
    ∀Z:ℝ,1<Z→∀z∈liveRows C D U R rows,
      Real.logb Z (normValue z)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
        Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ))

theorem exists_exceptional_family (η:Character) (C D:Ideal O)
    (hC:Supported C) (hD:Supported D) (hCD:primeSupport C=primeSupport D)
    (U:Finset (CommonIndex C D)) : ∃τ,Family η C D hC hD U τ := by
  choose τ he ht hrest using fun χ:RayCharacter=>exists_retained_width_family η χ C D hC U
  refine ⟨τ,he,?_,?_⟩
  · intro χ I hI hi t
    rw [ht χ I hI t]
    rcases hi with hi|hi
    · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
    · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]
  · intro t S β R rows W K hK n hne χ
    have hne':physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n≠0:=by
      rwa [←physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
    obtain ⟨w,_,hwc⟩:=physicalBlock_nonzero_common η t S β C D hC hD hCD U R
      (liveRows C D U R rows) (fun z hz=>(liveRows_geometry C D U R rows z hz).2.1)
      W K hK n hne'
    obtain ⟨hN,hwidth⟩:=hrest χ hD hCD (nonunitFrequencyGenerator C D U*w) hwc
    refine ⟨hN,?_⟩
    intro Z hZ z hz
    exact (hwidth Z R hZ z (liveRows_weight C D U R rows z hz)).2.2.2.2.2

namespace Family
variable {η:Character} {C D:Ideal O} {hC:Supported C} {hD:Supported D}
  {U:Finset (CommonIndex C D)} {τ:RayCharacter→Character}

theorem nonexceptional_iff (h:Family η C D hC hD U τ) (χ:RayCharacter)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow (τ χ) Q fixedBadMask 1 z :=
  actual_nonexceptional_iff η (τ χ) χ C D hC U (h.element_eq χ) Q m z hm hml hm2

theorem inducing_iff (h:Family η C D hC hD U τ) (χ:RayCharacter)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow (τ χ) Q fixedBadMask 1 z :=
  actual_reduced_inducing_iff η (τ χ) χ C D hC U (h.element_eq χ) Q m z hm hz hml hm2

theorem paired_inducing_iff (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O) (hQ:Q≤Ideal.span {(72:O)}) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (τ χ) Q fixedBadMask 1 z ↔
      FixedInducingRow (τ ξ) Q fixedBadMask 1 (-z) :=
  (h.inducing_iff χ Q m z hm hz hml hm2).symm.trans
    ((CenteredMomentExceptionalReflection.fixedInducingRow_reflection_iff η χ ξ Q hQ m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z hml hm2).trans
      (h.inducing_iff ξ Q m (-z) hm (neg_ne_zero.mpr hz) hml hm2))

theorem both_inducing (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O) (hQ:Q≤Ideal.span {(72:O)}) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m)
    (hex:FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) :
    FixedInducingRow (τ χ) Q fixedBadMask 1 z ∧
      FixedInducingRow (reflected (τ ξ)) Q fixedBadMask 1 z := by
  have hleft := (h.inducing_iff χ Q m z hm hz hml hm2).mp hex
  refine ⟨hleft,?_⟩
  exact (reflected_inducing (τ ξ) Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp
    ((h.paired_inducing_iff χ ξ Q hQ m z hm hz hml hm2).mp hleft)

theorem reflected_height_eq (h:Family η C D hC hD U τ) (ξ:RayCharacter)
    (I:Ideal O)(hI:Supported I)(hi:IsCoprime C I ∨ IsCoprime D I)(t:ℝ) :
    heightCoeff (reflected (τ ξ)) t I=heightCoeff η t I*
      idealRowHom (-(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)) I*
      rayCharacter ξ (primaryGenerator I) := by
  have hneg : idealRowHom (-(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)) I=
      idealRowHom (-1) I*idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I := by
    rw [show -(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)=
      (-1)*(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) by ring]
    exact idealRowHom_argument_mul _ _ _
  rw [reflected_height _ _ _ hI,h.height_eq ξ I hI hi t,hneg]
  ring

theorem live_both_inducing (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O)(hQ:Q≤Ideal.span {(72:O)})(m z:O)(hm:m≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)
    (radius:ℝ)(rows:Finset O)(hz:z∈liveRows C D U radius rows)
    (hex:FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) :
    z≠0 ∧ FixedInducingRow (τ χ) Q fixedBadMask 1 z ∧
      FixedInducingRow (reflected (τ ξ)) Q fixedBadMask 1 z := by
  have hz0 := (liveRows_geometry C D U radius rows z hz).2.1
  exact ⟨hz0,h.both_inducing χ ξ Q hQ m z hm hz0 hml hm2 hex⟩

theorem physical_conductor_bounds (h:Family η C D hC hD U τ)
    (hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)(χ:RayCharacter) :
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*C.absNorm ∧
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*D.absNorm := by
  have hN := (h.physical_budget t S β R rows W K hK n hne χ).1
  obtain ⟨h₁,h₂⟩ := selected_nonunit_norm C D hC hD hCD U
  constructor
  · exact hN.trans <| by
      simpa only [mul_assoc] using (Nat.mul_le_mul_left (η.modulus.absNorm*fixedFactor) h₁)
  · exact hN.trans <| by
      simpa only [mul_assoc] using (Nat.mul_le_mul_left (η.modulus.absNorm*fixedFactor) h₂)

end Family

def expandedConductor (τ:Character)(R C:Ideal O)(z:O):ℕ :=
  τ.modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
    (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm

def expandedFactor (η:Character):ℕ :=
  1296*η.modulus.absNorm*fixedFactor*(Ideal.span {fixedBadMask}).absNorm*
    (Ideal.span {(72:O)}).absNorm

theorem expanded_conductor_bounds {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O) :
    expandedConductor (τ χ) R C z≤
      expandedFactor η*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm ∧
    expandedConductor (reflected (τ ξ)) R D z≤
      expandedFactor η*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm := by
  have hl := (h.physical_conductor_bounds hCD t S β radius rows W K hK n hne χ).2
  have hr := (h.physical_conductor_bounds hCD t S β radius rows W K hK n hne ξ).1
  have hl' : (τ χ).modulus.absNorm≤1296*(η.modulus.absNorm*fixedFactor*D.absNorm) := by
    exact hl.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  have hr' := (reflected_modulus_bound (τ ξ)).trans (Nat.mul_le_mul_left 1296 hr)
  constructor
  · calc
      expandedConductor (τ χ) R C z≤
        (1296*(η.modulus.absNorm*fixedFactor*D.absNorm))*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm := by
            unfold expandedConductor
            gcongr
      _=_ := by unfold expandedFactor;ring
  · calc
      expandedConductor (reflected (τ ξ)) R D z≤
        (1296*(η.modulus.absNorm*fixedFactor*C.absNorm))*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm := by
            unfold expandedConductor
            gcongr
      _=_ := by unfold expandedFactor;ring

theorem eventually_expanded_conductor_caps (η:Character)(ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(z:O)(c d r m:ℝ),
    (C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→(R.absNorm:ℝ)≤Z^r→normValue z≤Z^m→
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+ε) := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (expandedFactor η:ℝ)
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.1 he
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ C D hC hD hCD U τ h t S β radius rows W K hK n hne χ ξ R z c d r m hCN hDN hRN hzn
  have hZpos : 0<Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have hconstant := hZ₀ Z ((le_max_right _ _).trans hZ)
  have hproduct : (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm≤
      Z^(c+d+r+m+ε) := by
    calc
      _≤Z^ε*Z^r*Z^c*Z^d*Z^m := by
        change (Ideal.absNorm (Ideal.span {z}):ℝ)≤_ at hzn
        gcongr
      _=Z^(c+d+r+m+ε) := by
        rw [←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos]
        congr 1
        ring
  obtain ⟨hl,hr⟩ := expanded_conductor_bounds h hCD t S β radius rows W K hK n hne χ ξ R z
  constructor
  · exact (show (expandedConductor (τ χ) R C z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hl).trans hproduct
  · exact (show (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hr).trans hproduct

theorem live_norm_le_four_radius (C D:Ideal O)(U:Finset (CommonIndex C D))
    (radius:ℝ)(rows:Finset O)(z:O)(hz:z∈liveRows C D U radius rows) :
    normValue z≤4*radius := by
  obtain ⟨hr,hg,hv,_,_,hn,_⟩ := retained_geometry radius
    (commonFrequencyGenerator C D) (nonunitFrequencyGenerator C D U) z
    (liveRows_weight C D U radius rows z hz)
  have hG := normValue_ge_one _ hg
  have hV := normValue_ge_one _ hv
  have hprod : 1≤normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hG) (sub_nonneg.mpr hV)]
  exact hn.trans (div_le_self (by positivity) hprod)

theorem eventually_live_expanded_conductor_caps (η:Character)(ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m:ℝ),
    (C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→(R.absNorm:ℝ)≤Z^r→ radius≤Z^m→
    ∀z∈liveRows C D U radius rows,z≠0 ∧
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+ε) := by
  obtain ⟨Z₁,hZ₁,h₁⟩ := eventually_expanded_conductor_caps η (ε/2) (by positivity)
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<ε/2 by positivity))) (4:ℝ)
  obtain ⟨Z₂,h₂⟩ := Filter.eventually_atTop.1 he
  refine ⟨max Z₁ Z₂,hZ₁.trans_le (le_max_left _ _),?_⟩
  intro Z hZ C D hC hD hCD U τ h t S β radius rows W K hK n hne χ ξ R c d r m hCN hDN hRN hrad z hz
  have hZpos : 0<Z := zero_lt_one.trans (hZ₁.trans_le ((le_max_left _ _).trans hZ))
  have hfour := h₂ Z ((le_max_right _ _).trans hZ)
  have hfreq : normValue z≤Z^(m+ε/2) := by
    calc
      _≤4*radius := live_norm_le_four_radius C D U radius rows z hz
      _≤Z^(ε/2)*Z^m := mul_le_mul hfour hrad
        (liveRows_geometry C D U radius rows z hz).1.le (Real.rpow_nonneg hZpos.le _)
      _=Z^(m+ε/2) := by rw [←Real.rpow_add hZpos,add_comm]
  have hc := h₁ Z ((le_max_left _ _).trans hZ) C D hC hD hCD U τ h t S β radius rows W K hK
    n hne χ ξ R z c d r (m+ε/2) hCN hDN hRN hfreq
  have hexp : c+d+r+(m+ε/2)+ε/2=c+d+r+m+ε := by ring
  rw [hexp] at hc
  exact ⟨(liveRows_geometry C D U radius rows z hz).2.1,hc⟩

end SevenEighths.CenteredMomentSecondExceptionalFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondChildRadialWidth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondChildRadialWidth
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRadicalBudget
open CenteredMomentSecondActualWidth CenteredMomentSecondWidthDrop
local notation "O" => HeckeFamily.O

theorem physicalBlock_live_dyadic_witness (η:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z:O,z∈liveRows C D U R rows ∧ z∈dyadicRows rows n ∧
      z≠0 ∧ dyadicScale (n 1)<4*normValue z := by
  rw [physicalBlock_live_dyadic_rows η t S β C D hC hD U R rows W K n] at hne
  unfold physicalBlock at hne
  obtain ⟨z,hz,_⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hl,hd⟩:=(mem_dyadicRows _ n z).mp hz
  have hz':z∈dyadicRows rows n:=(mem_dyadicRows rows n z).mpr
    ⟨(Finset.mem_filter.mp hl).1,hd⟩
  exact ⟨z,hl,hz',dyadicRows_nonzero rows n z hz',by
    have hh:=(dyadicRows_norm rows n z hz').1
    linarith⟩

section Family
variable {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
  {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
  (h:Family η C D hC hD U τ)
  (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
  (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
  (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)

include h hK hne

theorem dyadic_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*(fixedFactor:ℝ)) := by
  obtain ⟨z,hzl,_,hz0,hscale⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U R rows W K n hne
  have hw:=(h.physical_budget t S β R rows W K hK n hne χ).2 Z hZ z hzl
  have hh:=Real.logb_le_logb_of_le hZ (dyadicScale_pos (n 1)) hscale.le
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) (normValue_pos z hz0).ne'] at hh
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*(fixedFactor:ℝ))=
      Real.logb Z (4:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul (by norm_num : (4:ℝ)≠0) (by positivity : 4*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [hf]
  linarith

omit h hK hne in

theorem radial_support_bound (Φ:ℝ→ℂ)(b:ℝ)
    (hs:Function.support Φ⊆Set.Iic b)(y:O)
    (hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y≤b*dyadicScale (n 1) :=
  (div_le_iff₀ (dyadicScale_pos (n 1))).mp (hs hy)

theorem radial_radius_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hh:=dyadic_log_budget h t S β R rows W K hK n hne Z hZ χ
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*(fixedFactor:ℝ))=
      Real.logb Z b+Real.logb Z (16*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hb.ne' (by positivity : 16*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [Real.logb_mul hb.ne' (dyadicScale_pos (n 1)).ne',hf]
  linarith

theorem radial_point_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (normValue y)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hl:=Real.logb_le_logb_of_le hZ (normValue_pos y hy0)
    (radial_support_bound n Φ b hs y hy)
  have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb
  linarith

theorem declared_radial_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hbH:1≤b*dyadicScale (n 1):=(normValue_ge_one y hy0).trans
    (radial_support_bound n Φ b hs y hy)
  rw [max_eq_right hbH]
  exact radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb

theorem whole_radial_norm_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ))) := by
  have hτ:(0:ℝ)<(τ χ).modulus.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (τ χ).modulus_ne_bot)
  have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb
  rw [←Real.logb_mul (mul_pos hb (dyadicScale_pos (n 1))).ne' hτ.ne'] at hh
  exact (mul_le_mul_of_nonneg_right (radial_support_bound n Φ b hs y hy) hτ.le).trans
    ((Real.logb_le_iff_le_rpow hZ (mul_pos (mul_pos hb (dyadicScale_pos (n 1))) hτ)).mp hh)

end Family

theorem fixed_radial_cost_eventually (b ε:ℝ)(hb:0<b)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→Real.logb Z (16*b*(fixedFactor:ℝ))≤ε := by
  have he:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (16*b*(fixedFactor:ℝ))
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (he.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ
  obtain ⟨hc,hZ1⟩:=hZ₀ Z ((le_max_right _ _).trans hZ)
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  exact (Real.logb_le_iff_le_rpow hZ1 (by positivity)).mpr hc

theorem eventually_whole_radial_width (b ε:ℝ)(hb:0<b)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(η:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
      (U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U R rows W K n≠0→
    ∀(χ:RayCharacter)(Φ:ℝ→ℂ),Function.support Φ⊆Set.Iic b→
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε ∧
    ∀y:O,Φ (normValue y/dyadicScale (n 1))≠0→
      normValue y*((τ χ).modulus.absNorm:ℝ)≤
        Z^(Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
          Real.logb Z (normValue (commonFrequencyGenerator C D))+
          Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε) := by
  obtain ⟨Z₀,hZ₀,hcost⟩:=fixed_radial_cost_eventually b ε hb hε
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ η C D hC hD U τ h t S β R rows W K hK n hne χ Φ hs
  have hZ1:=hZ₀.trans_le hZ
  have hc:=hcost Z hZ
  constructor
  · have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ1 χ b hb
    linarith
  · intro y hy
    exact (whole_radial_norm_budget h t S β R rows W K hK n hne Z hZ1 χ Φ b hb hs y hy).trans
      (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))

theorem physical_declared_radial_width_drop {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H K Tsec Csec ξ M σ g:ℝ)(hZ:1<Z)(hH:0<H)(hK:0<K)
    (hT:0<Tsec)(hCs:0<Csec)
    (hg:amplificationIncrement η Z H K M σ≤g)
    (hscale:Tsec≤Csec*(H^2/(K*Z^g))) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ)
      rows W (K*Z^g) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      M-σ+ξ/2+Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hKg:0<K*Z^g:=mul_pos hK (Real.rpow_pos_of_pos hz _)
  have hw:=declared_radial_log_budget h t S β (frequencyRadius Tsec Z ξ) rows W
    (K*Z^g) hKg n hne Z hZ χ Φ b hb hs y hy0 hy
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hn:nominalLength Z H K g+Real.logb Z (η.modulus.absNorm:ℝ)≤M-σ := by
    have hnom:=actual_nominal_drop η Z H K M σ
    unfold nominalLength at hnom ⊢
    linarith
  rw [physical_frequency_scale Z H K g hZ hH hK] at hscale
  have hl:=Real.logb_le_logb_of_le hZ hT hscale
  rw [Real.logb_mul hCs.ne' (Real.rpow_pos_of_pos hz _).ne',
    Real.logb_rpow hz hZ.ne'] at hl
  have hr:Real.logb Z (frequencyRadius Tsec Z ξ)≤
      nominalLength Z H K g+ξ/2+Real.logb Z Csec := by
    rw [frequencyRadius,Real.logb_mul hT.ne' (Real.rpow_pos_of_pos hz _).ne',
      Real.logb_rpow hz hZ.ne']
    linarith
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*Csec*(fixedFactor:ℝ))=
      Real.logb Z Csec+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hCs.ne' (by positivity : 16*b*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [hf]
  linarith

end SevenEighths.CenteredMomentSecondChildRadialWidth

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AmplifiedChildWidth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplifiedChildWidth
open ActualEisensteinCubic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CenteredMomentSecondRadicalBudget
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondActualWidth CenteredMomentSecondWidthDrop
open CenteredMomentSecondCanonical CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem modulus_pos (η:Character) : 0<(η.modulus.absNorm:ℝ) :=
  norm_pos _ η.modulus_ne_bot
theorem span_pos (m:O)(hm:m≠0) : 0<((Ideal.span {m}).absNorm:ℝ) :=
  norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr hm)

theorem canonical_modulus_log (η ρ:Character)(m:O)(hm:m≠0)
    (I J:Ideal O)(A:Finset (CommonIndex I J))(Z:ℝ)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J}) :
    Real.logb Z (ρ.modulus.absNorm:ℝ)=
      Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((∏P∈A,P.val).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ) := by
  have he:0<((∏P∈A,P.val).absNorm:ℝ) := by
    apply norm_pos
    exact Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  rw [hmod,first_displayed_norm]
  push_cast
  rw [Real.logb_mul (mul_pos (mul_pos (modulus_pos η) (span_pos m hm))
      (span_pos 72 (by norm_num))).ne' (mul_pos he (active_norm_pos I J)).ne',
    Real.logb_mul (mul_pos (modulus_pos η) (span_pos m hm)).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (modulus_pos η).ne' (span_pos m hm).ne',
    Real.logb_mul he.ne' (active_norm_pos I J).ne']
  ring

theorem radical_error_log_bound (ρ η:Character)(χ:RayCharacter)(m p:O)
    (hm:m≠0)(hp:p≠0)(Z:ℝ)(hZ:1<Z)(n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:η.modulus.absNorm≤ radicalBound (childCharacter ρ χ) m p (errorMovingExponent n)) :
    Real.logb Z (η.modulus.absNorm:ℝ)≤
      Real.logb Z (ρ.modulus.absNorm:ℝ)+Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+errorMoving p Z (n+1) := by
  have hmpos:=span_pos m hm
  have h12:=span_pos 12 (by norm_num)
  have h72:=span_pos 72 (by norm_num)
  have hρ:=modulus_pos ρ
  have hray:( (childCharacter ρ χ).modulus.absNorm:ℝ)≤
      (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm := by
    exact_mod_cast child_modulus_bound ρ χ
  have hb:(η.modulus.absNorm:ℝ)≤
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)) := by
    have hh:(η.modulus.absNorm:ℝ)≤(radicalBound (childCharacter ρ χ) m p (errorMovingExponent n):ℝ):=by exact_mod_cast hN
    rw [radicalBound_error_power _ m p hp Z hZ n hn] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hray (by positivity))
        (by positivity)) (by positivity))
  have hh:=Real.logb_le_logb_of_le hZ (modulus_pos η) hb
  rw [Real.logb_mul (by positivity : (0:ℝ)<
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm).ne'
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
    Real.logb_mul (by positivity : (0:ℝ)<
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*(Ideal.span {m}).absNorm).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (mul_pos (modulus_pos ρ) (span_pos 12 (by norm_num))).ne' (span_pos m hm).ne',
    Real.logb_mul (modulus_pos ρ).ne' (span_pos 12 (by norm_num)).ne',
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  linarith

theorem common_nominal_identity (A c d R E m q w wo σ δ reserve branch:ℝ) :
    2*(A-c-w)-(2*A-c-d+R+E-m+
      max (d-c-2*w+wo) 0+branch*σ+δ+reserve)+(q+R+E+wo)=
    m+q+(d-c-2*w+wo-max (d-c-2*w+wo) 0)-branch*σ-δ-reserve := by ring

theorem common_nominal_le (A c d R E m q w wo σ δ reserve branch:ℝ) :
    2*(A-c-w)-(2*A-c-d+R+E-m+
      max (d-c-2*w+wo) 0+branch*σ+δ+reserve)+(q+R+E+wo)≤
    m+q-branch*σ-δ-reserve := by
  rw [common_nominal_identity]
  linarith [le_max_left (d-c-2*w+wo) (0:ℝ)]

theorem shortened_log (I J:Ideal O)(X Z:ℝ)(hX:0<X)(p:O)(hp:p≠0)(k:ℕ) :
    Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^k))=
      Real.logb Z X-Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)-errorRemoval p Z k := by
  rw [Real.logb_div hX.ne' (mul_pos (norm_pos _ (commonPart_ne_zero I J))
    (pow_pos (normValue_pos p hp) k)).ne',
    Real.logb_mul (norm_pos _ (commonPart_ne_zero I J)).ne' (pow_pos (normValue_pos p hp) k).ne',
    Real.logb_pow]
  unfold errorRemoval
  ring

theorem main_nominal_bound (η ρ:Character)(m:O)(hm:m≠0)(I J:Ideal O)
    (A:Finset (CommonIndex I J))(K X Z σ δ reserve:ℝ)
    (hK:0<K)(hX:0<X)(hZ:1<Z)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J}) :
    2*Real.logb Z (X/(commonPart I J).absNorm)-
      Real.logb Z (mainCommonRadius Z (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ))
        (nominalLog I J (∏P∈A,P.val) K X Z) (Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) σ δ reserve)+
      Real.logb Z (ρ.modulus.absNorm:ℝ)≤
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)-
      2*σ-δ-reserve := by
  have he:(∏P∈A,P.val)≠0 := Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  rw [Real.logb_div hX.ne' (norm_pos _ (commonPart_ne_zero I J)).ne',
    mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',
    nominalLog,CenteredMomentFirstPhysicalLedger.nominal_log I J _ he Z K X hK hX,
    canonical_modulus_log η ρ m hm I J A Z hmod]
  linarith [le_max_left (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)-
    Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) (0:ℝ)]

theorem error_nominal_bound (η ρ θ:Character)(χ:RayCharacter)(m₀ m₁ p:O)
    (hm₀:m₀≠0)(hm₁:m₁≠0)(hp:p≠0)(I J:Ideal O)(A:Finset (CommonIndex I J))
    (K X Z σ δ reserve:ℝ)(hK:0<K)(hX:0<X)(hZ:1<Z)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m₀}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J})
    (n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:θ.modulus.absNorm≤ radicalBound (childCharacter ρ χ) m₁ p (errorMovingExponent n)) :
    2*Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^(n+1)))-
      Real.logb Z (errorCommonRadius Z (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ))
        (nominalLog I J (∏P∈A,P.val) K X Z) (Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) σ δ reserve p (n+1))+
      Real.logb Z (θ.modulus.absNorm:ℝ)≤
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {m₀}).absNorm:ℝ)+Real.logb Z ((Ideal.span {m₁}).absNorm:ℝ)+
      2*Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)-σ-δ-reserve := by
  have he:(∏P∈A,P.val)≠0 := Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  have hq:=radical_error_log_bound ρ θ χ m₁ p hm₁ hp Z hZ n hn hN
  rw [canonical_modulus_log η ρ m₀ hm₀ I J A Z hmod] at hq
  rw [shortened_log I J X Z hX p hp (n+1),errorCommonRadius,
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',nominalLog,
    CenteredMomentFirstPhysicalLedger.nominal_log I J _ he Z K X hK hX]
  linarith [le_max_left (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)-
    Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)-2*errorRemoval p Z (n+1)+errorMoving p Z (n+1)) (0:ℝ)]

theorem physical_radial_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)-
      Real.logb Z (normValue (commonFrequencyGenerator C D))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hw:=radial_radius_log_budget h t S β (frequencyRadius Tsec Z ξ) rows W L hL n hne Z hZ χ b hb
  have hl:=Real.logb_le_logb_of_le hZ hT hscale
  rw [Real.logb_mul hCs.ne' (div_pos (sq_pos_of_pos hH) hL).ne',
    Real.logb_div (sq_pos_of_pos hH).ne' hL.ne',Real.logb_pow] at hl
  have hr:Real.logb Z (frequencyRadius Tsec Z ξ)≤
      2*Real.logb Z H-Real.logb Z L+ξ/2+Real.logb Z Csec := by
    rw [frequencyRadius,Real.logb_mul hT.ne'
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
    push_cast at hl
    linarith
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*Csec*(fixedFactor:ℝ))=
      Real.logb Z Csec+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hCs.ne' (by positivity : (16:ℝ)*b*fixedFactor≠0)]
    congr 1
    ring
  rw [hf]
  linarith

theorem physical_declared_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hh:=physical_radial_budget h t S β rows W Z H L Tsec Csec ξ hZ hH hL hT hCs hscale n hne χ b hb
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hbH:1≤b*dyadicScale (n 1):=(normValue_ge_one y hy0).trans
    (radial_support_bound n Φ b hs y hy)
  rw [max_eq_right hbH]
  linarith

theorem physical_whole_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
        Real.logb Z (16*b*Csec*(fixedFactor:ℝ))) := by
  have hh:=physical_radial_budget h t S β rows W Z H L Tsec Csec ξ hZ hH hL hT hCs hscale n hne χ b hb
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hb':Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
        Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by linarith
  rw [←Real.logb_mul (mul_pos hb (dyadicScale_pos (n 1))).ne' (modulus_pos (τ χ)).ne'] at hb'
  exact (mul_le_mul_of_nonneg_right (radial_support_bound n Φ b hs y hy)
    (modulus_pos (τ χ)).le).trans
    ((Real.logb_le_iff_le_rpow hZ (mul_pos (mul_pos hb (dyadicScale_pos (n 1)))
      (modulus_pos (τ χ)))).mp hb')

theorem original_coefficient_fixed_mask {ι:Type*}[Fintype ι]
    (D:OriginalData ι)(ρ:Character)(t T:ℝ) :
    D.coefficient ρ fixedBadMask t T=
      fun I:supportedColumns D.columns => (Real.sqrt T:ℂ)⁻¹*(D.beta I*heightCoeff ρ t I) := by
  funext I
  rw [OriginalData.coefficient,←heightCoeff_eq_fixed_rowWeight ρ t I
    (Finset.mem_filter.mp I.property).2]

def presentationFactor : ℝ :=
  ((Ideal.span {(72:O)}).absNorm:ℝ)*(fixedFactor:ℝ)

theorem presentationFactor_pos : 0<presentationFactor :=
  mul_pos (span_pos 72 (by norm_num)) (by exact_mod_cast fixedFactor_pos)

theorem presentationFactor_log (Z:ℝ) : Real.logb Z presentationFactor=
    2*Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ) := by
  unfold presentationFactor fixedFactor
  push_cast
  rw [Real.logb_mul (span_pos 72 (by norm_num)).ne'
      (mul_pos (mul_pos (span_pos 12 (by norm_num)) (span_pos fixedBadMask fixedBadMask_ne_zero))
        (span_pos 72 (by norm_num))).ne',
    Real.logb_mul (mul_pos (span_pos 12 (by norm_num)) (span_pos fixedBadMask fixedBadMask_ne_zero)).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (span_pos 12 (by norm_num)).ne' (span_pos fixedBadMask fixedBadMask_ne_zero).ne']
  ring

theorem first_fixed_log_le (Z:ℝ)(hZ:1<Z) :
    Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)≤Real.logb Z presentationFactor := by
  apply Real.logb_le_logb_of_le hZ (span_pos 72 (by norm_num))
  have hf:(1:ℝ)≤fixedFactor:=by exact_mod_cast fixedFactor_pos
  exact le_mul_of_one_le_right (span_pos 72 (by norm_num)).le hf

theorem exists_fixed_width_threshold (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→∀ξ:ℝ,ξ≤σ/4→
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)<σ/2 := by
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  let C:ℝ:=((Ideal.span {fixedBadMask}).absNorm:ℝ)*(16*b*Csec*(fixedFactor:ℝ)*presentationFactor)
  have hCp:0<C:=mul_pos (span_pos fixedBadMask fixedBadMask_ne_zero)
    (mul_pos (by positivity : (0:ℝ)<16*b*Csec*fixedFactor) presentationFactor_pos)
  have he:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<σ/4 by linarith))) C
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (he.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ ξ hξ
  obtain ⟨hCZ,hZ1⟩:=hZ₀ Z ((le_max_right _ _).trans hZ)
  have hh:Real.logb Z C≤σ/4:=(Real.logb_le_iff_le_rpow hZ1 hCp).mpr hCZ
  dsimp [C] at hh
  rw [Real.logb_mul (span_pos fixedBadMask fixedBadMask_ne_zero).ne'
    (mul_pos (by positivity : (0:ℝ)<16*b*Csec*fixedFactor) presentationFactor_pos).ne'] at hh
  linarith

def fixedWidthThreshold (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) : ℝ :=
  (exists_fixed_width_threshold b Csec σ hb hCs hσ).choose

theorem fixedWidthThreshold_spec (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) :
    1<fixedWidthThreshold b Csec σ hb hCs hσ ∧
    ∀Z:ℝ,fixedWidthThreshold b Csec σ hb hCs hσ≤Z→∀ξ:ℝ,ξ≤σ/4→
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)<σ/2 :=
  (exists_fixed_width_threshold b Csec σ hb hCs hσ).choose_spec

section ActualSource
variable (η ρ:Character)(m:O)(hm:m≠0)(I J:Ideal O)(A:Finset (CommonIndex I J))
  (K X Z σ δ reserve:ℝ)(hK:0<K)(hX:0<X)(hZ:1<Z)
  (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J})

local notation "cc" => Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)
local notation "dd" => Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)
local notation "kk" => nominalLog I J (∏P∈A,Subtype.val P) K X Z
local notation "Lm" => mainCommonRadius Z dd kk cc σ δ reserve
local notation "Hx" => X/Ideal.absNorm (commonPart I J)
local notation "parentWidth" => Real.logb Z K+Real.logb Z (Ideal.absNorm (Character.modulus η):ℝ)+Real.logb Z (Ideal.absNorm (Ideal.span (Singleton.singleton m)):ℝ)
include σ δ reserve hm hK hX hZ hmod

theorem main_nominal_fixed :
    2*Real.logb Z Hx-Real.logb Z Lm+Real.logb Z (ρ.modulus.absNorm:ℝ)≤
      parentWidth+Real.logb Z presentationFactor-2*σ-δ-reserve := by
  have hh:=main_nominal_bound η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  linarith [first_fixed_log_le Z hZ]

theorem error_nominal_fixed (θ:Character)(χ:RayCharacter)(p:O)(hp:p≠0)
    (n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:θ.modulus.absNorm≤ radicalBound (childCharacter ρ χ) fixedBadMask p (errorMovingExponent n)) :
    2*Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^(n+1)))-
      Real.logb Z (errorCommonRadius Z dd kk cc σ δ reserve p (n+1))+
      Real.logb Z (θ.modulus.absNorm:ℝ)≤
      parentWidth+Real.logb Z presentationFactor-σ-δ-reserve := by
  have hh:=error_nominal_bound η ρ θ χ m fixedBadMask p hm fixedBadMask_ne_zero hp
    I J A K X Z σ δ reserve hK hX hZ hmod n hn hN
  rw [presentationFactor_log]
  linarith

theorem main_declared_width {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      parentWidth-2*σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor) := by
  have hHx:0<Hx:=div_pos hX (norm_pos _ (commonPart_ne_zero I J))
  have hL:0<Lm:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_declared_budget h t S β rows W Z Hx Lm Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hnom:=main_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem error_declared_width (θ:Character)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤ radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      parentWidth-σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor) := by
  have hHx:0<X/((commonPart I J).absNorm*(normValue p)^(k+1)):=
    div_pos hX (mul_pos (norm_pos _ (commonPart_ne_zero I J)) (pow_pos (normValue_pos p hp) _))
  have hL:0<errorCommonRadius Z dd kk cc σ δ reserve p (k+1):=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_declared_budget h t S β rows W Z _ _ Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hnom:=error_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem main_whole_width {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(parentWidth-2*σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)) := by
  have hHx:0<Hx:=div_pos hX (norm_pos _ (commonPart_ne_zero I J))
  have hL:0<Lm:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_whole_budget h t S β rows W Z Hx Lm Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy
  have hnom:=main_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  apply hw.trans
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem error_whole_width (θ:Character)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤ radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(parentWidth-σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)) := by
  have hHx:0<X/((commonPart I J).absNorm*(normValue p)^(k+1)):=
    div_pos hX (mul_pos (norm_pos _ (commonPart_ne_zero I J)) (pow_pos (normValue_pos p hp) _))
  have hL:0<errorCommonRadius Z dd kk cc σ δ reserve p (k+1):=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_whole_budget h t S β rows W Z _ _ Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy
  have hnom:=error_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  apply hw.trans
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem main_declared_width_drop {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0)
    (hmask:m=fixedBadMask)(q:ℝ)(hcap:(η.modulus.absNorm:ℝ)≤Z^q)
    (hσ:0<σ)(hδ:0≤δ)(hr:0≤ reserve)(hξ:ξ≤σ/4)
    (hlarge:fixedWidthThreshold b Csec σ hb hCs hσ≤Z) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)<
      Real.logb Z K+q-σ/2 := by
  have hw:=main_declared_width η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod h t S β rows W Tsec Csec ξ hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hq:Real.logb Z (η.modulus.absNorm:ℝ)≤q:=
    (Real.logb_le_iff_le_rpow hZ (modulus_pos η)).mpr hcap
  have hc:=(fixedWidthThreshold_spec b Csec σ hb hCs hσ).2 Z hlarge ξ hξ
  rw [hmask] at hw
  linarith

theorem error_declared_width_drop (θ:Character)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤ radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0)
    (hmask:m=fixedBadMask)(q:ℝ)(hcap:(η.modulus.absNorm:ℝ)≤Z^q)
    (hσ:0<σ)(hδ:0≤δ)(hr:0≤ reserve)(hξ:ξ≤σ/4)
    (hlarge:fixedWidthThreshold b Csec σ hb hCs hσ≤Z) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)<
      Real.logb Z K+q-σ/2 := by
  have hw:=error_declared_width η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN h t S β rows W Tsec Csec ξ hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hq:Real.logb Z (η.modulus.absNorm:ℝ)≤q:=
    (Real.logb_le_iff_le_rpow hZ (modulus_pos η)).mpr hcap
  have hc:=(fixedWidthThreshold_spec b Csec σ hb hCs hσ).2 Z hlarge ξ hξ
  rw [hmask] at hw
  linarith

end ActualSource
end SevenEighths.CenteredMomentAmplifiedChildWidth

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamilyUniform -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace SevenEighths.CenteredMomentSecondExceptionalFamilyUniform
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondHeightFamily
open CenteredMomentSecondRadicalBudget CenteredMomentSecondLiveBlock
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentReflectedSource CenteredMomentSecondExceptionalFamily
local notation "O" => HeckeFamily.O

def fixedExpandedCost : ℝ :=
  1296*(fixedFactor:ℝ)*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

theorem fixedExpandedCost_pos : 0<fixedExpandedCost := by
  have hb : (0:ℝ)<(Ideal.span {fixedBadMask}).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have h72 : (0:ℝ)<(Ideal.span {(72:O)}).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (show (72:O)≠0 by norm_num)))
  have hf : (0:ℝ)<fixedFactor := by exact_mod_cast fixedFactor_pos
  unfold fixedExpandedCost
  positivity

theorem expandedFactor_real (η:Character) :
    (expandedFactor η:ℝ)=fixedExpandedCost*(η.modulus.absNorm:ℝ) := by
  unfold expandedFactor fixedExpandedCost
  push_cast
  ring

theorem expanded_real_bounds {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O) :
    (expandedConductor (τ χ) R C z:ℝ)≤
      fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*normValue z ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*normValue z := by
  obtain ⟨hl,hr⟩ := expanded_conductor_bounds h hCD t S β radius rows W K hK n hne χ ξ R z
  have hl' : (expandedConductor (τ χ) R C z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*normValue z := by
    dsimp only [normValue]
    exact_mod_cast hl
  have hr' : (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*normValue z := by
    dsimp only [normValue]
    exact_mod_cast hr
  rw [expandedFactor_real] at hl' hr'
  exact ⟨hl',hr'⟩

theorem live_expanded_real_bounds {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O)(hz:z∈liveRows C D U radius rows) :
    0< radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤
      (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius := by
  obtain ⟨hR,hz0,hz1,_⟩ := liveRows_geometry C D U radius rows z hz
  obtain ⟨hl,hr⟩ := expanded_real_bounds h hCD t S β radius rows W K hK n hne χ ξ R z
  have hf := fixedExpandedCost_pos
  have hbound : fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*normValue z≤
      (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius := by
    calc
      _≤fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*(4*radius) :=
        mul_le_mul_of_nonneg_left (live_norm_le_four_radius C D U radius rows z hz)
          (by positivity)
      _=_ := by ring
  exact ⟨hR,hz0,hz1,hl.trans hbound,hr.trans hbound⟩

theorem eventually_uniform_live_caps (ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→∀η:Character,
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m q:ℝ),
    (η.modulus.absNorm:ℝ)≤Z^q→(C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→
    (R.absNorm:ℝ)≤Z^r→ radius≤Z^m→∀z∈liveRows C D U radius rows,
    0< radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+q+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+q+ε) := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (4*fixedExpandedCost)
  obtain ⟨Z₁,hZ₁⟩ := Filter.eventually_atTop.1 he
  refine ⟨max 2 Z₁,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ η C D hC hD hCD U τ h t S β radius rows W K hK n hne χ ξ R c d r m q hη hCN hDN hRN hrad z hz
  have hZpos : 0<Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have hconstant := hZ₁ Z ((le_max_right _ _).trans hZ)
  obtain ⟨hR,hz0,hz1,hl,hr⟩ := live_expanded_real_bounds h hCD t S β radius rows W K hK n hne χ ξ R z hz
  have hbound : (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius≤
      Z^(c+d+r+m+q+ε) := by
    calc
      _≤Z^ε*Z^q*Z^r*Z^c*Z^d*Z^m := by gcongr
      _=Z^(c+d+r+m+q+ε) := by
        rw [←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,
          ←Real.rpow_add hZpos,←Real.rpow_add hZpos]
        congr 1
        ring
  exact ⟨hR,hz0,hz1,hl.trans hbound,hr.trans hbound⟩

theorem exists_uniform_exceptional_family (ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀(η:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D),
    primeSupport C=primeSupport D→∀U:Finset (CommonIndex C D),
    ∃τ:RayCharacter→Character,Family η C D hC hD U τ ∧
    ∀Z:ℝ,Z₀≤Z→∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m q:ℝ),
    (η.modulus.absNorm:ℝ)≤Z^q→(C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→
    (R.absNorm:ℝ)≤Z^r→ radius≤Z^m→∀z∈liveRows C D U radius rows,
    0< radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+q+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+q+ε) := by
  obtain ⟨Z₀,hZ₀,hcaps⟩ := eventually_uniform_live_caps ε hε
  refine ⟨Z₀,hZ₀,?_⟩
  intro η C D hC hD hCD U
  obtain ⟨τ,hτ⟩ := exists_exceptional_family η C D hC hD hCD U
  refine ⟨τ,hτ,?_⟩
  intro Z hZ
  exact hcaps Z hZ η C D hC hD hCD U τ hτ

end SevenEighths.CenteredMomentSecondExceptionalFamilyUniform

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPairDictionary -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondExceptionalPairDictionary
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

lemma raw_pair (V:ℝ)(hV:0<V)(a b:ℂ):
    ‖a‖*‖b‖=V*‖(Real.sqrt V:ℂ)⁻¹*a‖*‖(Real.sqrt V:ℂ)⁻¹*b‖:=by
  have hs:0<Real.sqrt V:=Real.sqrt_pos.mpr hV
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  field_simp
  rw [Real.sq_sqrt hV.le]

omit [DecidableEq ι] in
theorem original_pair (s:Input ι)(η τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y:ℝ)(Ds:Finset (Ideal O))(rows:Finset O)
    (hτ₁:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ₁ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (hτ₂:∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
      heightCoeff τ₂ v I=heightCoeff η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient A (sectorElement C hC.1 S)
            (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
          columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) w) z‖*
      ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*
          star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) w)) (-z)‖)=
      volume s.toData*(∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖windowColumn s C hC R seed L τ₁ t w X logAnnulus z‖*
        ‖windowColumn s D hD R seed L (reflected τ₂) t (-w) Y logAnnulus z‖):=by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  rw [mul_left_comm (volume s.toData) ‖(moebius L:ℂ)‖]
  apply congrArg (fun a:ℝ=>‖(moebius L:ℂ)‖*a)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [raw_pair (volume s.toData) (volume_pos s.toData)]
  rw [actual_sector_window s η τ₁ χ A C hC R seed L t w X logAnnulus z hτ₁,
    actual_reflected_sector_window s η τ₂ ξ A D hD R seed L t w Y z hτ₂]
  ring

end SevenEighths.CenteredMomentSecondExceptionalPairDictionary

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPairBound -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalPairBound
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonExceptionalWindow CenteredMomentExceptionalWindowHeight
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def originalPair (s:Input ι)(η:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y:ℝ)(Ds:Finset (Ideal O))(rows:Finset O):ℝ:=
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient A (sectorElement C hC.1 S)
            (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
          columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) w) z‖*
      ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*
          star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) w)) (-z)‖)

omit [DecidableEq ι] in
lemma window_withHeight (s:Input ι)(τ η:Character)(v t θ X:ℝ)(C:Ideal O)(hC:Supported C)
    (R seed L:Ideal O)(V:ℝ→ℂ)(z:O):
    windowColumn (withHeight s τ v) C hC R seed L η t θ X V z=
      windowColumn s C hC R seed L η t θ X V z:=rfl

theorem actual_original_pair (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀(τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O),
      (∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
        heightCoeff τ₁ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
        heightCoeff τ₂ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)) →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z)) →
      (∀z∈rows,(τ₁.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,((reflected τ₂).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(X Y:ℝ),0<X → 0<Y → ∀Ds:Finset (Ideal O),
      (∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) → ∀w:ℝ,
      originalPair s s.η χ ξ A C D hC hD R seed s.t w X Y Ds rows≤
        (K*(rows.card:ℝ)*Z^(2*ε+δ-max (r-Real.logb Z (C.absNorm:ℝ)) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*
            frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2)*
          (1+‖w‖)^(2*J):=by
  obtain ⟨J,hJ⟩:=actual_common_window lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hb:=hZ.2 (withHeight s τ₁ s.t) (withHeight s (reflected τ₂) s.t) p p hlo hhi
    hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD r r
    hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ w (-w) X Y hX hY Ds hDs
  simp only [window_withHeight] at hb
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hb (volume_pos s.toData).le).trans
  have hm:=mass_phase s s p p w J
  let F:=volume s.toData*(K*(rows.card:ℝ)*Z^(2*ε+δ-max (r-Real.logb Z (C.absNorm:ℝ)) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)))*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (volume_pos s.toData).le
      (mul_nonneg (by positivity) (div_nonneg (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s))
        (by positivity)))) (sq_nonneg _)
  calc
    _=F*mass s s p p s.t s.t w (-w) J:=by
      dsimp only [F,frozenProfile,withHeight,mass,
        CenteredMomentAllocatedDetectorAmplitude.slotControl,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _≤F*((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*(1+‖w‖)^(2*J)):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentSecondExceptionalPairBound

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQPair -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary CenteredMomentSecondExceptionalPairBound
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_original_pair (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀(τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O),
      (∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
        heightCoeff τ₁ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
        heightCoeff τ₂ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)) →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z)) →
      (∀z∈rows,(τ₁.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,((reflected τ₂).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ₀:RayCharacter)(U:Finset (CommonIndex C D)),
      idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ₀) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(X Y:ℝ),0<X → 0<Y → ∀Ds:Finset (Ideal O),
      (∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) → ∀w:ℝ,
      originalPair s s.η χ ξ A C D hC hD R seed s.t w X Y Ds rows≤
        (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
            frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2)*
          (1+‖w‖)^(2*J):=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_canonical_common_window wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ η₀ χ₀ U hη m hm hml hm2 hex Cr M hCr hN X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hb:=hZ.2 (withHeight s τ₁ s.t) (withHeight s (reflected τ₂) s.t) p p hlo hhi hlo hhi
    hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD r r
    hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ η₀ χ₀ U hη m hm hml hm2 hex Cr M hCr hN w (-w) X Y hX hY Ds hDs
  simp only [window_withHeight] at hb
  rw [CenteredMomentCommonExceptionalSymmetry.same_raw_better_cap] at hb
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hb (volume_pos s.toData).le).trans
  have hm:=mass_phase Sprofile s s p p w J
  let F:=volume s.toData*(K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)))*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (volume_pos s.toData).le
      (mul_nonneg (by positivity) (div_nonneg (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s))
        (by positivity)))) (sq_nonneg _)
  calc
    _=F*mass Sprofile s s p p s.t s.t w (-w) J:=by
      dsimp only [F,frozenProfile,withHeight,CenteredMomentFiniteProfileExceptionalCommon.mass,
        CenteredMomentAllocatedDetectorAmplitude.slotControl,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _≤F*((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*(1+‖w‖)^(2*J)):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalPair -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary CenteredMomentSecondExceptionalPairBound
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_original_pair (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀(τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O),
      (∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
        heightCoeff τ₁ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
        heightCoeff τ₂ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)) →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z)) →
      (∀z∈rows,(τ₁.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,((reflected τ₂).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ₀:RayCharacter)(U:Finset (CommonIndex C D)),
      IsCoprime Q C → idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ₀) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(X Y:ℝ),0<X → 0<Y → ∀Ds:Finset (Ideal O),
      (∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) → ∀w:ℝ,
      originalPair s s.η χ ξ A C D hC hD R seed s.t w X Y Ds rows≤
        (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
            frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2)*
          (1+‖w‖)^(2*J):=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_canonical_common_window wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ η₀ χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hb:=hZ.2 (withHeight s τ₁ s.t) (withHeight s (reflected τ₂) s.t) p p hlo hhi hlo hhi
    hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD r r
    hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ η₀ χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN w (-w) X Y hX hY Ds hDs
  simp only [window_withHeight] at hb
  rw [CenteredMomentCommonExceptionalSymmetry.same_raw_better_cap] at hb
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hb (volume_pos s.toData).le).trans
  have hm:=mass_phase Sprofile s s p p w J
  let F:=volume s.toData*(K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)))*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (volume_pos s.toData).le
      (mul_nonneg (by positivity) (div_nonneg (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s))
        (by positivity)))) (sq_nonneg _)
  calc
    _=F*mass Sprofile s s p p s.t s.t w (-w) J:=by
      dsimp only [F,frozenProfile,withHeight,CenteredMomentFiniteProfileExceptionalCommon.mass,
        CenteredMomentAllocatedDetectorAmplitude.slotControl,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _≤F*((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*(1+‖w‖)^(2*J)):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSecondDivisorSupport
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondExceptionalPairBound RayFourExpansion
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem live_right_divisor_norm (D I L:Ideal O)(hD:D≠0)(hI:I≠0)
    (β:Ideal O→ℂ)(H:ℝ)(hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)
    (hne:β (D*I)≠0)(hLI:L∣I):
    (L.absNorm:ℝ)≤H/(D.absNorm:ℝ):=by
  have hDpos:(0:ℝ)<D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hnorm:(L.absNorm:ℝ)≤I.absNorm:=by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)) (map_dvd Ideal.absNorm hLI)
  have hb:=hβ (D*I) hne
  rw [map_mul,Nat.cast_mul] at hb
  apply hnorm.trans
  apply (le_div_iff₀ hDpos).mpr
  simpa only [mul_comm] using hb

theorem right_divisor_coefficient_zero
    (D:Ideal O)(hD:Supported D)(S:Finset (Ideal O))(β:Ideal O→ℂ)(H:ℝ)
    (hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)(L:Ideal O)(hL:H/(D.absNorm:ℝ)<L.absNorm)
    (η:Character)(t:ℝ)(A:O)(ξ:RayCharacter)(I:sectorPool D hD.1 S):
    divisorCoefficient L (sectorElement D hD.1 S)
      (movingCoefficient A (sectorElement D hD.1 S)
        (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I=0:=by
  unfold divisorCoefficient
  rw [sectorElement_span]
  split_ifs with hd
  · have hz:β (D*I)=0:=by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (sectorPool_supported D hD.1 S I).1 β H hβ hn hd)
    simp only [movingCoefficient,hz,zero_mul]
  · rfl

theorem right_divisor_row_zero
    (D:Ideal O)(hD:Supported D)(S:Finset (Ideal O))(β:Ideal O→ℂ)(H:ℝ)
    (hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)(L:Ideal O)(hL:H/(D.absNorm:ℝ)<L.absNorm)
    (η:Character)(t:ℝ)(A:O)(ξ:RayCharacter)(v:sectorPool D hD.1 S→ℂ)(z:O):
    rowPolynomial Finset.univ (sectorElement D hD.1 S)
      (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
        (movingCoefficient A (sectorElement D hD.1 S)
          (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*v I) z=0:=by
  unfold rowPolynomial
  apply Finset.sum_eq_zero
  intro I hI
  exact mul_eq_zero_of_left
    (mul_eq_zero_of_left (right_divisor_coefficient_zero D hD S β H hβ L hL η t A ξ I) _) _

theorem originalPair_filter_right {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(η:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y H:ℝ)(Ds:Finset (Ideal O))(rows:Finset O)
    (hβ:∀I:Ideal O,finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I≠0→
      (I.absNorm:ℝ)≤H):
    originalPair s η χ ξ A C D hC hD R seed t w X Y Ds rows=
      originalPair s η χ ξ A C D hC hD R seed t w X Y
        (Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ))) rows:=by
  unfold originalPair
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hLD
  by_cases hL:(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)
  · rw [ite_eq_left hL]
  · rw [ite_eq_right hL]
    have hz:=right_divisor_row_zero D hD (finiteColumns (Fintype.piFinset s.pools))
      (finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed))
      H hβ L (lt_of_not_ge hL) η t A ξ
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro z hzr
    apply mul_eq_zero_of_right
    exact norm_eq_zero.mpr (hz _ _)

end SevenEighths.CenteredMomentSecondDivisorSupport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBlock -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def sourceBudget {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
    Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
      (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
      2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*
    ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
      frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

lemma sourceBudget_nonneg {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ)(hK:0≤K)(hZ:0≤Z)(hCr:0≤Cr):
    0≤ sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M:=by
  have hp:=profileMass_nonneg Sprofile s.toData s.toData p p J
  have hf:=frozenProfile_nonneg s
  have hv:0≤volume s.toData:=(volume_pos s.toData).le
  unfold sourceBudget
  positivity

theorem actual_original_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀X Y:ℝ,0<X → 0<Y →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R:ℝ)(ρ x:O→ℝ)(rK:ℝ),0< rK →
      (1+rK)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff s.η s.t I)*star (β (D*J)*heightCoeff s.η s.t J))*
              wholeKernel W (fun _=>logAnnulus) rK (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M:=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_canonical_original_pair wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  obtain ⟨Ck,hCk,hkernel⟩:=actual_exceptional_block_bound W decay (2*J)
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN X Y hX hY H hβ hHD R ρ x rK hrK
  apply hkernel rK hrK s.η s.t S β C D hC hD hCD U R rows ρ x
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) Q m χ₀ hQ72 hml hm2 hex
    (sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M)
    (sourceBudget_nonneg Sprofile s p J Q C D U K Z ε δ θ r Cr M hK.le (zero_lt_one.trans hZ.1).le hCr)
  intro χ ξ _ _ w
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD r
    hX₁ hX₂ hY₁ hY₂ (τ χ) (τ (ξ⁻¹)) χ (ξ⁻¹) A
    (fun I hI hc v=>hτ χ I hI (Or.inl hc) v)
    (fun I hI hc v=>hτ (ξ⁻¹) I hI (Or.inr hc) v)
    rows hn (hex₁ χ) (hex₂ (ξ⁻¹)) (hcond₁ χ) (hcond₂ (ξ⁻¹))
    s.η χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY
    ((divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))).filter
      (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)))
    (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hHD) w
  change originalPair s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y
    (divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))) rows≤_
  rw [originalPair_filter_right s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y H _ rows hβ]
  exact hp

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQBlock -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_original_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀X Y:ℝ,0<X → 0<Y →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R:ℝ)(ρ x:O→ℝ)(rK:ℝ),0< rK →
      (1+rK)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff s.η s.t I)*star (β (D*J)*heightCoeff s.η s.t J))*
              wholeKernel W (fun _=>logAnnulus) rK (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M:=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_canonical_original_pair wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  obtain ⟨Ck,hCk,hkernel⟩:=actual_exceptional_block_bound W decay (2*J)
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex Cr M hCr hN X Y hX hY H hβ hHD R ρ x rK hrK
  apply hkernel rK hrK s.η s.t S β C D hC hD hCD U R rows ρ x
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) Q m χ₀ hQ72 hml hm2 hex
    (sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M)
    (sourceBudget_nonneg Sprofile s p J Q C D U K Z ε δ θ r Cr M hK.le (zero_lt_one.trans hZ.1).le hCr)
  intro χ ξ _ _ w
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD r
    hX₁ hX₂ hY₁ hY₂ (τ χ) (τ (ξ⁻¹)) χ (ξ⁻¹) A
    (fun I hI hc v=>hτ χ I hI (Or.inl hc) v)
    (fun I hI hc v=>hτ (ξ⁻¹) I hI (Or.inr hc) v)
    rows hn (hex₁ χ) (hex₂ (ξ⁻¹)) (hcond₁ χ) (hcond₂ (ξ⁻¹))
    s.η χ₀ U hη m hm hml hm2 hex Cr M hCr hN X Y hX hY
    ((divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))).filter
      (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)))
    (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hHD) w
  change originalPair s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y
    (divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))) rows≤_
  rw [originalPair_filter_right s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y H _ rows hβ]
  exact hp

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQRows -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_physical_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_original_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex Cr M hCr hN H hβ hHD R Kphys hKphys n rK
  have hrK:0< rK:=div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hh:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex Cr M hCr hN (dyadicScale (n 2)) (dyadicScale (n 3))
    (dyadicScale_pos _) (dyadicScale_pos _) H hβ hHD R
    (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1))) rK hrK
  change (1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤_ at hh
  have ho:0≤outerScalar C D Kphys n:=by unfold outerScalar; positivity
  have hno:0≤normalizer C D U:=(normalizer_pos C D hC U).le
  rw [physicalBlock_eq s.η s.t S β C D hC hD U R rows hn W Kphys hKphys n,
    norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
  calc
    _=(outerScalar C D Kphys n*normalizer C D U)*
        ((1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQDyadic -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_dyadic_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_physical_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n rK
  rw [physicalBlock_dyadic_rows s.η s.t S β C D hC hD U R rows W Kphys n]
  exact hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ (dyadicRows rows n)
    (fun z hz=>dyadicRows_nonzero rows n z hz)
    (fun χ z hz=>hex₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hex₂ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hcond₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hcond₂ χ z (dyadicRows_subset rows n hz))
    χ₀ hη m hm hml hm2 (fun z hz=>hex z (dyadicRows_subset rows n hz))
    1 (Real.logb Z (dyadicScale (n 1))) (by norm_num)
    (fun z hz=>by simpa only [one_mul] using dyadicRows_power_cap rows n Z hZ.1 z hz)
    H hβ hHD R Kphys hKphys n

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid
open CenteredMomentSecondPhysicalLedger
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentForcing CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma profileMass_self {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ):
    profileMass Sprofile s.toData s.toData p p J=
      p.control Sprofile^2*(1+‖s.t‖)^(2*J)*slotControl s.toData^2*volume s.toData:=by
  have hs:volume s.toData=Real.sqrt (volume s.toData)*Real.sqrt (volume s.toData):=by
    nlinarith [Real.sq_sqrt (volume_pos s.toData).le]
  unfold CenteredMomentFiniteProfileExceptionalCommon.profileMass
  rw [show 2*J=J+J by omega,pow_add]
  conv_rhs => rw [hs]
  ring

lemma count_power (Z h f e:ℝ)(hZ:1<Z)(hh:0<h)(hf:0<f):
    Z^((Real.logb Z h-4*Real.logb Z f)/6+e)=
      h^(1/6:ℝ)/f^(2/3:ℝ)*Z^e:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  rw [show (Real.logb Z h-4*Real.logb Z f)/6+e=
    Real.logb Z h*(1/6)-Real.logb Z f*(2/3)+e by ring,
    Real.rpow_add hz,Real.rpow_sub hz,Real.rpow_mul hz.le,Real.rpow_mul hz.le,
    Real.rpow_logb hz (ne_of_gt hZ) hh,Real.rpow_logb hz (ne_of_gt hZ) hf]

def profileFactor {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q:Ideal O)(K:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
    p.control Sprofile^2*(1+‖s.t‖)^(2*J)*slotControl s.toData^2*frozenProfile s^2*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

omit [DecidableEq ι] in
lemma profileFactor_nonneg {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q:Ideal O)(K:ℝ)(hK:0≤K):
    0≤profileFactor Sprofile s p J Q K:=by
  unfold profileFactor
  have hp:=Profiles.control_nonneg p Sprofile
  positivity

lemma sourceBudget_exact {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(U:Finset (CommonIndex C D))(K Z ε δ θ r h:ℝ)
    (hZ:1<Z)(hh:0<h):
    sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z h)=
      profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      (h^(1/6:ℝ)/(forcingNorm C D U)^(2/3:ℝ)*volume s.toData^2/
        ((C.absNorm:ℝ)*D.absNorm)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold sourceBudget
  simp only [forcingNorm] at hf ⊢
  rw [Real.one_rpow, mul_one]
  rw [show (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+2*ε+δ-
      max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0=
      (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
        (2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0) by ring,
    count_power Z h (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ) _ hZ hh hf,profileMass_self]
  unfold profileFactor
  ring

theorem central_sourceBudget_exact {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(_hD:Supported D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys:ℝ)(n:Fin 4→ℤ)(hZ:1<Z):
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))=
    profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      centralPhysicalCost C D U Kphys (volume s.toData) n/
      ((Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  have hp:=common_product_pos C D hC Finset.univ
  have hpow:(forcingNorm C D U)^(2/3:ℝ)=
      (forcingNorm C D U)^(1/3:ℝ)*(forcingNorm C D U)^(1/3:ℝ):=by
    rw [←Real.rpow_add hf];congr 1;ring
  rw [sourceBudget_exact Sprofile s p J Q C D hC U K Z ε δ θ r _ hZ (dyadicScale_pos _),hpow]
  unfold centralPhysicalCost
  field_simp

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end

