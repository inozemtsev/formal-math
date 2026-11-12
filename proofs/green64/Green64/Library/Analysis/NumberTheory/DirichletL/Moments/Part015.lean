module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part014
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part013
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part012

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part015

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondRadicalBudget -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
namespace SevenEighths.CenteredMomentSecondRadicalBudget
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondRadicalFamily CenteredMomentSecondMovingSupport
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst CenteredMomentChildRows CenteredMomentPartitionNorm
open CenteredMomentHeckeColumnWindow RayFourExpansion CenteredMomentCommonSupport CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

def fixedFactor : ℕ := (Ideal.span {(12:O)}).absNorm*
  (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

theorem fixedFactor_pos : 0<fixedFactor := by
  unfold fixedFactor
  apply Nat.mul_pos
  · apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))

theorem child_modulus_bound (η : Character) (χ : RayCharacter) :
    (childCharacter η χ).modulus.absNorm≤η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm := by
  have hn : η.modulus*Ideal.span {(12:O)}≠0 := mul_ne_zero η.modulus_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  have hd : (childCharacter η χ).modulus∣η.modulus*Ideal.span {(12:O)} := by
    apply Ideal.dvd_iff_le.mpr
    exact le_inf Ideal.mul_le_left Ideal.mul_le_right
  simpa only [map_mul] using Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)) (map_dvd Ideal.absNorm hd)

theorem active_radical_dvd (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*w)≠0) :
    (∏P∈fixedActiveSet C D U,P.val)∣
      (∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U} := by
  have hd := Finset.prod_dvd_prod_of_subset (fixedActiveSet C D U)
    (U∪nonunitPartitionSet C D U) (fun P:CommonIndex C D=>P.val)
    (fixedActiveSet_subset C D hC hD hCD U w hne)
  have hdis : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hP hV
    exact (Finset.mem_sdiff.mp hV).2 hP
  rw [Finset.prod_union hdis] at hd
  rw [nonunitFrequencyGenerator_span]
  simpa only [unitIdeal,commonPrime_span C D hC] using hd

theorem active_radical_norm_bound (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*w)≠0) :
    (∏P∈fixedActiveSet C D U,P.val).absNorm≤
      (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by
  have hp (S : Finset (CommonIndex C D)) : (∏P∈S,P.val)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun P _=>(commonPrime_supported_ideal C D hC P).1)
  have hv : Ideal.span {nonunitFrequencyGenerator C D U}≠0 := by
    rw [nonunitFrequencyGenerator_span]
    simpa only [unitIdeal,commonPrime_span C D hC] using hp (nonunitPartitionSet C D U)
  simpa only [map_mul] using Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero (hp U) hv)))
    (map_dvd Ideal.absNorm (active_radical_dvd C D hC hD hCD U w hne))

theorem exists_second_budgeted_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD : Supported D),CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD
        (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*
        (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by
  obtain ⟨τ,hN,he,ht⟩ := exists_second_radical_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hne
  have h1 := child_modulus_bound η χ
  have h2 := active_radical_norm_bound C D hC hD hCD U w hne
  apply hN.trans
  calc
    _≤(η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
      ((∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)) h2
    _=_ := by unfold fixedFactor;ring

theorem conductor_log_bound (η τ : Character) (A B : Ideal O) (hA : A≠0) (hB : B≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*A.absNorm*B.absNorm)
    (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z (fixedFactor:ℝ)+Real.logb Z (A.absNorm:ℝ)+Real.logb Z (B.absNorm:ℝ) := by
  have hτ : (0:ℝ)<τ.modulus.absNorm := by
    exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))
  have hη : (η.modulus.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hK : (fixedFactor:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt fixedFactor_pos)
  have ha : (A.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hA)
  have hb : (B.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hh := Real.logb_le_logb_of_le hZ hτ (show (τ.modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*fixedFactor*A.absNorm*B.absNorm by exact_mod_cast hN)
  rwa [Real.logb_mul (mul_ne_zero (mul_ne_zero hη hK) ha) hb,
    Real.logb_mul (mul_ne_zero hη hK) ha,Real.logb_mul hη hK] at hh

theorem exists_second_log_budgeted_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD : Supported D),CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      ∀Z:ℝ,1<Z → Real.logb Z (τ.modulus.absNorm:ℝ)≤
        Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z (fixedFactor:ℝ)+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ) := by
  obtain ⟨τ,he,ht,hN⟩ := exists_second_budgeted_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hne Z hZ
  have hp (S : Finset (CommonIndex C D)) : (∏P∈S,P.val)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun P _=>(commonPrime_supported_ideal C D hC P).1)
  have hv : Ideal.span {nonunitFrequencyGenerator C D U}≠0 := by
    rw [nonunitFrequencyGenerator_span]
    simpa only [unitIdeal,commonPrime_span C D hC] using hp (nonunitPartitionSet C D U)
  exact conductor_log_bound η τ _ _ (hp U) hv (hN hD hCD w hne) Z hZ

theorem fixed_log_cost_eventually (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ:ℝ in Filter.atTop,1<Z ∧ Real.logb Z (fixedFactor:ℝ)≤ε := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (fixedFactor:ℝ)
  filter_upwards [he,Filter.eventually_gt_atTop (1:ℝ)] with Z hK hZ
  refine ⟨hZ,?_⟩
  have hp : (0:ℝ)<fixedFactor := by exact_mod_cast fixedFactor_pos
  have hh := Real.logb_le_logb_of_le hZ hp hK
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hh

end SevenEighths.CenteredMomentSecondRadicalBudget

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondActualWidth -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondActualWidth
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondRadicalBudget CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentSupport CenteredMomentDescentLedger
open CenteredMomentPartitionNorm CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem actual_common_log_ge_unit (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)≤Real.logb Z (normValue (commonFrequencyGenerator C D)) := by
  have hh:=common_log_ge_unit (commonPrime C D) (commonPrime_supported C D hC)
    (leftExponent C D) (rightExponent C D) (leftExponent_pos C D) (rightExponent_pos C D) U Z hZ
  rw [←commonFrequencyGenerator_span C D hC] at hh
  simpa only [unitIdeal,commonPrime_span C D hC,normValue] using hh

theorem actual_width_bound (η τ : Character) (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z Tsec Csec L ξ : ℝ)
    (hZ : 1<Z) (hCsec : 0<Csec) (hT : Tsec≤Csec*Z^L)
    (hτ : Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z (fixedFactor:ℝ)+Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {nonunitFrequencyGenerator C D U}).absNorm:ℝ))
    (h : O) (hne : retainedWeight (frequencyRadius Tsec Z ξ)
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))≠0) :
    max 0 (L-Real.logb Z (normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))+
      frequencyLoss Z Csec ξ)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
      L+Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z (fixedFactor:ℝ)+frequencyLoss Z Csec ξ-
        (Real.logb Z (normValue (commonFrequencyGenerator C D))-
          Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)) := by
  have hn:=actual_nonempty_width_of_weight Tsec Z Csec L ξ hZ hCsec hT _ h hne
  rw [max_eq_right hn]
  have hg := normValue_pos (commonFrequencyGenerator C D)
    (CenteredMomentSecondCanonicalFrequency.commonFrequencyGenerator_ne_zero C D hC)
  have hv := normValue_pos (nonunitFrequencyGenerator C D U)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  rw [normValue_mul,Real.logb_mul hg.ne' hv.ne']
  change _≤_
  change Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
    Real.logb Z (fixedFactor:ℝ)+Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
      Real.logb Z (normValue (nonunitFrequencyGenerator C D U)) at hτ
  linarith

theorem exists_actual_width_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ:Character,
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        CanonicalRowCompletion.idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD:Supported D),primeSupport C=primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      ∀Z Tsec Csec L ξ M σ:ℝ,1<Z → 0<Csec → Tsec≤Csec*Z^L →
      L+Real.logb Z (η.modulus.absNorm:ℝ)≤M-σ →
      ∀h:O,retainedWeight (frequencyRadius Tsec Z ξ)
        (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))≠0 →
      max 0 (L-Real.logb Z (normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))+
        frequencyLoss Z Csec ξ)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          M-σ+Real.logb Z (fixedFactor:ℝ)+frequencyLoss Z Csec ξ := by
  obtain ⟨τ,he,ht,hN⟩:=exists_second_log_budgeted_family η χ C D hC U
  refine ⟨τ,ht,?_⟩
  intro hD hCD w hw Z Tsec Csec L ξ M σ hZ hCs hT hnom h hh
  have hb:=actual_width_bound η τ C D hC U Z Tsec Csec L ξ hZ hCs hT
    (hN hD hCD w hw Z hZ) h hh
  have hg:=actual_common_log_ge_unit C D hC U Z hZ
  linarith

end SevenEighths.CenteredMomentSecondActualWidth

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondRadicalColumns -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondRadicalColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentSecondSixthSource CenteredMomentSecondRadicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem sixthFactor_span_dvd_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣D := by
  conv_rhs => rw [←right_ideal_product C D hC hD hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  have hd := rightExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤ rightExponent C D P := min_le_right _ _
  unfold fixedExponent
  split_ifs <;> omega

theorem residual_sixth_coefficient_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime D I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,ite_eq_left
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd_right C D hC hD hCD U)),mul_one]

theorem exists_actual_masked_radical_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      τ.modulus.absNorm≤(childCharacter η χ).modulus.absNorm*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (∏P∈fixedActiveSet C D U,P.val).absNorm ∧
      ∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀t:ℝ,
        heightCoeff τ t I=heightCoeff η t I*
          idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
          rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hN,he,hτ⟩ := exists_second_radical_family η χ C D hC U
  refine ⟨τ,hN,?_⟩
  intro I hI hi t
  rw [hτ I hI t]
  rcases hi with hi|hi
  · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
  · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]

end SevenEighths.CenteredMomentSecondRadicalColumns

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondReducedPredicate -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondReducedPredicate
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredExceptionalProfile CenteredMomentFixedRowMask CenteredMomentRestrictedEnergy
open CenteredMomentSecondFamilyTransport CenteredMomentSecondHeightFamily CenteredMomentChildRows
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSixthReduction CenteredMomentCanonicalFirst RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem fixed_mask_change (η : Character) (Q : Ideal O) (m n A z : O)
    (hm:m≠0) (hn:n≠0) (hA:A≠0) (hz:z≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m)
    (hnLam:ConcretePrimeRowBridge.goodLambda∣n) (hn2:(2:O)∣n) :
    FixedInducingRow η Q m A z ↔ FixedInducingRow η Q n A z := by
  have h1:=fixedInducingRow_mul_mask_iff η Q m n A z hm hn hA hz hmLam hm2
  have h2:=fixedInducingRow_mul_mask_iff η Q n m A z hn hm hA hz hnLam hn2
  rw [mul_comm n m] at h2
  exact h1.symm.trans h2

theorem actual_reduced_inducing_iff (η τ : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hz:z≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [fixed_sixth_inducing_iff _ Q m z hm hz hmLam hm2 C D hC U]
  exact (fixed_mask_change (childCharacter η χ) Q m fixedBadMask (reducedNumerator C D U) z
    hm fixedBadMask_ne_zero (reducedNumerator_ne_zero C D hC U) hz hmLam hm2
    (dvd_mul_right _ _) (dvd_mul_left _ _)).trans
      (fixedInducingRow_transport η τ χ _ hτ Q z).symm

theorem actual_nonexceptional_iff (η τ : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D))
    (hτ:∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n)
    (Q:Ideal O) (m z:O) (hm:m≠0)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  unfold nonexceptional
  by_cases hz:z=0
  · simp only [hz,ne_eq,not_true_eq_false,false_and]
  · rw [actual_reduced_inducing_iff η τ χ C D hC U hτ Q m z hm hz hmLam hm2]

end SevenEighths.CenteredMomentSecondReducedPredicate

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NonprincipalGate -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNonprincipalGate
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion
open ConcretePrimeRowBridge CenteredMomentRestrictedEnergy CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O

def unitCharacter : Character := Character.ofResidue ⊤ top_ne_bot 1 (by
  intro u
  exact MulChar.one_apply (IsUnit.map (Ideal.Quotient.mk ⊤) u.isUnit))

theorem unitCharacter_primitive : FiniteFourier.IsPrimitiveOnIdeals unitCharacter.residue := by
  change FiniteFourier.IsPrimitiveOnIdeals (1:MulChar (O⧸(⊤:Ideal O)) ℂ)
  intro I hI
  exact (hI (Subsingleton.elim _ _)).elim

theorem unitCharacter_ideal (I:Ideal O) (hI:I≠0) : idealCoeff unitCharacter I=1 := by
  rw [←span_idealGenerator I,idealCoeff_span _ (idealGenerator_ne_zero I hI)]
  change (1:MulChar (O⧸(⊤:Ideal O)) ℂ) (Ideal.Quotient.mk _ (idealGenerator I))=1
  rw [show Ideal.Quotient.mk (⊤:Ideal O) (idealGenerator I)=1 from Subsingleton.elim _ _]
  exact map_one _

theorem principal_inducedBy_unit (χ:Character) (hχ:χ.residue=1) : InducedBy χ unitCharacter := by
  intro I
  by_cases hI:I=0
  · subst I
    simp only [map_zero,ite_self]
  · have hn:=idealGenerator_ne_zero I hI
    rw [unitCharacter_ideal I hI]
    rw [←span_idealGenerator I,idealCoeff_span χ hn]
    change χ.residue (Ideal.Quotient.mk χ.modulus (idealGenerator I))=_
    rw [hχ]
    by_cases hc:IsCoprime (Ideal.span {idealGenerator I}) χ.modulus
    · rw [ite_eq_left hc]
      exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hc)
    · rw [ite_eq_right hc]
      exact MulChar.map_nonunit _ (fun h=>hc ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp h))

theorem principal_row_fixed (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hχ:χ.residue=1) : FixedInducingRow η Q m A z :=
  ⟨χ,unitCharacter,unitCharacter_primitive,principal_inducedBy_unit χ hχ,le_top,hrow⟩

theorem actual_row_nonprincipal (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hex:¬FixedInducingRow η Q m A z) : χ.residue≠1 :=
  fun h=>hex (principal_row_fixed η χ Q m A z hrow h)

theorem nonexceptional_row_nonprincipal (η χ:Character) (ξ:RayCharacter)
    (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom (childCharacter η ξ)) m 1 (A*z) n)
    (hex:nonexceptional η ξ Q m A z) : χ.residue≠1 :=
  actual_row_nonprincipal (childCharacter η ξ) χ Q m A z hrow hex.2

end SevenEighths.CenteredMomentNonprincipalGate

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => HeckeFamily.O

structure NaturalRow (η : Character) (z : O) where
  character : Character
  modulus_bound : character.modulus.absNorm≤ rowConductorBound η fixedBadMask 1 z
  element : ∀n,elementCoeff character n=rowTwist (elementHom η) fixedBadMask 1 z n

def naturalRow (η : Character) (z : O) (hz : z≠0) : NaturalRow η z := by
  let e:=exists_row_character_with_conductor η fixedBadMask 1 z
    fixedBadMask_ne_zero one_ne_zero hz (dvd_mul_right _ _) (dvd_mul_left _ _)
  exact ⟨Classical.choose e,(Classical.choose_spec e).1,(Classical.choose_spec e).2⟩

lemma NaturalRow.ideal {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff F.character I=idealCoeff η I*idealRowHom (fixedBadMask^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η F.character fixedBadMask 1 z F.element I

lemma NaturalRow.element_zero {η : Character} {z : O} (F : NaturalRow η z) :
    elementCoeff F.character 0=0 := by
  rw [F.element]
  change elementHom η 0*idealRowHom (fixedBadMask^6*1^4*z) (Ideal.span {(0:O)})=0
  rw [Ideal.span_singleton_zero]
  change elementHom η 0*idealRowHom (fixedBadMask^6*1^4*z) (0:Ideal O)=0
  rw [(idealRowHom (fixedBadMask^6*1^4*z)).map_zero,mul_zero]

lemma NaturalRow.masked_element {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (n : O) :
    elementCoeff (excluded F.character R) n=
      rowTwist (elementHom η) (fixedBadMask*idealGenerator R) 1 z n := by
  rw [excluded_element_generator F.character F.element_zero R hR,F.element]
  simpa only [one_mul] using
    (row_mask_mul η fixedBadMask (idealGenerator R) 1 z n
      (dvd_mul_right _ _) (dvd_mul_left _ _)).symm

lemma NaturalRow.masked_ideal {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (I : Ideal O) :
    idealCoeff (excluded F.character R) I=
      idealCoeff η I*idealRowHom ((fixedBadMask*idealGenerator R)^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η (excluded F.character R)
    (fixedBadMask*idealGenerator R) 1 z (F.masked_element R hR) I

lemma NaturalRow.masked_element_span {η : Character} {z : O} (F : NaturalRow η z)
    (r : O) (hr : r≠0) (n : O) :
    elementCoeff (excluded F.character (Ideal.span {r})) n=
      rowTwist (elementHom η) (fixedBadMask*r) 1 z n := by
  rw [excluded_element F.character F.element_zero (Ideal.span {r})
    (Ideal.span_singleton_eq_bot.not.mpr hr),Ideal.isCoprime_span_singleton_iff,F.element]
  simpa only [one_mul] using
    (row_mask_mul η fixedBadMask r 1 z n (dvd_mul_right _ _) (dvd_mul_left _ _)).symm

theorem NaturalRow.nonprincipal {η : Character} {z : O} (F : NaturalRow η z)
    (hz : z≠0) (Q R : Ideal O) (hR : R≠0)
    (hex : ¬FixedInducingRow η Q (fixedBadMask*idealGenerator R) 1 z) :
    F.character.residue≠1 := by
  have hbase : ¬FixedInducingRow η Q fixedBadMask 1 z := by
    intro h
    exact hex ((fixedInducingRow_mul_mask_iff η Q fixedBadMask (idealGenerator R) 1 z
      fixedBadMask_ne_zero (idealGenerator_ne_zero R hR) one_ne_zero hz
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h)
  exact CenteredMomentNonprincipalGate.actual_row_nonprincipal η F.character Q fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) hbase

def fixedConductorFactor : ℕ := (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

lemma NaturalRow.natural_modulus_bound {η : Character} {z : O} (F : NaturalRow η z) :
    F.character.modulus.absNorm≤η.modulus.absNorm*fixedConductorFactor*(Ideal.span {z}).absNorm := by
  have hh:=F.modulus_bound
  simpa [rowConductorBound,fixedConductorFactor,Ideal.span_singleton_one,mul_assoc] using hh

theorem NaturalRow.modulus_power_bound {η : Character} {z : O} (F : NaturalRow η z)
    (Z m q Cz : ℝ) (hZ : 0<Z) (_hCz : 0≤Cz)
    (hη : (η.modulus.absNorm:ℝ)≤Z^m)
    (hz : ((Ideal.span {z}).absNorm:ℝ)≤Cz*Z^q) :
    (F.character.modulus.absNorm:ℝ)≤(fixedConductorFactor:ℝ)*Cz*Z^(m+q) := by
  have hb : (F.character.modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*(fixedConductorFactor:ℝ)*((Ideal.span {z}).absNorm:ℝ) :=
    by exact_mod_cast F.natural_modulus_bound
  apply hb.trans
  calc
    _≤(Z^m*(fixedConductorFactor:ℝ))*(Cz*Z^q) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)) hz
        (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg hZ.le _) (Nat.cast_nonneg _))
    _=(fixedConductorFactor:ℝ)*Cz*Z^(m+q) := by rw [Real.rpow_add hZ]; ring

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceDictionary -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O

lemma NaturalRow.masked_plain {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (W : ℝ→ℂ) (t X : ℝ) :
    rowTwistedSum η (fixedBadMask*idealGenerator R) 1 z W t X=
      twistedIdealSum (excluded F.character R) W t X := by
  exact rowTwistedSum_eq η (excluded F.character R) (fixedBadMask*idealGenerator R) 1 z
    (by simpa only [one_mul] using F.masked_element R hR) W t X

lemma NaturalRow.masked_slot {η : Character} {z : O} (F : NaturalRow η z)
    (R : Ideal O) (hR : R≠0) (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t : ℝ) :
    rowSlot η (fixedBadMask*idealGenerator R) 1 z S β t=
      ∑I∈S,β I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t) := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.masked_ideal R hR I,one_mul]

theorem NaturalRow.masked_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) W₁ t X₁*
          twistedIdealSum (excluded F.character R) W₂ t X₂)*
          ∏i,∑I∈S i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  simp only [positiveSlotRow,F.masked_plain R hR,F.masked_slot R hR]

theorem NaturalRow.masked_retained {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    retainedPositiveRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ S β P t X₁ X₂=
      (Real.sqrt (clippedScale X₁*clippedScale X₂*∏i,P i):ℂ)⁻¹*
        ((twistedIdealSum (excluded F.character R) (dilated W₁ (clipDilation X₁)) t (clippedScale X₁)*
          twistedIdealSum (excluded F.character R) (dilated W₂ (clipDilation X₂)) t (clippedScale X₂))*
          ∏i,∑I∈S i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t)) := by
  exact F.masked_positive R hR _ _ S β P t _ _

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondRetainedWidth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology

namespace SevenEighths.CenteredMomentSecondRetainedWidth
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondRadicalBudget CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentCanonicalFirst
open CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem retained_geometry (R : ℝ) (G V z : O)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    0<R ∧ G≠0 ∧ V≠0 ∧ z≠0 ∧ 1≤normValue z ∧
      normValue z≤4*R/(normValue G*normValue V) ∧
      1≤4*R/(normValue G*normValue V) := by
  obtain ⟨hGV,hz⟩:=retained_product_ne_zero R (G*V) z hne
  have hg:=left_ne_zero_of_mul hGV
  have hv:=right_ne_zero_of_mul hGV
  have hrow:=retained_norm_enclosure R (G*V) z hGV hne
  rw [normValue_mul] at hrow
  have hn:=normValue_ge_one z hz
  have hr:=retainedWeight_enclosure R _ hne
  refine ⟨by linarith,hg,hv,hz,hn,hrow,hn.trans hrow⟩

theorem retained_log_budget (η τ : Character) (G V z : O) (U : Ideal O)
    (hU : U≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*U.absNorm*
      (Ideal.span {V}).absNorm)
    (R Z : ℝ) (hZ : 1<Z)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    Real.logb Z (max 1 (4*R/(normValue G*normValue V)))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue G)+
        Real.logb Z (U.absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨hR,hG,hV,_,_,_,hmax⟩:=retained_geometry R G V z hne
  have hg:=normValue_pos G hG
  have hv:=normValue_pos V hV
  have hF : (fixedFactor:ℝ)≠0:=by exact_mod_cast fixedFactor_pos.ne'
  have hc:=conductor_log_bound η τ U (Ideal.span {V}) hU
    (Ideal.span_singleton_eq_bot.not.mpr hV) hN Z hZ
  change Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
    Real.logb Z (fixedFactor:ℝ)+Real.logb Z (U.absNorm:ℝ)+Real.logb Z (normValue V) at hc
  rw [max_eq_right hmax,Real.logb_div (mul_ne_zero (by norm_num) hR.ne')
    (mul_ne_zero hg.ne' hv.ne'),Real.logb_mul (by norm_num : (4:ℝ)≠0) hR.ne',
    Real.logb_mul hg.ne' hv.ne',Real.logb_mul (by norm_num : (4:ℝ)≠0) hF]
  linarith

theorem retained_row_log_budget (η τ : Character) (G V z : O) (U : Ideal O)
    (hU : U≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*U.absNorm*
      (Ideal.span {V}).absNorm)
    (R Z : ℝ) (hZ : 1<Z)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue G)+
        Real.logb Z (U.absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨_,_,_,hz,_,hn,_⟩:=retained_geometry R G V z hne
  have hh:=Real.logb_le_logb_of_le hZ (normValue_pos z hz) (hn.trans (le_max_right 1 _))
  have hb:=retained_log_budget η τ G V z U hU hN R Z hZ hne
  linarith

theorem exists_retained_width_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀hD : Supported D,CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
      ∀Z R:ℝ,1<Z → ∀z:O,
        retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0 →
        0<R ∧ z≠0 ∧ 1≤normValue z ∧
        normValue z≤4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)) ∧
        Real.logb Z (max 1 (4*R/(normValue (commonFrequencyGenerator C D)*
          normValue (nonunitFrequencyGenerator C D U))))+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) ∧
        Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨τ,he,ht,hN⟩:=exists_second_budgeted_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hw
  have hb:=hN hD hCD w hw
  refine ⟨hb,?_⟩
  intro Z R hZ z hz
  have hU : (∏P∈U,P.val)≠0:=Finset.prod_ne_zero_iff.mpr
    (fun P _=>(commonPrime_supported_ideal C D hC P).1)
  obtain ⟨hR,_,_,hne,h1,hrow,_⟩:=retained_geometry R _ _ z hz
  exact ⟨hR,hne,h1,hrow,retained_log_budget η τ _ _ z _ hU hb R Z hZ hz,
    retained_row_log_budget η τ _ _ z _ hU hb R Z hZ hz⟩

theorem fixed_width_cost_eventually (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ:ℝ in Filter.atTop,1<Z ∧ Real.logb Z (4*(fixedFactor:ℝ))≤ε := by
  have he:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (4*(fixedFactor:ℝ))
  filter_upwards [he,Filter.eventually_gt_atTop (1:ℝ)] with Z hF hZ
  refine ⟨hZ,?_⟩
  have hp : (0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hh:=Real.logb_le_logb_of_le hZ (by positivity : 0<4*(fixedFactor:ℝ)) hF
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hh

theorem exists_uniform_retained_width_family (ε : ℝ) (hε : 0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀(η:Character)(χ:RayCharacter)(C D:Ideal O)
      (hC:Supported C)(U:Finset (CommonIndex C D)),
    ∃τ:Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀hD : Supported D,CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
      ∀Z R:ℝ,Z₀≤Z → ∀z:O,
        retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0 →
        0<R ∧ z≠0 ∧ 1≤normValue z ∧
        normValue z≤4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)) ∧
        Real.logb Z (max 1 (4*R/(normValue (commonFrequencyGenerator C D)*
          normValue (nonunitFrequencyGenerator C D U))))+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε ∧
        Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε := by
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.mp (fixed_width_cost_eventually ε hε)
  refine ⟨Z₀,(hZ₀ Z₀ le_rfl).1,?_⟩
  intro η χ C D hC U
  obtain ⟨τ,he,ht,hb⟩:=exists_retained_width_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hw
  obtain ⟨hN,hrow⟩:=hb hD hCD w hw
  refine ⟨hN,?_⟩
  intro Z R hZ z hz
  obtain ⟨hZ1,hcost⟩:=hZ₀ Z hZ
  obtain ⟨hR,hn,h1,hup,hmax,hlog⟩:=hrow Z R hZ1 z hz
  exact ⟨hR,hn,h1,hup,by linarith,by linarith⟩

end SevenEighths.CenteredMomentSecondRetainedWidth

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondSourceMask -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSourceMask
open CanonicalQuadraticSieve CenteredMomentSecondSectorColumns CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask
open CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

theorem divisor_dvd_common (C D a b s : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b)
    (hsI : s∣C*a) (hsJ : s∣D*b) : s∣C ∧ s∣D := by
  have hDa := (coprime_of_same_support C D a hC hD ha hCD).mp hCa
  have hDb := (coprime_of_same_support C D b hC hD hb hCD).mp hCb
  have hsa : IsCoprime s a := ((hDa.symm.mul_right hab).of_isCoprime_of_dvd_right hsJ).symm
  have hsb : IsCoprime s b := ((hCb.symm.mul_right hab.symm).of_isCoprime_of_dvd_right hsI).symm
  exact ⟨hsa.dvd_mul_right_iff.mp hsI,hsb.dvd_mul_right_iff.mp hsJ⟩

variable {ι : Type*} [Fintype ι]

theorem column_nonzero_divisor (S : Finset (Tuple ι)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O)
    (h : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) : s∣I := by
  rw [column_mask] at h
  by_contra hn
  exact h (by rw [ite_eq_right hn,mul_zero])

theorem source_pair_divisor_common (S : Finset (Tuple ι)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b)
    (hleft : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*a)≠0)
    (hright : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (D*b)≠0) : s∣C ∧ s∣D :=
  divisor_dvd_common C D a b s hC hD ha hb hCD hCa hCb hab
    (column_nonzero_divisor S R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s _ hleft)
    (column_nonzero_divisor S R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s _ hright)

end SevenEighths.CenteredMomentSecondSourceMask

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondLiveEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRestrictedSource
open CenteredMomentRestrictedEnergy CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentFirstSectors RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem live_divisor_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R L : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB) (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
      (fun I => (if L∣I then 1 else 0)*f I) W K=
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB) (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K := by
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  rw [maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  ring

theorem actual_second_child_live_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*CanonicalRowCompletion.idealRowHom A I*
        rayCharacter χ (CompletedGauss.primaryGenerator I))
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ L : Ideal O) (t : ℝ)
    (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    let Q := finiteColumns (Fintype.piFinset S)
    let β := finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 Q)
      (divisorCoefficient L (sectorElement C hC.1 Q)
        (movingCoefficient A (sectorElement C hC.1 Q)
          (fun J : sectorPool C hC.1 Q => β (C*J)*heightCoeff η t J)) χ) W K≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff τ t) W K := by
  dsimp only
  rw [sector_child_energy η τ χ A hτ (finiteColumns (Fintype.piFinset S))
    (finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) C hC L t keep W K]
  have he := original_restricted_child_energy S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
    (fun I => (if L∣I then 1 else 0)*heightCoeff τ t I) keep W K hK hW
  simp_rw [live_divisor_energy] at he
  refine le_trans ?_ he
  apply le_of_eq
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs <;> simp_all

end SevenEighths.CenteredMomentSecondLiveEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondSourceCost -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceCost
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRestrictedSource
open CenteredMomentRestrictedEnergy CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentSecondLiveEnergy CenteredMomentRestrictedSourceNormalization
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem source_divisor_common_saving (τ : Character)
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ L : Ideal O) (t : ℝ)
    (Traw : ℝ) (hTraw : 0<Traw) (hP : ∀ i,0<P i)
    (M : ι → ℝ) (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤M i)
    (hM : ∀ i,1≤M i) (a b : ℝ) (ha : 0<a)
    (hslot : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    let Q := finiteColumns (Fintype.piFinset S)
    let β := finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
    sourceRestrictedEnergy keep (residualPool C hC.1 Q)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ t) W K/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*
        (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          ∑ B : actualAllocations S C, (sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff τ t) W K)/CenteredMomentCommonRawScale.remainingRaw B Traw P := by
  dsimp only
  have he := restricted_child_common_saving S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ Traw hTraw hP M hν hWnorm hM a b ha hslot
    (fun I => (if L∣I then 1 else 0)*heightCoeff τ t I) keep W K hK hW
  simp_rw [live_divisor_energy] at he
  refine le_trans ?_ he
  apply le_of_eq
  congr 1
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs <;> simp_all

end SevenEighths.CenteredMomentSecondSourceCost

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondWholeKernel -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondWholeKernel
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentScale CenteredMomentSmooth
open CenteredMomentFirstWholeKernel CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def secondEffectiveScale (C D : Ideal O) (A : O) (K : ℝ) : ℝ :=
  K*‖eisEmbedding A‖^2/((Ideal.absNorm C:ℝ)*(Ideal.absNorm D:ℝ))

theorem secondEffectiveScale_pos (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (A : O) (hA : A≠0) (K : ℝ) (hK : 0<K) : 0<secondEffectiveScale C D A K := by
  apply div_pos (mul_pos hK (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hA))))
  exact mul_pos (CenteredMomentFirstScale.norm_pos C hC) (CenteredMomentFirstScale.norm_pos D hD)

theorem primary_norm_sq (I : Ideal O) (hI : Supported I) :
    ‖eisEmbedding (primaryGenerator I)‖^2=(Ideal.absNorm I:ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,primary_span_supported I hI]

theorem second_kernel_argument (C D a b : Ideal O)
    (hC : Supported C) (hD : Supported D) (ha : Supported a) (hb : Supported b)
    (A h : O) (K : ℝ) :
    K*‖eisEmbedding (A*h)‖^2/
      ‖eisEmbedding (primaryGenerator (C*a)*primaryGenerator (D*b))‖^2=
      secondEffectiveScale C D A K*‖eisEmbedding h‖^2/((Ideal.absNorm a:ℝ)*(Ideal.absNorm b:ℝ)) := by
  simp only [map_mul,norm_mul,mul_pow,primary_norm_sq (C*a) ((supported_mul_iff _ _).mpr ⟨hC,ha⟩),
    primary_norm_sq (D*b) ((supported_mul_iff _ _).mpr ⟨hD,hb⟩),map_mul,Nat.cast_mul,secondEffectiveScale]
  ring

theorem common_normalized_kernel (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (k H a b C D K K₀ H₀ A₀ B₀ : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b)
    (hC : 0<C) (hD : 0<D) (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    (K:ℂ)/((Real.sqrt (C*a):ℂ)*(Real.sqrt (D*b):ℂ))*
      windows V k H a b K₀ H₀ A₀ B₀*paperRadialFourier W (k*H/(a*b))=
      (K:ℂ)/((Real.sqrt C:ℂ)*(Real.sqrt D:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ))*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (k/K₀)) (Real.log (H/H₀)) (Real.log (a/A₀)) (Real.log (b/B₀)) := by
  rw [wholeKernel_actual W V k H a b K₀ H₀ A₀ B₀ hk hH ha hb hK₀ hH₀ hA₀ hB₀]
  rw [Real.sqrt_mul hC.le a,Real.sqrt_mul hD.le b]
  simp only [Complex.ofReal_mul,windows]
  have hc : (Real.sqrt C:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hC).ne'
  have hd : (Real.sqrt D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD).ne'
  have haa : (Real.sqrt A₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA₀).ne'
  have hbb : (Real.sqrt B₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB₀).ne'
  field_simp

theorem second_frequency_whole_kernel (C D a b : Ideal O)
    (hC : Supported C) (hD : Supported D) (ha : Supported a) (hb : Supported b)
    (A h : O) (hA : A≠0) (hh : h≠0) (K : ℝ) (hK : 0<K)
    (F : ℂ) (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    let k := secondEffectiveScale C D A K
    ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*a):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*b):ℝ):ℂ)))*F*
      windows V k (‖eisEmbedding h‖^2) (Ideal.absNorm a:ℝ) (Ideal.absNorm b:ℝ) K₀ H₀ A₀ B₀*
      paperRadialFourier W (K*‖eisEmbedding (A*h)‖^2/
        ‖eisEmbedding (primaryGenerator (C*a)*primaryGenerator (D*b))‖^2)=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*F*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (k/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
          (Real.log ((Ideal.absNorm a:ℝ)/A₀)) (Real.log ((Ideal.absNorm b:ℝ)/B₀)) := by
  dsimp only
  rw [second_kernel_argument C D a b hC hD ha hb]
  simp only [map_mul,Nat.cast_mul]
  have he := common_normalized_kernel W V (secondEffectiveScale C D A K) (‖eisEmbedding h‖^2)
    (Ideal.absNorm a:ℝ) (Ideal.absNorm b:ℝ) (Ideal.absNorm C:ℝ) (Ideal.absNorm D:ℝ)
    K K₀ H₀ A₀ B₀ (secondEffectiveScale_pos C D hC.1 hD.1 A hA K hK)
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))
    (CenteredMomentFirstScale.norm_pos a ha.1) (CenteredMomentFirstScale.norm_pos b hb.1)
    (CenteredMomentFirstScale.norm_pos C hC.1) (CenteredMomentFirstScale.norm_pos D hD.1)
    hK₀ hH₀ hA₀ hB₀
  convert congrArg (fun z : ℂ => F*z) he using 1 <;> ring

end SevenEighths.CenteredMomentSecondWholeKernel

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.LogDyadic -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentLogDyadic
open CenteredMomentSectorLocalization CenteredMomentFirstWholeKernel

def logAnnulus (x : ℝ) : ℂ := annulus (Real.exp x)

theorem logAnnulus_smooth : ContDiff ℝ ∞ logAnnulus :=
  Complex.ofRealCLM.contDiff.comp (annulus_smooth.comp Real.contDiff_exp)

theorem logAnnulus_support : Function.support logAnnulus ⊆ Set.Icc (-Real.log 4) 0 := by
  intro x hx
  have hn : annulus (Real.exp x)≠0 := by simpa only [Function.mem_support,logAnnulus,ne_eq,Complex.ofReal_eq_zero] using hx
  have hlo : 1/4<Real.exp x := lt_of_not_ge (fun h=>hn (annulus_zero_low _ h))
  have hhi : Real.exp x<1 := lt_of_not_ge (fun h=>hn (annulus_zero_high _ h))
  constructor
  · have hh := Real.strictMonoOn_log (show 1/4∈Set.Ioi (0:ℝ) by norm_num)
      (Real.exp_pos x) hlo
    rw [Real.log_exp,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hh
    exact hh.le
  · exact (Real.exp_lt_one_iff.mp hhi).le

theorem logAnnulus_compact : HasCompactSupport logAnnulus :=
  HasCompactSupport.intro (isCompact_Icc) (fun x hx=>by
    by_contra hn
    exact hx (logAnnulus_support hn))

theorem logAnnulus_norm (x : ℝ) : ‖logAnnulus x‖≤1 := by
  rw [logAnnulus,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (annulus_bounds _).1]
  exact (annulus_bounds _).2

theorem logAnnulus_log (q H : ℝ) (hq : 0<q) (hH : 0<H) :
    logAnnulus (Real.log (q/H))=(annulus (q/H):ℂ) := by
  rw [logAnnulus,Real.exp_log (div_pos hq hH)]

theorem actual_dyadic_log_window (n : ℤ) (q : ℝ) (hq : 0<q) :
    (dyadicWeight n q:ℂ)=logAnnulus (Real.log (q/dyadicScale n)) := by
  rw [logAnnulus_log q _ hq (dyadicScale_pos n)];rfl

theorem actual_product_windows (k H a b : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b) (n : Fin 4→ℤ) :
    ((dyadicWeight (n 0) k*dyadicWeight (n 1) H*
      dyadicWeight (n 2) a*dyadicWeight (n 3) b:ℝ):ℂ)=
      windows (fun _=>logAnnulus) k H a b
        (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  simp only [Complex.ofReal_mul,actual_dyadic_log_window (n 0) k hk,
    actual_dyadic_log_window (n 1) H hH,actual_dyadic_log_window (n 2) a ha,
    actual_dyadic_log_window (n 3) b hb,windows]

end SevenEighths.CenteredMomentLogDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondTail -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSupportedCorrelation CenteredMomentSecondWholeKernel
local notation "O" => ActualEisensteinCubic.O

theorem actual_second_kernel_reference (I J : Ideal O) (hI : I≠0) (hJ : J≠0)
    (K X H Tsec : ℝ) (hK : 0<K) (hX : 0<X)
    (hi : (Ideal.absNorm I:ℝ)≤Real.exp H*X) (hj : (Ideal.absNorm J:ℝ)≤Real.exp H*X)
    (hsec : X^2/K≤Tsec) :
    kernelReference Tsec H≤K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
  have hT : 0<Tsec := (div_pos (sq_pos_of_pos hX) hK).trans_le hsec
  have hNi := CenteredMomentFirstScale.norm_pos I hI
  have hNj := CenteredMomentFirstScale.norm_pos J hJ
  have hprod : (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)≤Real.exp (2*H)*X^2 := by
    apply (mul_le_mul hi hj hNj.le (by positivity)).trans_eq
    rw [show 2*H=H+H by ring,Real.exp_add]
    ring
  unfold kernelReference
  apply (le_div_iff₀ (mul_pos hNi hNj)).mpr
  calc
    _ ≤ (Real.exp (-2*H)/Tsec)*(Real.exp (2*H)*X^2) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = X^2/Tsec := by
      rw [show -2*H=-(2*H) by ring,Real.exp_neg]
      field_simp
    _ ≤ K := (div_le_iff₀ hT).mpr (by simpa only [mul_comm] using (div_le_iff₀ hK).mp hsec)

def secondDiscardedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
    ∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
      actualCorrelation (primaryGenerator I) (primaryGenerator J)
        ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) (-h)*
      paperRadialFourier W (K*‖eisEmbedding h‖^2/
        ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2)

theorem second_discarded_pair_bound (Adec : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
        (K X H Tsec Z Csec ξ : ℝ),0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp H*X → (Ideal.absNorm J:ℝ)≤Real.exp H*X →
      X^2/K≤Tsec → (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖secondDiscardedPair I J hI hJ W K Tsec Z ξ‖≤
        K*(Real.exp H*X)^2*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_second_tail Adec
  refine ⟨s,C,hC,?_⟩
  intro W I J hI hJ K X H Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hT : 0<Tsec := (div_pos (sq_pos_of_pos hX) hK).trans_le hsec
  have hb := ht W Tsec Z Csec H ξ (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))
    hT hZ hCs hthreshold (actual_second_kernel_reference I J hI.1 hJ.1 K X H Tsec hK hX hi hj hsec)
    (primaryGenerator I) (primaryGenerator J)
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ)
  have he (h : O) : K*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2=
      (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*normValue h := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq I hI,primary_norm_sq J hJ,normValue_eq_embedding]
    ring
  have hu : normValue (primaryGenerator I)=(Ideal.absNorm I:ℝ) := by rw [normValue,primary_span_supported I hI]
  have hv : normValue (primaryGenerator J)=(Ideal.absNorm J:ℝ) := by rw [normValue,primary_span_supported J hJ]
  rw [hu,hv] at hb
  have hNi : (1:ℝ)≤Ideal.absNorm I := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
  have hNj : (1:ℝ)≤Ideal.absNorm J := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ.1)
  have hroot : 1≤Real.sqrt (Ideal.absNorm I:ℝ)*Real.sqrt (Ideal.absNorm J:ℝ) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr hNi) (Real.one_le_sqrt.mpr hNj)
  have hnorm : ‖(K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))‖≤K := by
    rw [norm_div,norm_mul]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_self hK.le hroot
  unfold secondDiscardedPair
  simp_rw [he]
  rw [norm_mul]
  apply (mul_le_mul hnorm hb (norm_nonneg _) hK.le).trans
  have hprod := mul_le_mul hi hj (Nat.cast_nonneg _) (by positivity : 0≤Real.exp H*X)
  have hfac : 0≤(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec) := by positivity
  have hb' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hfac) hK.le
  convert hb' using 1 <;> ring

end SevenEighths.CenteredMomentSecondTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondWidthDrop -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondWidthDrop
open HeckeFamily CenteredMomentSecondActualWidth CenteredMomentSecondRadicalBudget
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit CenteredMomentCanonicalFirst
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
local notation "O" => HeckeFamily.O

def amplificationIncrement (η:Character) (Z H K M σ:ℝ) : ℝ :=
  max (2*Real.logb Z H-Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-M) 0+σ

def nominalLength (Z H K g:ℝ) : ℝ := 2*Real.logb Z H-Real.logb Z K-g

lemma physical_frequency_scale (Z H K g:ℝ) (hZ:1<Z) (hH:0<H) (hK:0<K) :
    H^2/(K*Z^g)=Z^(nominalLength Z H K g) := by
  have hzg:0<Z^g:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hp:0<H^2/(K*Z^g):=div_pos (sq_pos_of_pos hH) (mul_pos hK hzg)
  have he:Real.logb Z (H^2/(K*Z^g))=nominalLength Z H K g := by
    rw [Real.logb_div (sq_pos_of_pos hH).ne' (mul_pos hK hzg).ne',Real.logb_pow,
      Real.logb_mul hK.ne' hzg.ne',Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)]
    unfold nominalLength
    norm_num
    ring
  rw [←he,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) hp]

lemma actual_nominal_drop (η:Character) (Z H K M σ:ℝ) :
    nominalLength Z H K (amplificationIncrement η Z H K M σ)+
      Real.logb Z (η.modulus.absNorm:ℝ)≤M-σ := by
  have hh:=le_max_left (2*Real.logb Z H-Real.logb Z K+
    Real.logb Z (η.modulus.absNorm:ℝ)-M) 0
  unfold nominalLength amplificationIncrement
  linarith

theorem exists_physical_width_family (η:Character) (χ:RayCharacter)
    (C D:Ideal O) (hC:Supported C) (U:Finset (CommonIndex C D)) :
    ∃τ:Character,
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        CanonicalRowCompletion.idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD:Supported D),CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      ∀Z H K Tsec Csec ξ M σ g:ℝ,1<Z → 0<H → 0<K → 0<Csec →
      amplificationIncrement η Z H K M σ≤g →
      Tsec≤Csec*(H^2/(K*Z^g)) →
      ∀h:O,retainedWeight (frequencyRadius Tsec Z ξ)
        (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h))≠0 →
      max 0 (nominalLength Z H K g-
        Real.logb Z (normValue (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))+
        frequencyLoss Z Csec ξ)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          M-σ+Real.logb Z (fixedFactor:ℝ)+frequencyLoss Z Csec ξ := by
  obtain ⟨τ,hτ,hw⟩:=exists_actual_width_family η χ C D hC U
  refine ⟨τ,hτ,?_⟩
  intro hD hCD w hn Z H K Tsec Csec ξ M σ g hZ hH hK hCs hg hscale h hret
  apply hw hD hCD w hn Z Tsec Csec (nominalLength Z H K g) ξ M σ hZ hCs
  · rwa [←physical_frequency_scale Z H K g hZ hH hK]
  · have hh:=actual_nominal_drop η Z H K M σ
    unfold nominalLength at hh ⊢
    linarith
  · exact hret

end SevenEighths.CenteredMomentSecondWidthDrop

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondWindowSource -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedSource
open CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentConjugateWindow
local notation "O" => ActualEisensteinCubic.O

theorem sector_window_from_source (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (keep : O→Prop) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ→ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀ z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀ v : ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) Φ H≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  have he (v : ℝ) := funext (sector_divisor_coefficient η τ χ A hτ S β C hC L v)
  simp_rw [sector_divisor_coefficient η τ χ A hτ S β C hC L t]
  have hh := restricted_window_energy_from_height keep V hVc hVs J Finset.univ
    (sectorElement C hC.1 S) (sectorElement_supported C hC.1 S)
    (fun I : sectorPool C hC.1 S=>if L∣(I:Ideal O) then β (C*I) else 0)
    τ t θ X hX Φ H hH hΦ E hE ?_
  · simpa only [sectorElement_span] using hh
  intro v
  have hs := hsource v
  rw [←sector_child_energy η τ χ A hτ S β C hC L v keep Φ H,he v] at hs
  simpa only [sectorElement_span] using hs

theorem star_logAnnulus (x : ℝ) : star (logAnnulus x)=logAnnulus x := by
  simp only [logAnnulus,Complex.star_def,Complex.conj_ofReal]

theorem star_logAnnulus_column (u t : ℝ) :
    star (columnPhase logAnnulus u t)=columnPhase logAnnulus u (-t) := by
  rw [star_columnPhase]
  simp only [star_logAnnulus]

theorem sector_conjugate_window_from_source (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (keep : O→Prop) (t θ X : ℝ) (hX : 0<X) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀ z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀ v : ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ)) Φ H≤
      (E*heightCost t (-θ)^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*
        ‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖)^2 := by
  simp only [star_logAnnulus_column]
  exact sector_window_from_source η τ χ A hτ S β C hC L keep t (-θ) X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth J Φ H hH hΦ E hE hsource

end SevenEighths.CenteredMomentSecondWindowSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondReducedEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondReducedEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedSource CenteredMomentChildAssembly
open CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion CenteredMomentLogDyadic
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondWindowSource
local notation "O" => ActualEisensteinCubic.O

theorem masked_source_energy (η τ τr : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (hCD : primeSupport C=primeSupport D)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
          rayCharacter χ (primaryGenerator I))
    (hτr : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τr t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O)
    (keep : O→Prop) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ t) Φ H=
    sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τr t) Φ H := by
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs with hi
  · have hI : Supported (I:Ideal O) := (Finset.mem_filter.mp I.property).2
    rw [hτ I hI t,hτr I hI t,residual_sixth_coefficient C D hC hCD U I hI hi.1]
  · simp only [zero_mul]

theorem original_window_from_reduced_source (η τr : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (_hD : Supported D)
    (hCD : primeSupport C=primeSupport D)
    (U : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
    (hτr : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τr t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (keep : O→Prop)
    (t θ X : ℝ) (hX : 0<X) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀ v : ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τr v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
          (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) Φ H≤
      (E*heightCost t θ^(2*J))*(∫w:ℝ,(1+‖w‖)^J*
        ‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖)^2 := by
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 := by
    rw [fixed_sixth_factorization]
    exact mul_ne_zero (reducedNumerator_ne_zero C D hC U) (pow_ne_zero _ (sixthFactor_ne_zero C D hC U))
  obtain ⟨τ,hN,hτ⟩ := exists_second_family η χ _ hA
  apply sector_window_from_source η τ χ _ hτ S β C hC L keep t θ X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth J Φ H hH hΦ E hE
  intro v
  rw [masked_source_energy η τ τr χ C D hC hCD U hτ hτr S β L keep v Φ H]
  exact hsource v

end SevenEighths.CenteredMomentSecondReducedEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondMaskedWindow -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondMaskedWindow
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedSource
open CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentRowNorm CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

theorem masked_divisor_coefficient (η τ : Character) (χ : RayCharacter) (A : O)
    (C : Ideal O) (hC : Supported C)
    (hτ : ∀I:Ideal O,Supported I → IsCoprime C I → ∀t:ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (t : ℝ)
    (I : sectorPool C hC.1 S) :
    divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient A (sectorElement C hC.1 S)
        (fun J:sectorPool C hC.1 S=>β (C*J)*heightCoeff η t J)) χ I=
      (if L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I := by
  have hi : IsCoprime C (I:Ideal O) := (Finset.mem_filter.mp I.property).2
  rw [divisorCoefficient,movingCoefficient,sectorElement_span,
    hτ I (sectorPool_supported C hC.1 S I) hi t]
  dsimp only [sectorElement]
  split_ifs <;> ring

theorem masked_child_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (C : Ideal O) (hC : Supported C)
    (hτ : ∀I:Ideal O,Supported I → IsCoprime C I → ∀t:ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (t : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J:sectorPool C hC.1 S=>β (C*J)*heightCoeff η t J)) χ) Φ H=
    sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ t) Φ H := by
  have he := funext (masked_divisor_coefficient η τ χ A C hC hτ S β L t)
  rw [he]
  unfold restrictedEnergy sourceRestrictedEnergy
  apply tsum_congr
  intro z
  rw [sector_rowPolynomial S (fun I=>(if L∣I then β (C*I) else 0)*heightCoeff τ t I) C hC z]
  have hc : (fun I : supportedColumns (residualPool C hC.1 S)=>
      if IsCoprime C (I:Ideal O) then (if L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I else 0)=
      (fun I : supportedColumns (residualPool C hC.1 S)=>
        (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then β (C*I) else 0)*heightCoeff τ t I) := by
    funext I
    split_ifs <;> simp_all
  rw [hc]

theorem original_window_from_masked_source (η τ : Character) (χ : RayCharacter) (A : O)
    (C : Ideal O) (hC : Supported C)
    (hτ : ∀I:Ideal O,Supported I → IsCoprime C I → ∀t:ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (keep : O→Prop)
    (t θ X : ℝ) (hX : 0<X) (J : ℕ)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (E : ℝ) (hE : 0≤E)
    (hsource : ∀v:ℝ,sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
      (heightCoeff τ v) Φ H≤E*(1+‖v‖)^(2*J)) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) Φ H≤
      (E*heightCost t θ^(2*J))*(∫w:ℝ,(1+‖w‖)^J*
        ‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖)^2 := by
  have hc := funext (masked_divisor_coefficient η τ χ A C hC hτ S β L t)
  change restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
    (fun I=>(divisorCoefficient L (sectorElement C hC.1 S)
      (movingCoefficient A (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ) I*_) Φ H≤_
  rw [hc]
  have hh := restricted_window_energy_from_height keep logAnnulus logAnnulus_compact logAnnulus_smooth J
    Finset.univ (sectorElement C hC.1 S) (sectorElement_supported C hC.1 S)
    (fun I:sectorPool C hC.1 S=>if L∣(I:Ideal O) then β (C*I) else 0)
    τ t θ X hX Φ H hH hΦ E hE ?_
  · simpa only [sectorElement_span] using hh
  intro v
  have hs := hsource v
  rw [←masked_child_energy η τ χ A C hC hτ S β L v keep Φ H] at hs
  rw [funext (masked_divisor_coefficient η τ χ A C hC hτ S β L v)] at hs
  simpa only [sectorElement_span] using hs

end SevenEighths.CenteredMomentSecondMaskedWindow

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowBudget
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentSecondWindowSource

def profileMoment (J : ℕ) : ℝ :=
  ∫ w : ℝ,(1+‖w‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖

theorem profileMoment_nonneg (J : ℕ) : 0≤profileMoment J :=
  integral_nonneg (fun w=>by positivity)

def heightEnvelope (t : ℝ) : ℝ := (1+‖t‖+2*Real.pi)*(1+2*Real.pi)

theorem heightEnvelope_pos (t : ℝ) : 0<heightEnvelope t := by unfold heightEnvelope;positivity

theorem heightCost_le_envelope (t θ : ℝ) : heightCost t θ≤heightEnvelope t*(1+‖θ‖) := by
  have hh : 1+‖t‖+2*Real.pi*‖θ‖≤(1+‖t‖+2*Real.pi)*(1+‖θ‖) := by
    nlinarith [norm_nonneg t,norm_nonneg θ,Real.pi_pos]
  have he := mul_le_mul_of_nonneg_right hh (show 0≤1+2*Real.pi by positivity)
  convert he using 1 <;> simp only [heightCost,heightEnvelope] ; ring

def windowBudget (J : ℕ) (t E : ℝ) : ℝ := Real.sqrt E*heightEnvelope t^J*profileMoment J

theorem windowBudget_nonneg (J : ℕ) (t E : ℝ) : 0≤windowBudget J t E :=
  mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (heightEnvelope_pos _).le _))
    (profileMoment_nonneg _)

theorem shifted_window_budget (J : ℕ) (t θ E : ℝ) (hE : 0≤E) :
    (E*heightCost t θ^(2*J))*profileMoment J^2≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  calc
    _ ≤ E*(heightEnvelope t*(1+‖θ‖))^(2*J)*profileMoment J^2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (heightCost_pos _ _).le (heightCost_le_envelope t θ) _) hE)
        (sq_nonneg _)
    _ = _ := by
      rw [show 2*J=J*2 by omega,pow_mul]
      simp only [windowBudget,mul_pow,Real.sq_sqrt hE]
      ring

theorem conjugate_shifted_window_budget (J : ℕ) (t θ E : ℝ) (hE : 0≤E) :
    (E*heightCost t (-θ)^(2*J))*profileMoment J^2≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  simpa only [norm_neg] using shifted_window_budget J t (-θ) E hE

end SevenEighths.CenteredMomentSecondWindowBudget

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRectangleEnergy
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedDomain CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSourceRectangle
open CenteredMomentSourceRectangleMask CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentDivisorRowEnergy CenteredMomentDivisorRetained
local notation "O" => ActualEisensteinCubic.O

theorem height_source_row (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S=>β I*heightCoeff η t I) z=
      ∑ I∈S,β I*rowWeight η fixedBadMask 1 z t I := by
  rw [source_rowPolynomial S (fun I=>β I*heightCoeff η t I) z]
  calc
    _ = ∑ I∈supportedColumns S,β I*rowWeight η fixedBadMask 1 z t I := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [heightCoeff_eq_fixed_rowWeight η t I (Finset.mem_filter.mp hI).2,
        rowWeight_split η fixedBadMask 1 z t I]
      ring
    _ = _ := Finset.sum_filter_of_ne (fun I hI hn => by
      by_contra hs
      apply hn
      rw [rowWeight_zero_of_not_supported η fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) I hs,mul_zero])

theorem source_restricted_energy_eq_rectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (t : ℝ) (keep : O→Prop)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (tuplePool slots S₁ S₂))
      (finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L))
      (heightCoeff η t) W K=
      ∑' z : O,if keep z then
        ‖maskedRectangle η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
          (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2*
        (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0 := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_congr
  intro z
  rw [height_source_row]
  rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    η fixedBadMask 1 z t (dvd_mul_right _ _) (dvd_mul_left _ _)
    slots S₁ S₂ R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂]

end SevenEighths.CenteredMomentSourceRectangleEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ActiveSourceRetained -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentActiveSourceRetained
open CenteredMomentActiveAllocation HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_active_retained (N : ℕ) (hslots : Fintype.card ι≤N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
      ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
      ∀ (rows : Finset O) (ω : O→ℝ),(∀ z∈rows,0≤ω z) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      (∑ z∈rows,ω z*‖(Real.sqrt (raw*∏ i,P i):ℂ)⁻¹*
        rowPolynomial Finset.univ (sourceGenerator Q)
          (fun I : supportedColumns Q=>β I*heightCoeff η t I) z‖^2)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a ∈ activeAllocations η (fixedBadMask*idealGenerator R) 1 t slots coeff L W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂) (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑ z∈rows,ω z*
            (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩ := active_raw_to_retained_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hX hY hcov₁ hcov₂ rows ω hω
  dsimp only
  simp_rw [height_source_row]
  simp_rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    η fixedBadMask 1 _ t (dvd_mul_right _ _) (dvd_mul_left _ _)
    slots S₁ S₂ R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hcov₁ hcov₂]
  have hb₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hb₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  obtain ⟨hx,hy⟩ := pullback_same_product X₁ X₂ Y₁ Y₂ T B₁ B₂ hX hY
  exact hbound η (fixedBadMask*idealGenerator R) 1 t slots hp
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) M P hM hP hcoeff L hL
    W₁ W₂ b₁ b₂ _ _ _ _ _ hs₁ hs₂
    (div_pos hX₁ hb₁) (div_pos hX₂ hb₂) (div_pos hY₁ hb₁) (div_pos hY₂ hb₂)
    hx hy rows ω hω

end SevenEighths.CenteredMomentActiveSourceRetained

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ActiveSmoothedSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentActiveSmoothedSource
open CenteredMomentActiveAllocation HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentPositiveSummability
open CenteredMomentActiveSourceRetained
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_active_smoothed (N : ℕ) (hslots : Fintype.card ι≤N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
      ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
      ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0<K →
      (∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a ∈ activeAllocations η (fixedBadMask*idealGenerator R) 1 t slots coeff L W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂) (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑' z:O,(if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)*
            (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩:=source_plain_to_active_retained (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  dsimp only
  let Q:=finiteColumns (tuplePool slots S₁ S₂)
  let β:=finiteColumnCoefficient (tuplePool slots S₁ S₂)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
  let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
  let coeff:=fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
  let ω:=fun z:O=>if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hω (z:O):0≤ω z:=by dsimp only [ω];split_ifs;exact hΦ z;exact le_rfl
  have hbn (B:Ideal O) (hB:B≠0):(0:ℝ)<Ideal.absNorm B:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hraw:0< raw:=div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have htotal:0< raw*∏i,P i:=mul_pos hraw (Finset.prod_pos (fun i _=>hP i))
  change sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤_
  unfold sourceRestrictedEnergy restrictedEnergy
  rw [←tsum_div_const]
  have he (z:O):
      (if keep z then ‖rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)/(raw*∏i,P i)=
      ω z*‖(Real.sqrt (raw*∏i,P i):ℂ)⁻¹*rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2 := by
    rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ htotal]
    dsimp only [ω]
    split_ifs <;> ring
  simp_rw [he]
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (hω z) (sq_nonneg _))
  intro rows
  have hh:=hbound η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂
    rows ω (fun z _=>hω z)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  have hf:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hP i))
  have hfac:0≤(2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P:=by
    apply div_nonneg _ hf.le
    exact mul_nonneg (by positivity) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left ?_ hfac
  have hX:=allocated_positive_summable η (fixedBadMask*idealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hX₁ (hbn B₁ hB₁)) (div_pos hX₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hY:=allocated_positive_summable η (fixedBadMask*idealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hY₁ (hbn B₁ hB₁)) (div_pos hY₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hs:Summable (fun z:O=>ω z*
    (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
     ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)):=by
    convert hX.add hY using 1
    funext z
    dsimp only [ω]
    split_ifs <;> ring
  exact sum_le_hasSum rows (fun z _=>mul_nonneg (hω z) (add_nonneg (sq_nonneg _) (sq_nonneg _))) hs.hasSum
end SevenEighths.CenteredMomentActiveSmoothedSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RadialSourceDictionary -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentRadialSourceDictionary
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

 theorem actual_source_energy {ι:Type*} [Fintype ι] [DecidableEq ι]
    (s:Data ι) (r:Radial) (S₁ S₂:Finset (Ideal O)) (R L B₁ B₂:Ideal O)
    (X₁ X₂ Y₁ Y₂:ℝ)
    (hm:s.m=fixedBadMask*idealGenerator R) (hA:s.A=1)
    (hX₁:s.X₁=X₁/Ideal.absNorm B₁) (hX₂:s.X₂=X₂/Ideal.absNorm B₂)
    (hY₁:s.Y₁=Y₁/Ideal.absNorm B₁) (hY₂:s.Y₂=Y₂/Ideal.absNorm B₂)
    (hcov₁:PlainCoverage S₁ s.W₁ B₁ X₁ Y₁) (hcov₂:PlainCoverage S₂ s.W₂ B₂ X₂ Y₂) :
    sourceRestrictedEnergy r.keep (finiteColumns (tuplePool s.slots S₁ S₂))
      (finiteColumnCoefficient (tuplePool s.slots S₁ S₂)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L))
      (heightCoeff s.η s.t) r.profile r.scale/(s.X₁*s.X₂*∏i,s.P i)=energy s r L := by
  rw [source_restricted_energy_eq_rectangle s.η s.t r.keep s.slots S₁ S₂ R L
    s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hcov₁ hcov₂ r.profile r.scale]
  unfold energy
  rw [←tsum_div_const]
  apply tsum_congr
  intro z
  have ht:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
  have hc:s.coefficient=(fun i I=>s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)):=rfl
  rw [hc]
  dsimp only [Radial.weight]
  rw [hm,hA,hX₁,hX₂,hY₁,hY₂]
  split_ifs <;> ring

end SevenEighths.CenteredMomentRadialSourceDictionary

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceAbsoluteEnvelope -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSourceAbsoluteEnvelope
open HeckeFamily CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentSourceRectangleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeHeight CenteredMomentPositiveSummability
open CenteredMomentAbsoluteEnergy QuadraticInitialBound ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

 theorem actual_source_absolute (Q:Finset (Ideal O)) (c:Ideal O→ℂ) (η:Character) (t:ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    sourceRestrictedEnergy keep Q c (heightCoeff η t) Φ K≤
      diagonalControl Φ*max 1 K*(∑I∈Q,‖c I‖)^2 := by
  let F:O→ℂ:=fun z=>rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I:supportedColumns Q=>c I*heightCoeff η t I) z
  let B:ℝ:=∑I∈Q,‖c I‖
  have hB:0≤B:=Finset.sum_nonneg (fun I _=>norm_nonneg _)
  have hF (z:O):‖F z‖≤B:=by
    change ‖rowPolynomial Finset.univ (sourceGenerator Q) (fun I:supportedColumns Q=>c I*heightCoeff η t I) z‖≤∑I∈Q,‖c I‖
    rw [height_source_row η t Q c z]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg (c I)) (rowWeight_norm_le_one_all η CenteredMomentSecondHeightFamily.fixedBadMask 1 z t I)
  have hs:=bounded_radial_summable F B hF keep Φ K hK
  have hh:=hs.tsum_le_tsum (g:=fun z:O=>B^2*‖Φ (‖eisEmbedding z‖^2/K)‖) (fun z=>by
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hF z) 2) (norm_nonneg _))
    · positivity) ((radial_norm_summable Φ K hK).mul_left (B^2))
  rw [tsum_mul_left] at hh
  apply hh.trans
  exact (mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) (sq_nonneg B)).trans_eq (by ring)

end SevenEighths.CenteredMomentSourceAbsoluteEnvelope

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceRetainedEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceRetainedEnergy
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_retained (N : ℕ) (hslots : Fintype.card ι≤N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
      ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
      ∀ (rows : Finset O) (ω : O→ℝ),(∀ z∈rows,0≤ω z) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      (∑ z∈rows,ω z*‖(Real.sqrt (raw*∏ i,P i):ℂ)⁻¹*
        rowPolynomial Finset.univ (sourceGenerator Q)
          (fun I : supportedColumns Q=>β I*heightCoeff η t I) z‖^2)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a : Allocation L (Finset.univ : Finset (ι⊕Fin 2)),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑ z∈rows,ω z*
            (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩ := masked_raw_to_retained_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hX hY hcov₁ hcov₂ rows ω hω
  dsimp only
  simp_rw [height_source_row]
  simp_rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    η fixedBadMask 1 _ t (dvd_mul_right _ _) (dvd_mul_left _ _)
    slots S₁ S₂ R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hcov₁ hcov₂]
  have hb₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hb₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  obtain ⟨hx,hy⟩ := pullback_same_product X₁ X₂ Y₁ Y₂ T B₁ B₂ hX hY
  exact hbound η (fixedBadMask*idealGenerator R) 1 t slots hp
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) M P hM hP hcoeff L hL
    W₁ W₂ b₁ b₂ _ _ _ _ _ hs₁ hs₂
    (div_pos hX₁ hb₁) (div_pos hX₂ hb₂) (div_pos hY₁ hb₁) (div_pos hY₂ hb₂)
    hx hy rows ω hω

end SevenEighths.CenteredMomentSourceRetainedEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SmoothedRetainedSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSmoothedRetainedSource
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentPositiveSummability
open CenteredMomentSourceRetainedEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_to_smoothed_retained (N : ℕ) (hslots : Fintype.card ι≤N)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
      ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
      ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0<K →
      (∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      let coeff := fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      C*(Ideal.absNorm L:ℝ)^ε*
        ∑ a : Allocation L (Finset.univ : Finset (ι⊕Fin 2)),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
          ∑' z:O,(if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)*
            (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
             ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
              (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2) := by
  obtain ⟨C,hC,hbound⟩:=source_plain_to_retained (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  dsimp only
  let Q:=finiteColumns (tuplePool slots S₁ S₂)
  let β:=finiteColumnCoefficient (tuplePool slots S₁ S₂)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
  let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
  let coeff:=fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)
  let ω:=fun z:O=>if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hω (z:O):0≤ω z:=by dsimp only [ω];split_ifs;exact hΦ z;exact le_rfl
  have hbn (B:Ideal O) (hB:B≠0):(0:ℝ)<Ideal.absNorm B:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hraw:0< raw:=div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have htotal:0< raw*∏i,P i:=mul_pos hraw (Finset.prod_pos (fun i _=>hP i))
  change sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤_
  unfold sourceRestrictedEnergy restrictedEnergy
  rw [←tsum_div_const]
  have he (z:O):
      (if keep z then ‖rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)/(raw*∏i,P i)=
      ω z*‖(Real.sqrt (raw*∏i,P i):ℂ)⁻¹*rowPolynomial Finset.univ (sourceGenerator Q)
        (fun I:supportedColumns Q=>β I*heightCoeff η t I) z‖^2 := by
    rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ htotal]
    dsimp only [ω]
    split_ifs <;> ring
  simp_rw [he]
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (hω z) (sq_nonneg _))
  intro rows
  have hh:=hbound η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂
    rows ω (fun z _=>hω z)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  have hf:0<formalReductionFactor L a P:=mul_pos (selectedNorm_pos L a)
    (Finset.prod_pos (fun i _=>hP i))
  have hfac:0≤(2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P:=by
    apply div_nonneg _ hf.le
    exact mul_nonneg (by positivity) (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left ?_ hfac
  have hX:=allocated_positive_summable η (fixedBadMask*idealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hX₁ (hbn B₁ hB₁)) (div_pos hX₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hY:=allocated_positive_summable η (fixedBadMask*idealGenerator R) 1 t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hY₁ (hbn B₁ hB₁)) (div_pos hY₂ (hbn B₂ hB₂)) slots coeff P L a keep Φ K hK
  have hs:Summable (fun z:O=>ω z*
    (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
     ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots coeff P L a W₁ W₂
      (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)):=by
    convert hX.add hY using 1
    funext z
    dsimp only [ω]
    split_ifs <;> ring
  exact sum_le_hasSum rows (fun z _=>mul_nonneg (hω z) (add_nonneg (sq_nonneg _) (sq_nonneg _))) hs.hasSum
end SevenEighths.CenteredMomentSmoothedRetainedSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CanonicalRetainedSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalRetainedSource
open CanonicalQuadraticSieve CenteredMomentFirstSectors
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentCommonRawScale CenteredMomentRestrictedSourceNormalization
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveChildren (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑ a : Allocation L (Finset.univ : Finset (ι⊕Fin 2)),
    ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
      ∑' z:O,(if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)*
        (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
         ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)

theorem positiveChildren_nonneg (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (hP : ∀ i,0<P i) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg
  · apply div_nonneg
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=>hP i))).le
  · apply tsum_nonneg
    intro z
    apply mul_nonneg
    · split_ifs;exact hΦ z;exact le_rfl
    · exact add_nonneg (sq_nonneg _) (sq_nonneg _)

def SmoothedBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
    ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
    ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
    ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
    ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0<K →
      (∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      D*(Ideal.absNorm L:ℝ)^ε*
        positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_smoothed_bound (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ J:Finset ι,SmoothedBound J D ε := by
  have hex (J:Finset ι) : ∃ D:ℝ,0<D ∧ SmoothedBound J D ε := by
    simpa only [SmoothedBound,positiveChildren] using
      CenteredMomentSmoothedRetainedSource.source_plain_to_smoothed_retained
        (ι:=J) (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose D hD hbound using hex
  let C:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hC:0<C:=by dsimp [C];linarith
  have hDC (J:Finset ι):D J≤C:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  have hh:=hbound J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hDC J) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (positiveChildren_nonneg η t slots R L ν Wslot P M hP W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K hΦ))

omit [DecidableEq ι] in

theorem live_residual_pool (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ j,B j≠0) (i : liveIndices B) :
    residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val))=S (Sum.inl i.val) := by
  ext I
  rw [mem_residualPool,(Finset.mem_filter.mp i.property).2,one_mul]

omit [DecidableEq ι] in
theorem liveBox_original_pools (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ j,B j≠0) :
    liveBox S B hB=tuplePool (fun i:liveIndices B=>S (Sum.inl i.val))
      (residualPool (B (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
      (residualPool (B (Sum.inr 1)) (hB _) (S (Sum.inr 1))) := by
  rw [liveBox_eq_tuplePool]
  simp_rw [live_residual_pool]

def commonPositiveChildren (τ : Character) (t : ℝ)
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι) (C R L : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  positiveChildren τ t (fun i:liveIndices B=>S (Sum.inl i.val)) (R*C) L
    (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) (fun i=>M i.val)
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) keep Φ K

local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤M i) → (∀ i,1≤M i) →
      ∀ (a b : ℝ),0<a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  obtain ⟨D,hD,hbound⟩:=uniform_smoothed_bound (ι:=ι) ε hε
  refine ⟨D,hD,?_⟩
  intro τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  dsimp only
  have hbn (I:Ideal O) (hI:I≠0):(0:ℝ)<Ideal.absNorm I:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hraw:0<T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂):=
    div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have hcommon:=CenteredMomentSecondSourceCost.source_divisor_common_saving τ S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L t _ hraw hP M hν hWnorm hM a b ha hslot keep Φ K hK hΦ
  dsimp only at hcommon
  refine hcommon.trans ?_
  let pref:ℝ:=((actualAllocations S C).card:ℝ)*
    (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))
  have hpref:0≤pref:=by dsimp [pref];positivity
  change pref*_≤pref*D*(Ideal.absNorm L:ℝ)^ε*_
  calc
    _ ≤ pref*∑ B:actualAllocations S C,
      D*(Ideal.absNorm L:ℝ)^ε*commonPositiveChildren τ t S B C R L ν Wslot P M
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
      apply mul_le_mul_of_nonneg_left ?_ hpref
      apply Finset.sum_le_sum
      intro B _
      have hB:= (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
      have hcoeff (i:liveIndices (B:Tuple ι)) (I:Ideal O) :
          ‖ν i.val I*Wslot i.val ((Ideal.absNorm I:ℝ)/P i.val)‖≤M i.val := by
        rw [norm_mul]
        calc
          _ ≤ 1*M i.val := mul_le_mul (hν _ _) (hWnorm _ _) (norm_nonneg _) (by norm_num)
          _ = _ := one_mul _
      have hh:=hbound (liveIndices (B:Tuple ι)) τ t
        (fun i:liveIndices (B:Tuple ι)=>S (Sum.inl i.val))
        (fun i I hI=>hp i.val I hI)
        (residualPool (B.val (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
        (residualPool (B.val (Sum.inr 1)) (hB _) (S (Sum.inr 1)))
        (R*C) L hL (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) (fun i=>M i.val)
        (fun i=>hP i.val) (fun i=>(hM i.val).trans' zero_le_one) (fun i I _=>hcoeff i I)
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1))
        (mul_ne_zero hB₁ (hB _)) (mul_ne_zero hB₂ (hB _)) hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT
        (plainCoverage_residualPool _ W₁ B₁ _ (hB _) X₁ Y₁ hcov₁)
        (plainCoverage_residualPool _ W₂ B₂ _ (hB _) X₂ Y₂ hcov₂) keep Φ K hK hΦ
      dsimp only at hh
      rw [remainingRaw_source B hB B₁ B₂ hB₁ hB₂ T P,liveBox_original_pools]
      exact hh
    _ = _ := by rw [←Finset.mul_sum];ring

def CanonicalBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤M i) → (∀ i,1≤M i) →
      ∀ (a b : ℝ),0<a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ J:Finset ι,CanonicalBound J D ε := by
  have hex (J:Finset ι):∃ D:ℝ,0<D ∧ CanonicalBound J D ε:=by
    simpa only [CanonicalBound] using canonical_source_to_positive (ι:=J) ε hε
  choose D hD hbound using hex
  let E:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hE:0<E:=by dsimp [E];linarith
  have hDE (J:Finset ι):D J≤E:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [E];linarith
  refine ⟨E,hE,?_⟩
  intro J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  have hh:=hbound J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  refine hh.trans ?_
  have hsum:0≤∑ B:actualAllocations S C,
      commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
        b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K:=by
    apply Finset.sum_nonneg
    intro B _
    exact positiveChildren_nonneg (ι:=liveIndices (B.val : Tuple J)) τ t
      (fun i=>S (Sum.inl i.val)) (R*C) L (fun i=>ν i.val) (fun i=>Wslot i.val)
      (fun i=>P i.val) (fun i=>M i.val) (fun i=>hP i.val)
      W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1)) keep Φ K hΦ
  apply mul_le_mul_of_nonneg_right ?_ hsum
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply mul_le_mul_of_nonneg_left (hDE J)
  positivity

end SevenEighths.CenteredMomentCanonicalRetainedSource

end

end OAI

end

