module

public import Green64.Library.Analysis.NumberTheory.DirichletL.QuadraticSieve.Part003

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / CubicSieve / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.FirstCoreCutoff -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def firstCoreSecondCutoff {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : Finset ι) (X Y A H : ℝ) (G E : Finset ι) : Finset O :=
  secondFrequencyCutoff
    (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 *
      (((X / primeProductNorm p D) / primeProductNorm p G) * Real.exp A)^2)) H

theorem firstCoreSecondCutoff_zero {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : Finset ι) (X Y A H : ℝ) (G E : Finset ι) :
    (0 : O) ∈ firstCoreSecondCutoff p D X Y A H G E :=
  secondFrequencyCutoff_zero _ _

theorem firstCoreSecondCutoff_uniform {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t A : ℝ)
    (hgA : ∀ s, g s ≠ 0 → |s| ≤ A)
    (D G E S T : Finset ι) (hGS : Disjoint G S) (hGT : Disjoint G T) (hST : Disjoint S T)
    (X Y H : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (hS : normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A)) (G∪S) ≠ 0)
    (hT : normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A)) (G∪T) ≠ 0)
    (k : O) (hk : k ∉ firstCoreSecondCutoff p D X Y A H G E) :
    H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
      ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2 := by
  have hXD : 0 < X / primeProductNorm p D := div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp D)
  have hXG : 0 < (X / primeProductNorm p D) / primeProductNorm p G :=
    div_pos hXD (FirstPassCubeLabels.primeProductNorm_pos p hp G)
  have hSup (S : Finset ι) (hGS : Disjoint G S)
      (hS : normalizedColumn p (fun A => firstCoreModeProfile g V negative t
        (columnLog p (X / primeProductNorm p D) A)) (G∪S) ≠ 0) :
      columnLog p ((X / primeProductNorm p D) / primeProductNorm p G) S ≤ A := by
    have hs : firstCoreModeProfile g V negative t (columnLog p (X / primeProductNorm p D) (G∪S)) ≠ 0 := by
      intro hz
      apply hS
      simp only [normalizedColumn, hz, zero_div]
    have ha := hgA _ (firstCoreModeProfile_support g V negative t _ hs).1
    rw [SecondPassIntegration.columnLog_extract_common p hp G S hGS _ hXD] at ha
    exact le_trans (le_abs_self _) ha
  exact secondFrequencyCutoff_uniform p hp ((X / primeProductNorm p D) / primeProductNorm p G)
    Y A H hXG hY (primeSubsetGenerator (fun i => Ideal.span {p i}) E)
    (primeSubsetGenerator_ne_zero _ _) S T hST (hSup S hGS hS) (hSup T hGT hT) k hk

theorem first_second_normalization_factor {ι : Type*}
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (D : Finset ι) (X Y R : ℝ) (hX : 0 < X) :
    (primeProductNorm p D)⁻¹ * (Y * R / (X / primeProductNorm p D)^2) =
      Y * primeProductNorm p D * R / X^2 := by
  have hn := (FirstPassCubeLabels.primeProductNorm_pos p hp D).ne'
  have hx := hX.ne'
  field_simp

end
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (halfNormalizationCLM halfNormalizationCLM_apply halfNormalization_twist
  frequencyTwist frequencyTwist_apply outerWindow tripleCoefficient)
open SecondPassIntegration (childGeometricMean)

theorem normalized_twisted_second_sector_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ t, g₁ t ≠ 0 → U t = 1)
    (hU₂ : ∀ t, g₂ t ≠ 0 → U t = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ D₀ E₀ V₀ X₀ K₀ Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X₀ → 0 < K₀ → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ t₁ t₂ t₃ : ℝ,
        (1+Y*K₀/(D₀*E₀^2*V₀^2*X₀^2))^decayOrder * ‖(𝓕 (frequencyTwist A₁ (-θ₁))) t₁*(𝓕 (frequencyTwist A₂ θ₂)) t₂*b t₃‖ ≤
          Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*firstLogDensity J t₁*firstLogDensity J t₂*firstLogDensity J t₃) ∧
      ∀ (B C D R F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (s : Finset (SecondExpansionData ι))
        (T : Finset (Ideal O × O)) (X lengthScale : ℝ),
        s ⊆ secondExpansionSector F (fun G E => (K G E).erase 0) R →
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ lengthScale →
        (∀ x ∈ s, |secondSectorZ p
          (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
            (expansionSupportData C D x)) X₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
          secondSupportRow p (expansionSupportData C D x)) ∈ T) →
        (∀ t ∈ T, t.1 ≠ ⊥) → (∀ t ∈ T, (Ideal.absNorm t.1 : ℝ) ≤ lengthScale) →
        ‖secondExpansionSource p hp hcop hg F Ψ m
          (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
            jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) z s
          (fun S => normalizedColumn p (fun A => (frequencyTwist g₁ θ₁) (columnLog p X A)) S)
          (fun S => normalizedColumn p (fun A => (frequencyTwist g₂ θ₂) (columnLog p X A)) S) W Y‖ ≤
        (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
            X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 (frequencyTwist A₁ (-θ₁))) (𝓕 (frequencyTwist A₂ θ₂)) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
              (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
              (windows 5) (windows 6) X₀ X₀ (t₁,t₂,t₃)) := by
  have hn₁ : ∀ t, halfNormalizationCLM U g₁ t ≠ 0 → |t| ≤ A := by
    intro t ht
    apply hg₁ t
    intro h
    apply ht
    rw [halfNormalizationCLM_apply U hUc hUs, h, mul_zero]
  have hn₂ : ∀ t, halfNormalizationCLM U g₂ t ≠ 0 → |t| ≤ A := by
    intro t ht
    apply hg₂ t
    intro h
    apply ht
    rw [halfNormalizationCLM_apply U hUc hUs, h, mul_zero]
  obtain ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hW,htrans⟩ :=
    actual_raw_twisted_sector_transfer p hp hcop hg hinj
      (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A H hA hH hn₁ hn₂ ε hε decayOrder J
  refine ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  obtain ⟨b,hb⟩ := htrans D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  refine ⟨b,?_⟩
  intro θ₁ θ₂
  obtain ⟨hb',hbound⟩ := hb θ₁ θ₂
  refine ⟨hb',?_⟩
  intro B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K s T X lengthScale hs hv hCB hD hΨ hX hL hz hud hue huv hkap hmap hT hnorm
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
    jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  have hsector : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x (hs hx)
  have hU₁' : ∀ s, frequencyTwist g₁ θ₁ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₁ s
    intro hz
    apply hs
    simp only [frequencyTwist_apply, hz, mul_zero]
  have hU₂' : ∀ s, frequencyTwist g₂ θ₂ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₂ s
    intro hz
    apply hs
    simp only [frequencyTwist_apply, hz, mul_zero]
  rw [secondExpansionSource_eq_raw_variable_sector p hp hcop hg hinj hpr B C D F v₁ v₂ ε₁ ε₂
    Ψ m r z s hsector X Y hX U hUc hUs (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W hU₁' hU₂']
  simp only [halfNormalization_twist U hUc hUs]
  have hrow : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact secondExpansionSector_frequency_ne_zero F K R x (hs hx)
  have liftP : ∀ P : SecondSupportData ι → Prop,
      (∀ x ∈ s, P (expansionSupportData C D x)) →
      ∀ y ∈ s.image (expansionSupportData C D), P y := by
    intro P hP y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hP x hx
  have hxscale : ∀ y : SecondSupportData ι, 0 < secondExpansionScale p X r y := by
    intro y
    exact div_pos hX (mul_pos
      (SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _))
      (SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _)))
  have hw : ∀ y ∈ s.image (expansionSupportData C D),
      ‖secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y) y *
        (secondExpansionScale p X r y : ℂ)⁻¹‖ *
      ‖outerWindow windows (secondSectorZ p (secondExpansionScale p X r y) X₀ y)
        (secondSectorUd p D₀ y) (secondSectorUe p E₀ y) (secondSectorUv p V₀ y)
        (secondSectorKap p K₀ y)‖ ≤
      Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ * Cw := by
    intro y hy
    exact mul_le_mul (secondNormalizedPushWeight_norm_le p hp hcop hg hinj hc C D Ψ m c d r z
      X Y hX hY.le s hsector (fun x hx => hΨ _) (fun x hx => hΨ _) y hy)
      (hW _ _ _ _ _) (norm_nonneg _) (by positivity)
  exact hbound B v₁ v₂ ε₁ ε₂ (s.image (expansionSupportData C D)) T
    (secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y))
    (Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ * Cw) lengthScale F
    (secondRayMinus Ψ z) (secondRayPlus Ψ z) m r (secondExpansionScale p X r)
    hv (liftP _ (fun x hx => hCB)) (liftP _ (fun x hx => hD))
    (fun y hy => hxscale y) (liftP _ hrow) (liftP _ hz) (liftP _ hud)
    (liftP _ hue) (liftP _ huv) (liftP _ hkap) (by positivity) hL
    (liftP _ hmap) hT hnorm hw

end

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (halfNormalizationCLM halfNormalizationCLM_apply halfNormalization_twist
  frequencyTwist frequencyTwist_apply outerWindow tripleCoefficient)
open SecondPassIntegration (childGeometricMean densityChildEnergy child_coefficient_density_bound)

theorem normalized_twisted_second_sector_density_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ t, g₁ t ≠ 0 → U t = 1)
    (hU₂ : ∀ t, g₂ t ≠ 0 → U t = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ D₀ E₀ V₀ X₀ K₀ Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X₀ → 0 < K₀ → 0 < Y →
      ∀ θ₁ θ₂ : ℝ,
      ∀ (B C D R F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (s : Finset (SecondExpansionData ι))
        (T : Finset (Ideal O × O)) (X lengthScale : ℝ),
        s ⊆ secondExpansionSector F (fun G E => (K G E).erase 0) R →
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ lengthScale →
        (∀ x ∈ s, |secondSectorZ p
          (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
            (expansionSupportData C D x)) X₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
          secondSupportRow p (expansionSupportData C D x)) ∈ T) →
        (∀ t ∈ T, t.1 ≠ ⊥) → (∀ t ∈ T, (Ideal.absNorm t.1 : ℝ) ≤ lengthScale) →
        ‖secondExpansionSource p hp hcop hg F Ψ m
          (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
            jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) z s
          (fun S => normalizedColumn p (fun A => (frequencyTwist g₁ θ₁) (columnLog p X A)) S)
          (fun S => normalizedColumn p (fun A => (frequencyTwist g₂ θ₂) (columnLog p X A)) S) W Y‖ ≤
        (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
            X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
        (Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2) /
          (1+Y*K₀/(D₀*E₀^2*V₀^2*X₀^2))^decayOrder) *
        densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
          (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
          (windows 5) (windows 6) X₀ X₀ J := by
  obtain ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,htrans⟩ :=
    normalized_twisted_second_sector_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g₁ g₂ W hU₁ hU₂ A H hA hH hg₁ hg₂ ε hε decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY θ₁ θ₂
  obtain ⟨b,hb⟩ := htrans D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  obtain ⟨hpoint,hbound⟩ := hb θ₁ θ₂
  intro B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K s T X lengthScale hs hv hCB hD hΨ hX hL
    hz hud hue huv hkap hmap hT hnorm
  have hh := hbound B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K s T X lengthScale hs hv hCB hD hΨ hX hL
    hz hud hue huv hkap hmap hT hnorm
  let scale := (1+Y*K₀/(D₀*E₀^2*V₀^2*X₀^2))^decayOrder
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hd := child_coefficient_density_bound p hp hcop hg F
    (secondRayMinus Ψ z) (secondRayPlus Ψ z)
    (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
    (windows 5) (windows 6) X₀ X₀
    (𝓕 (frequencyTwist A₁ (-θ₁))) (𝓕 (frequencyTwist A₂ θ₂)) b J scale
    (Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)) hpoint
  have hi := (le_div_iff₀' hscale).2 hd
  apply hh.trans
  calc
    _ ≤ (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
            X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
        ((Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2) *
          densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
            (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
            (windows 5) (windows 6) X₀ X₀ J) / scale) := by
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by dsimp [scale]; ring

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (tripleCoefficient frequencyTwist frequencyTwist_apply)
open SecondPassIntegration (childGeometricMean densityChildEnergy)

theorem secondInputCoefficient_frequencyTwist_norm {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (Ψ : O →* ℂ) (m c d : O)
    (g : 𝓢(ℝ, ℂ)) (θ X : ℝ) (G : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d
      (fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S) G‖ =
    ‖secondInputCoefficient p hg Ψ m c d
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) G‖ := by
  simp only [secondInputCoefficient, normalizedColumn, frequencyTwist_apply, norm_mul, norm_div,
    FourierBridge.logPhase_norm, one_mul]

theorem normalized_truncated_second_density_transfer
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ, ℂ)) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ (D₀ E₀ V₀ X₀ K₀ : Finset ι → κ → ℝ) (Y : ℝ),
        (∀ R j, 0 < D₀ R j) → (∀ R j, 0 < E₀ R j) → (∀ R j, 0 < V₀ R j) →
        (∀ R j, 0 < X₀ R j) → (∀ R j, 0 < K₀ R j) → 0 < Y → ∀ θ : ℝ,
      ∀ (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (X : ℝ) (K : Finset ι → Finset ι → Finset O)
        (label : Finset ι → SecondExpansionData ι → κ)
        (T : Finset ι → κ → Finset (Ideal O × O)) (lengthScale : Finset ι → κ → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X →
        (∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) →
        (∀ R ∈ F.powerset, ∀ j, 0 ≤ lengthScale R j) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorZ p
            (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
              (expansionSupportData C D x)) (X₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorUd p (D₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorUe p (E₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorUv p (V₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorKap p (K₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
            secondSupportRow p (expansionSupportData C D x)) ∈ T R j) →
        (∀ R ∈ F.powerset, ∀ j, ∀ t ∈ T R j, t.1 ≠ ⊥) →
        (∀ R ∈ F.powerset, ∀ j, ∀ t ∈ T R j, (Ideal.absNorm t.1 : ℝ) ≤ lengthScale R j) →
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
          jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Hcol := fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S
        ‖truncatedSecondSource p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
          |Y| * ‖paperRadialFourier W 0‖ *
            (∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d
              (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) G‖ ^ 2) +
          ∑ z : SecondRayIndex, ∑ R ∈ F.powerset, ∑ j : κ,
            (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
                X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
              (lengthScale R j * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
            (Cₛ*(1+‖θ‖)^(J+2)*(1+‖θ‖)^(J+2) /
              (1+Y*K₀ R j/(D₀ R j*(E₀ R j)^2*(V₀ R j)^2*(X₀ R j)^2))^decayOrder) *
            densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
              (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) (T R j)
              (windows 5) (windows 6) (X₀ R j) (X₀ R j) J := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hbound⟩ :=
    normalized_twisted_second_sector_density_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g g W hU hU A H hA hH hgA hgA ε hε decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY θ
    B C D F v₁ v₂ ε₁ ε₂ Ψ m X K label T lengthScale hv hCB hD hΨ hX hzero hL
    hz hud hue huv hkap hmap hT hnorm
  dsimp only
  apply (truncatedSecondSource_norm_le_zero_add_dyadic p hp hcop hg hinj hc hpr F Ψ m
    _ _ _ W Y K label).trans
  apply add_le_add
  · have hd := truncatedSecondZero_norm_le p hg hinj F Ψ m
      (primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) D)
      (fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S) W Y K hzero
    simpa only [secondInputCoefficient_frequencyTwist_norm] using hd
  · apply Finset.sum_le_sum
    intro z hz'
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    exact hbound (D₀ R j) (E₀ R j) (V₀ R j) (X₀ R j) (K₀ R j) Y
      (hD₀ R j) (hE₀ R j) (hV₀ R j) (hX₀ R j) (hK₀ R j) hY θ θ
      B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K
      (secondDyadicSector F K R label j) (T R j) X (lengthScale R j)
      (secondDyadicSector_subset F K R label j) hv hCB hD hΨ hX (hL R hR j)
      (hz R hR j) (hud R hR j) (hue R hR j) (huv R hR j) (hkap R hR j)
      (hmap R hR j) (hT R hR j) (hnorm R hR j)

end

open JointLogSeparation (frequencyTwist frequencyTwist_apply)

theorem firstCoreBaseProfile_frequencyTwist (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (θ : ℝ) :
    firstCoreBaseProfile (frequencyTwist g θ) V negative =
      frequencyTwist (firstCoreBaseProfile g V negative) θ := by
  ext s
  simp only [firstCoreBaseProfile_apply, frequencyTwist_apply]
  ring

theorem firstCoreModeProfile_frequencyTwist (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (θ t : ℝ) :
    firstCoreModeProfile (frequencyTwist g θ) V negative t =
      frequencyTwist (firstCoreBaseProfile g V negative) (θ + firstCoreModeHeight negative t) := by
  rw [firstCoreModeProfile, firstCoreBaseProfile_frequencyTwist,
    JointLogSeparation.frequencyTwist_twice]

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

def HasSieveExponent (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    sieveNorm M N ≤ C * (M * N) ^ ε * (M + N ^ α)

theorem hasSieveExponent_two : HasSieveExponent 2 := by
  intro ε hε
  let C := QuadraticInitialBound.initialSieveConstant
  have hC : 0 < C := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨4 * C, by positivity, ?_⟩
  intro M N hM hN
  have hc : (⌈N⌉₊ : ℝ) ≤ 2 * N := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ N by linarith)
    linarith
  have hc2 : (⌈N⌉₊ : ℝ) ^ 2 ≤ 4 * N ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) ⌈N⌉₊]
  have hmn : 1 ≤ M * N := by nlinarith [mul_le_mul hM hN (by norm_num : (0 : ℝ) ≤ 1) (show 0 ≤ M by linarith)]
  have he : 1 ≤ (M * N) ^ ε := Real.one_le_rpow hmn hε.le
  rw [Real.rpow_two]
  calc
    _ ≤ C * (M + (⌈N⌉₊ : ℝ) ^ 2) := sieveNorm_initial M N hM hN
    _ ≤ 4 * C * (M + N ^ 2) := by nlinarith
    _ ≤ (4 * C) * (M * N) ^ ε * (M + N ^ 2) := by
      nlinarith [show 0 ≤ (4 * C) * (M + N ^ 2) by positivity]

theorem HasSieveExponent.reverse {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C * (M * N) ^ ε * (N + M ^ α) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨262144 * C, by positivity, ?_⟩
  intro M N hM hN
  calc
    _ ≤ 262144 * sieveNorm N M := sieveNorm_reverse_le M N
    _ ≤ 262144 * (C * (N * M) ^ ε * (N + M ^ α)) :=
      mul_le_mul_of_nonneg_left (hb N M hN hM) (by norm_num)
    _ = _ := by rw [mul_comm N M]; ring

theorem sqrt_divisor_sieve_pair_le (M N D₁ D₂ Q C : ℝ)
    (hN : 0 ≤ N) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (h₁ : sieveNorm M (N / D₁) ≤ C * (N / D₁ + Q))
    (h₂ : sieveNorm M (N / D₂) ≤ C * (N / D₂ + Q)) :
    Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) ≤
      C * (N + Q * (D₁ * D₂)) := by
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hD₁le : D₁ ≤ D₁ * D₂ := by nlinarith
  have hD₂le : D₂ ≤ D₁ * D₂ := by nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ D₁ * D₂ * (C * (N / D₁ + Q)) * (C * (N / D₂ + Q)) := by
      gcongr
      exact sieveNorm_nonneg _ _
    _ = C ^ 2 * ((N + Q * D₁) * (N + Q * D₂)) := by field_simp
    _ ≤ C ^ 2 * ((N + Q * (D₁ * D₂)) * (N + Q * (D₁ * D₂))) := by gcongr
    _ = _ := by ring

theorem HasSieveExponent.divisor_pair {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N D₁ D₂ : ℝ,
      1 ≤ M → 1 ≤ N → 1 ≤ D₁ → 1 ≤ D₂ → D₁ ≤ N → D₂ ≤ N →
      Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) ≤
        C * (M * N) ^ ε * (N + M ^ α * (D₁ * D₂)) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h.reverse ε hε
  refine ⟨C, hC, ?_⟩
  intro M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N
  have hbound (D : ℝ) (hD : 1 ≤ D) (hDN : D ≤ N) :
      sieveNorm M (N / D) ≤ (C * (M * N) ^ ε) * (N / D + M ^ α) := by
    have hD0 : 0 < D := by linarith
    have hND : 1 ≤ N / D := (le_div_iff₀ hD0).mpr (by simpa using hDN)
    apply (hb M (N / D) hM hND).trans
    have hprod : M * (N / D) ≤ M * N := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact div_le_self (by linarith) hD
    gcongr
  exact sqrt_divisor_sieve_pair_le M N D₁ D₂ (M ^ α) (C * (M * N) ^ ε)
    (by linarith) hD₁ hD₂ (Real.rpow_nonneg (by linarith) _) (by positivity)
    (hbound D₁ hD₁ hD₁N) (hbound D₂ hD₂ hD₂N)

open IdealCoprimeSieveOperator DivisorBlockCauchy

variable {n p : Type*} [Fintype n] [Fintype p]

def divisorEnergyFactor (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  256 * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2 *
    Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ k, ‖b k‖ ^ 2)

theorem divisorEnergyFactor_nonneg (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) (b : p → ℂ) :
    0 ≤ divisorEnergyFactor ε hε N a b := by
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  unfold divisorEnergyFactor
  positivity

theorem divisorBlockCost_sqrt (ε : ℝ) (hε : 0 < ε) (D₁ D₂ M N : ℝ)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (a : n → ℂ) (b : p → ℂ) :
    Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) =
      divisorEnergyFactor ε hε N a b *
        Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) := by
  have hA := sieveNorm_nonneg M (N / D₁)
  have hB := sieveNorm_nonneg M (N / D₂)
  have hp : 0 ≤ D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) := by positivity
  have ha : 0 ≤ ∑ j, ‖a j‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : 0 ≤ ∑ k, ‖b k‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : 0 ≤ divisorBlockCost ε hε D₁ D₂ M N a b := by
    unfold divisorBlockCost
    positivity
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (divisorEnergyFactor_nonneg ε hε N a b) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt hc]
  simp only [divisorEnergyFactor, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hp]
  unfold divisorBlockCost
  ring

theorem HasSieveExponent.divisor_cost {α : ℝ} (h : HasSieveExponent α) :
    ∀ deltaLoss : ℝ, 0 < deltaLoss → ∃ C : ℝ, 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (M N D₁ D₂ : ℝ),
        1 ≤ M → 1 ≤ N → 1 ≤ D₁ → 1 ≤ D₂ → D₁ ≤ N → D₂ ≤ N →
        ∀ (a : n → ℂ) (b : p → ℂ),
        Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) ≤
          divisorEnergyFactor ε hε N a b * (C * (M * N) ^ deltaLoss * (N + M ^ α * (D₁ * D₂))) := by
  intro deltaLoss hδ
  obtain ⟨C, hC, hc⟩ := h.divisor_pair deltaLoss hδ
  refine ⟨C, hC, ?_⟩
  intro ε hε M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N a b
  rw [divisorBlockCost_sqrt ε hε D₁ D₂ M N (by linarith) (by linarith) a b]
  exact mul_le_mul_of_nonneg_left (hc M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N)
    (divisorEnergyFactor_nonneg ε hε N a b)

end CanonicalQuadraticSieve

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalDifference -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum QuadraticMainBoundary QuadraticMainOperatorBound IdealCoprimeSieveOperator

theorem normalizedPair_boundary_term
    (I J H D E : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hH : Supported H) (K : ℝ) (a b : ℂ) :
    (star a * b) * ((UniqueFactorizationMonoid.moebius E : ℂ) *
      normalizedIdealPair I J (H * D * E) * (cutoffDifference K H D : ℂ)) =
    (UniqueFactorizationMonoid.moebius E : ℂ) * mainWeight K H D E *
      (star (quadraticRow I (primaryGenerator H) *
        (a * quadraticRow I (idealGenerator D * idealGenerator E))) *
       (quadraticRow J (primaryGenerator H) *
        (b * quadraticRow J (idealGenerator D * idealGenerator E)))) := by
  have hspan : Ideal.span {idealGenerator D * idealGenerator E} = D * E := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_idealGenerator, span_idealGenerator]
  have hde := unrestrictedPairCharacter_span I J hI hJ hray (idealGenerator D * idealGenerator E)
  rw [hspan] at hde
  have hp : unrestrictedPairCharacter I J (H * D * E) =
      (quadraticRow I (primaryGenerator H) * quadraticRow J (primaryGenerator H)) *
      (quadraticRow I (idealGenerator D * idealGenerator E) *
        quadraticRow J (idealGenerator D * idealGenerator E)) := by
    rw [mul_assoc, unrestrictedPairCharacter_mul I J hI hJ hray,
      unrestrictedPairCharacter_eq_primary I J hI hJ hray H hH, hde]
  rw [normalizedIdealPair, hp]
  simp only [mainWeight, div_eq_mul_inv, star_mul,
    canonical_quadraticRow_star I hI]
  ring

def actualPrincipalDifference {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (K : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j) * a k *
      (normalizedPairPartial (cols j) (cols k) K * normalizedPairDivisors (cols j) (cols k) G -
       normalizedPairCoprimePartial (cols j) (cols k) G K * normalizedPairDensity (cols j) (cols k) G)
    else 0

theorem actualPrincipalDifference_bound
    {n : Type*} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (N : ℝ) (hN : 0 ≤ N) (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (cols j) = columnRay (cols k)) (a : n → ℂ)
    (G : Ideal O) (hG : Squarefree G) (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G)
    (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) :
    ‖actualPrincipalDifference cols a G K‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * sieveNorm K N * (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) := by
  let S := coprimeSquarefreeRange G K
  have hS : S ⊆ idealRange K := coprimeSquarefreeRange_subset_idealRange G hbad K
  let A : Matrix S n ℂ := fun H j => quadraticRow (cols j) (primaryGenerator H.val)
  let r : Ideal O → Ideal O → n → ℂ := fun D E j =>
    quadraticRow (cols j) (idealGenerator D * idealGenerator E)
  have hpoint (j k : n) :
      (if IsCoprime (cols j) (cols k) then star (a j) * a k *
        (normalizedPairPartial (cols j) (cols k) K * normalizedPairDivisors (cols j) (cols k) G -
         normalizedPairCoprimePartial (cols j) (cols k) G K * normalizedPairDensity (cols j) (cols k) G) else 0) =
      ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G, ∑ H : S,
        (UniqueFactorizationMonoid.moebius E : ℂ) * mainWeight K H.val D E *
          (if IsCoprime (cols j) (cols k) then
            star (A H j * (a j * r D E j)) * (A H k * (a k * r D E k)) else 0) := by
    dsimp only [A, r]
    by_cases hc : IsCoprime (cols j) (cols k)
    · rw [ite_eq_left hc, normalizedPair_main_difference (cols j) (cols k) (hcols j).1 (hcols k).1 (hray j k) G hG K]
      simp only [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (coprimeSquarefreeRange G K))) (t := idealDivisors G)]
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      apply Finset.sum_congr rfl
      intro H _
      rw [ite_eq_left hc]
      exact normalizedPair_boundary_term (cols j) (cols k) H.val D E (hcols j).1 (hcols k).1
        (hray j k) (admissible_supported (mem_idealRange.mp (hS H.property)).1) K (a j) (a k)
    · simp only [hc, ite_false, mul_zero, Finset.sum_const_zero]
  have heq : actualPrincipalDifference cols a G K =
      ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          (∑ H : S, mainWeight K H.val D E *
            (∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
              star (A H j * (a j * r D E j)) * (A H k * (a k * r D E k)) else 0)) := by
    dsimp only [A, r]
    unfold actualPrincipalDifference
    simp_rw [hpoint]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset n)) (t := idealDivisors G),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset S))]
    simp only [Finset.mul_sum, mul_assoc, A, r]
  rw [heq]
  have hb := main_difference_operator_bound ε hε K hK G hG.ne_zero (fun H : S => H.val)
    cols (fun j => (hcols j).1.1) N hN (fun j => (hcols j).2) A a r
    (fun D E j => quadraticRow_norm_le_one (cols j) _)
  have hA : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤ sieveNorm K N :=
    family_squared_norm_le (fun H : S => H.val) cols Subtype.val_injective hinj K N
      (fun H => mem_idealRange.mp (hS H.property)) hcols
  apply hb.trans
  have hs : 0 ≤ supportConstant ε hε := (supportConstant_pos ε hε).le
  gcongr

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def middleRatio (B b D₁ d D₂ e : ℝ) : ℝ := Real.sqrt (B / b) * (D₁ / d) * (D₂ / e)

theorem middleRatio_bounds (B b D₁ d D₂ e : ℝ)
    (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    1 / 4 ≤ middleRatio B b D₁ d D₂ e ∧ middleRatio B b D₁ d D₂ e ≤ 2 := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hu1 : 1 ≤ Real.sqrt (B / b) := by
    have hq : 1 ≤ B / b := (le_div_iff₀ hb0).mpr (by simpa using hb.2)
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  have hu2 : Real.sqrt (B / b) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hb0).mpr
    nlinarith
  have hv : (1 / 2 : ℝ) ≤ D₁ / d ∧ D₁ / d ≤ 1 :=
    ⟨(le_div_iff₀ hd0).mpr (by linarith), (div_le_one hd0).mpr hd.1⟩
  have hw : (1 / 2 : ℝ) ≤ D₂ / e ∧ D₂ / e ≤ 1 :=
    ⟨(le_div_iff₀ he0).mpr (by linarith), (div_le_one he0).mpr he.1⟩
  have hv0 : 0 ≤ D₁ / d := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hv.1
  have hw0 : 0 ≤ D₂ / e := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hw.1
  have hvw1 : (1 / 4 : ℝ) ≤ (D₁ / d) * (D₂ / e) := by
    nlinarith [mul_le_mul hv.1 hw.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) hv0]
  have hvw2 : (D₁ / d) * (D₂ / e) ≤ 1 := by
    nlinarith [mul_le_mul hv.2 hw.2 hw0 (by norm_num : (0 : ℝ) ≤ 1)]
  unfold middleRatio
  constructor
  · nlinarith [mul_le_mul hu1 hvw1 (by norm_num : (0 : ℝ) ≤ 1 / 4) (Real.sqrt_nonneg (B / b))]
  · nlinarith [mul_le_mul hu2 hvw2 (mul_nonneg hv0 hw0) (by norm_num : (0 : ℝ) ≤ 2)]

theorem middleRatio_log_bound (r : ℝ) (hr : (1 / 4 : ℝ) ≤ r ∧ r ≤ 2) : |Real.log r| ≤ 4 := by
  have hr0 : 0 < r := by linarith
  have hi : r⁻¹ ≤ 4 := by
    have h : (1 : ℝ) / r ≤ 4 := (div_le_iff₀ hr0).mpr (by linarith)
    simpa only [one_div] using h
  have h₁ := Real.log_le_sub_one_of_pos hr0
  have h₂ := Real.log_le_sub_one_of_pos (inv_pos.mpr hr0)
  rw [Real.log_inv] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem middleRatio_argument (M B b D₁ d D₂ e q : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    (Real.sqrt (M / B) * q / (D₁ * D₂)) * Real.exp (Real.log (middleRatio B b D₁ d D₂ e)) =
      Real.sqrt (M / b) * q / (d * e) := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hr : 0 < middleRatio B b D₁ d D₂ e := by
    have hh := middleRatio_bounds B b D₁ d D₂ e hB hb hD₁ hd hD₂ he
    linarith
  rw [Real.exp_log hr]
  have hs : Real.sqrt (M / B) * Real.sqrt (B / b) = Real.sqrt (M / b) := by
    rw [← Real.sqrt_mul (div_nonneg hM.le hB.le)]
    congr 1
    field_simp
  unfold middleRatio
  calc
    _ = (Real.sqrt (M / B) * Real.sqrt (B / b)) * q / (d * e) := by
      field_simp

    _ = _ := by rw [hs]

theorem actual_middle_radial_block_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ B N M : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hB : 1 ≤ B) (_hN : 1 ≤ N) (_hM : 0 < M)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
        (_hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (h : O), h ≠ 0 →
        (1 + Real.sqrt (M / B) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)) ^ A *
          (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
            originalTerm rows left right a b D.val E.val i j k *
              paperRadialFourier W
                (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
                  ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  obtain ⟨C, hC, hb⟩ := canonical_original_radial_divisor_block_bound W 4 0 0 (by norm_num) (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n p _ _ _ _ _ _ ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright a b h hh
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hB0 : 0 < B := by linarith
  let R := Real.sqrt (M / B) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)
  have hR : 0 < R := div_pos (mul_pos (Real.sqrt_pos.mpr (div_pos hM hB0))
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))) (mul_pos hD₁0 hD₂0)
  let x : S → T → m → ℝ := fun D E i => Real.log
    (middleRatio B (Ideal.absNorm (rows i)) D₁ (Ideal.absNorm D.val) D₂ (Ideal.absNorm E.val))
  have hx (D : S) (E : T) (i : m) : |x D E i| ≤ 4 :=
    middleRatio_log_bound _ (middleRatio_bounds _ _ _ _ _ _ hB0 (hrows i).2 hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property))
  have he := hb R hR ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT rows left right hr hl hri
    (fun i => ⟨(hrows i).1, (hrows i).2.2⟩) hleft hright a b x (fun _ => 0) (fun _ => 0) hx
    (fun _ => by simp) (fun _ => by simp)
  have harg (D : S) (E : T) (i : m) : R * Real.exp (x D E i + (0 + 0)) =
      Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)) := by
    simp only [add_zero]
    exact middleRatio_argument _ _ _ _ _ _ _ _ hM hB0 (hrows i).2 hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property)
  simpa only [harg, R] using he

end CanonicalQuadraticSieve

namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hp

theorem firstCoreInputRow_smoothed_mode
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (Y : ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2 : ℝ)) =
      ((primeProductNorm p D)⁻¹ : ℝ) *
      ∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
        (‖inputConjugateRow p hg (F\D) (firstCoreTwist negative χ Ψ r)
          (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (normalizedColumn p (fun A => firstCoreModeProfile g V negative t
            (columnLog p (X / primeProductNorm p D) A))) z‖ ^ 2 : ℝ) := by
  let P := inputConjugateRow p hg (F\D) (firstCoreTwist negative χ Ψ r)
    (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A)))
  have he (z : O) : W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2 : ℝ) =
      (((primeProductNorm p D)⁻¹ : ℝ) : ℂ) *
        (W (‖eisEmbedding z‖ ^ 2 / Y) * (‖P (if negative then -z else z)‖ ^ 2 : ℝ)) := by
    rw [firstCoreInputRow_mode_norm_sq p hp hg F D B v ε₁ ε₂ negative χ Ψ m g V X hX c d r t z]
    push_cast
    ring
  simp_rw [he]
  rw [tsum_mul_left]
  have hsign : (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖P (if negative then -z else z)‖ ^ 2 : ℝ)) =
      ∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) * (‖P z‖ ^ 2 : ℝ) := by
    cases negative
    · rfl
    · simpa only [Bool.true_eq, ite_true, Equiv.neg_apply, map_neg, norm_neg] using
        (Equiv.neg O).tsum_eq (fun z : O => W (‖eisEmbedding z‖ ^ 2 / Y) * (‖P z‖ ^ 2 : ℝ))
  rw [hsign]

theorem firstCoreInputRow_smoothed_truncated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (Y : ℝ) (hY : 0 < Y) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (K : Finset ι → Finset ι → Finset O) :
    let Hmode := normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A))
    let Ψmode := firstCoreTwist negative χ Ψ r
    let m' := m * b0Label p B v ε₁ ε₂
    let c' := c * jLabel p B v ε₁ ε₂
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2 : ℝ)) =
      ((primeProductNorm p D)⁻¹ : ℝ) *
        (truncatedSecondSource p hp hg hinj (F\D) Ψmode m' c' d Hmode W Y K +
          secondSourceTail p hp hg hinj (F\D) Ψmode m' c' d Hmode W Y K) := by
  dsimp only
  rw [firstCoreInputRow_smoothed_mode p hp hg F D B v ε₁ ε₂ negative χ Ψ m g V W X hX Y c d r t,
    inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc]
  exact hY

theorem firstCoreInputRow_finite_le_truncated_tail
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (Y : ℝ) (hY : 0 < Y) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (T : Finset O)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0) (K : Finset ι → Finset ι → Finset O) :
    let Hmode := normalizedColumn p (fun A => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) A))
    let Ψmode := firstCoreTwist negative χ Ψ r
    let m' := m * b0Label p B v ε₁ ε₂
    let c' := c * jLabel p B v ε₁ ε₂
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
      (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2) +
      ‖firstCoreTest (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X)
        negative t D ∅‖ ^ 2 ≤
      (primeProductNorm p D)⁻¹ *
        (‖truncatedSecondSource p hp hg hinj (F\D) Ψmode m' c' d Hmode rowMajorant Y K‖ +
          ‖secondSourceTail p hp hg hinj (F\D) Ψmode m' c' d Hmode rowMajorant Y K‖) := by
  dsimp only
  have h := firstCoreInputRow_finite_le_corrected_source p hg F D B v ε₁ ε₂ negative χ Ψ m
    (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t T Y hY hT hT0
  have he := firstCoreInputRow_smoothed_truncated p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    g V rowMajorant X hX Y hY c d r t K
  rw [he] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re] at h
  apply (le_sub_iff_add_le.mp h).trans
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp D).le

end SecondPassArithmetic

namespace SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

lemma childEnergy_eq_difference (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X a b : ℝ)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg F Ψ m T V X testNegative rowNegative a b =
      childEnergy p hp hcop hg F Ψ m T V X testNegative rowNegative (a-b) 0 := by
  have he : fixedSecondTest p V X a b testNegative =
      fixedSecondTest p V X (a-b) 0 testNegative := by
    funext N
    simp only [fixedSecondTest, sub_zero]
  simp only [childEnergy, he]

theorem densityChildEnergy_polynomial_bound (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (J : ℕ) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (h₁ : ∀ a : ℝ, childEnergy p hp hcop hg F Ψ₁ m T V₁ X₁ true false a 0 ≤
      B₁ * (1+‖a‖)^(2*J))
    (h₂ : ∀ a : ℝ, childEnergy p hp hcop hg F Ψ₂ m T V₂ X₂ false true a 0 ≤
      B₂ * (1+‖a‖)^(2*J)) :
    densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (2*J) ≤
      (Real.sqrt B₁ * Real.sqrt B₂) *
        (∫ t : ℝ, FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  let G := childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false) *
    Real.sqrt (energyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀ q, G q ≤ M := by
    intro q
    dsimp [G, childGeometricMean, M]
    gcongr
    · exact childEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact childEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  have hsqrt (B a e : ℝ) (hB : 0 ≤ B) (he : e ≤ B*(1+‖a‖)^(2*J)) :
      Real.sqrt e ≤ Real.sqrt B * (1+‖a‖)^J := by
    calc
      _ ≤ Real.sqrt (B*(1+‖a‖)^(2*J)) := Real.sqrt_le_sqrt he
      _ = _ := by
        rw [Real.sqrt_mul hB, mul_comm 2 J, pow_mul, Real.sqrt_sq (by positivity)]
  have hbound (q : Frequency) : G q ≤
      (Real.sqrt B₁ * Real.sqrt B₂) *
        (1+‖q.1‖)^(2*J)*(1+‖q.2.1‖)^(2*J)*(1+‖q.2.2‖)^(2*J) := by
    have hleft := h₁ (q.1-q.2.2)
    have hright := h₂ (q.2.1-q.2.2)
    rw [← childEnergy_eq_difference p hp hcop hg F Ψ₁ m T V₁ X₁ q.1 q.2.2 true false] at hleft
    rw [← childEnergy_eq_difference p hp hcop hg F Ψ₂ m T V₂ X₂ q.2.1 q.2.2 false true] at hright
    calc
      _ ≤ (Real.sqrt B₁ * (1+‖q.1-q.2.2‖)^J) *
          (Real.sqrt B₂ * (1+‖q.2.1-q.2.2‖)^J) :=
        mul_le_mul (hsqrt B₁ _ _ hB₁ hleft) (hsqrt B₂ _ _ hB₂ hright)
          (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt B₁ * Real.sqrt B₂) *
          ((1+‖q.1-q.2.2‖)^J * (1+‖q.2.1-q.2.2‖)^J) := by ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (difference_height_weight_le q.1 q.2.1 q.2.2 J)
          (mul_nonneg (Real.sqrt_nonneg B₁) (Real.sqrt_nonneg B₂))
        simpa only [mul_assoc] using hh
  exact triple_density_polynomial_bound G hG hG0 M hM (2*J)
    (Real.sqrt B₁ * Real.sqrt B₂) hbound

end SecondPassIntegration

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def residualPairWeight (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι) : ℂ :=
  star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
    (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T)

theorem residualSecondMode_tail_eq (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m c d : O) (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (K : Finset O) :
    (∑' k : {k : O // k ∉ K}, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y) =
    ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset, if Disjoint S T then
      residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
        ∑' k : {k : O // k ∉ K}, secondPairRadialMode p hp hg hinj S T e k.val W Y else 0 := by
  have hs (S T : Finset ι) : Summable (fun k : {k : O // k ∉ K} =>
      if Disjoint S T then residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
        secondPairRadialMode p hp hg hinj S T e k.val W Y else 0) := by
    by_cases hd : Disjoint S T
    · simp only [ite_eq_left hd]
      exact ((secondPairRadialMode_summable p hp hg hinj S T e he W Y hY).subtype _).mul_left _
    · simp only [ite_eq_right hd]
      exact summable_zero
  change (∑' k : {k : O // k ∉ K}, ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
    if Disjoint S T then residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T *
      secondPairRadialMode p hp hg hinj S T e k.val W Y else 0) = _
  rw [Summable.tsum_finsetSum (fun S _ => summable_sum (fun T _ => hs S T))]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Summable.tsum_finsetSum (fun T _ => hs S T)]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd, tsum_mul_left]
  · simp [hd]

def residualTailCost (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m c d : O) (H₁ H₂ : Finset ι → ℂ) (e : O) (Y H : ℝ) (A : ℕ) (P : ℝ) : ℝ :=
  ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset, if Disjoint S T then
    let n := ∏ i : activeSupport T S, p i.val
    let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
    ‖residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T‖ *
      ((Y/‖eisEmbedding n‖) * (P / ((min 1 scale)^2 * (1+H)^A)))
    else 0

theorem residualSecondMode_tail_bound
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
      (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H → ∀ K : Finset O,
      (∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T ≠ 0 →
        ∀ k : O, k ∉ K →
          H ≤ (Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) *
            ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y‖ ≤
      residualTailCost p hg F G Ψ₁ Ψ₂ m c d H₁ H₂ e Y H A (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := secondPairRadialMode_remainder p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y H hY hH K hK
  rw [residualSecondMode_tail_eq p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y hY K]
  unfold residualTailCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd, norm_mul]
    by_cases hw : residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T = 0
    · simp only [hw, norm_zero, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (hb S T e he W Y H hY hH K (hK S hS T hT hd hw)) (norm_nonneg _)
  · simp [hd]

theorem secondSourceTail_bound
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (Hcol : Finset ι → ℂ)
      (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
      ∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
        residualTailCost p hg F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := residualSecondMode_tail_bound p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro F Ψ m c d Hcol W Y H hY hH K hK
  unfold secondSourceTail
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro G hG
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro E hE
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
    (Finset.mem_powerset.mp E.property) Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))]
  exact hb F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) (primeSubsetGenerator_ne_zero _ _)
    W Y H hY hH (K G E.val) (hK G hG E)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_eq_ideal_norm (S : Finset ι) :
    primeProductNorm p S = (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) := by
  rw [primeProductNorm, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    FiniteGaussPhase.span_finset_prod]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_ge_one (S : Finset ι) : 1 ≤ primeProductNorm p S :=
  by
    rw [primeProductNorm, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {∏ i ∈ S, p i}) ≠ 0 by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_mono {S T : Finset ι} (hST : S ⊆ T) :
    primeProductNorm p S ≤ primeProductNorm p T := by
  have hd : Disjoint S (T\S) := Finset.disjoint_sdiff
  have hu : S ∪ (T\S) = T := Finset.union_sdiff_of_subset hST
  rw [← hu, FirstPassCubeLabels.primeProductNorm_union p S (T\S) hd]
  exact le_mul_of_one_le_right (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
    (primeProductNorm_ge_one p hp _)

def boundedPrimeSupports (F : Finset ι) (X : ℝ) : Finset (Finset ι) :=
  F.powerset.filter (fun S => primeProductNorm p S ≤ X)

include hinj in
theorem boundedPrimeSupports_card (F : Finset ι) (X : ℝ) (hX : 1 ≤ X) :
    ((boundedPrimeSupports p F X).card : ℝ) ≤ 128*X := by
  let q : Finset ι → Ideal O := fun S => ∏ i ∈ S, Ideal.span {p i}
  have hq : Function.Injective q := FirstCauchyArithmetic.family_product_injective _ hinj
  let I := (boundedPrimeSupports p F X).image q
  have hcard : I.card = (boundedPrimeSupports p F X).card := Finset.card_image_of_injective _ hq
  rw [← hcard]
  apply DescentFiberCost.finite_ideal_count_real I X hX
  · intro J hJ
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hJ
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))
  · intro J hJ
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hJ
    rw [← primeProductNorm_eq_ideal_norm p S]
    exact (Finset.mem_filter.mp hS).2

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem normalizedColumn_subset_norm_bound (g : 𝓢(ℝ, ℂ)) (A X : ℝ)
    (hX : 0 < X) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A) (G S U : Finset ι)
    (hU : U ⊆ G∪S)
    (hn : FirstPassCubeLabels.normalizedColumn p
      (fun R => g (FirstPassCubeLabels.columnLog p X R)) (G∪S) ≠ 0) :
    primeProductNorm p U ≤ X*Real.exp A := by
  have hval : g (FirstPassCubeLabels.columnLog p X (G∪S)) ≠ 0 := by
    intro h
    apply hn
    simp only [FirstPassCubeLabels.normalizedColumn,h,zero_div]
  exact (primeProductNorm_mono p hp hU).trans
    (columnLog_norm_upper p hp X A hX (G∪S) ((le_abs_self _).trans (hgA _ hval)))

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.SpatialDerivatives -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem column_sqrt_ratio_bounds (N n : ℝ) (hN : 0 < N) (hn : N / 2 ≤ n ∧ n ≤ N) :
    1 / 4 ≤ Real.sqrt (n / N) ∧ Real.sqrt (n / N) ≤ 2 := by
  have hq0 : 0 ≤ n / N := div_nonneg (by linarith) hN.le
  have hq1 : (1 / 2 : ℝ) ≤ n / N := (le_div_iff₀ hN).mpr (by linarith)
  have hq2 : n / N ≤ 1 := (div_le_one hN).mpr hn.2
  have hs := Real.sq_sqrt hq0
  have hp := Real.sqrt_nonneg (n / N)
  constructor <;> nlinarith

theorem dual_middle_sqrt_identity (M B b N i j F : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : 0 < b) (hN : 0 < N)
    (hi : 0 < i) (hj : 0 < j) (hF : 0 < F) :
    N * Real.sqrt (F / (M * B)) * Real.sqrt (B / b) * Real.sqrt (i / N) * Real.sqrt (j / N) =
      Real.sqrt (F * i * j / (M * b)) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  simp only [mul_pow, Real.sq_sqrt (show 0 ≤ F / (M * B) by positivity),
    Real.sq_sqrt (show 0 ≤ B / b by positivity), Real.sq_sqrt (show 0 ≤ i / N by positivity),
    Real.sq_sqrt (show 0 ≤ j / N by positivity), Real.sq_sqrt (show 0 ≤ F * i * j / (M * b) by positivity)]
  field_simp

theorem dual_middle_argument (M B b N i j F D₁ d D₂ e q : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) (hF : 0 < F)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    (N * Real.sqrt (F / (M * B)) * q / (D₁ * D₂)) *
      Real.exp (Real.log (middleRatio B b D₁ d D₂ e) +
        (Real.log (Real.sqrt (i / N)) + Real.log (Real.sqrt (j / N)))) =
      Real.sqrt (F * i * j / (M * b)) * q / (d * e) := by
  have hb0 : 0 < b := by linarith
  have hi0 : 0 < i := by linarith
  have hj0 : 0 < j := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hr : 0 < middleRatio B b D₁ d D₂ e := by
    have hh := middleRatio_bounds B b D₁ d D₂ e hB hb hD₁ hd hD₂ he
    linarith
  rw [Real.exp_add, Real.exp_add, Real.exp_log hr,
    Real.exp_log (Real.sqrt_pos.mpr (div_pos hi0 hN)),
    Real.exp_log (Real.sqrt_pos.mpr (div_pos hj0 hN))]
  unfold middleRatio
  calc
    _ = (N * Real.sqrt (F / (M * B)) * Real.sqrt (B / b) * Real.sqrt (i / N) * Real.sqrt (j / N)) * q / (d * e) := by
      field_simp

    _ = _ := by rw [dual_middle_sqrt_identity M B b N i j F hM hB hb0 hN hi0 hj0 hF]

theorem actual_dual_middle_radial_block_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ B N M F : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hB : 1 ≤ B) (_hN : 1 ≤ N)
        (_hM : 0 < M) (_hF : 0 < F)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
        (_hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (h : O), h ≠ 0 →
        (1 + N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)) ^ A *
          (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
            originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
              (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
                (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
                  ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  obtain ⟨C, hC, hb⟩ := canonical_original_radial_divisor_block_bound W 4 4 4 (by norm_num) (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n p _ _ _ _ _ _ ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright a b h hh
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hB0 : 0 < B := by linarith
  have hN0 : 0 < N := by linarith
  let R := N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)
  have hR : 0 < R := div_pos (mul_pos (mul_pos hN0 (Real.sqrt_pos.mpr (by positivity)))
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))) (mul_pos hD₁0 hD₂0)
  let x : S → T → m → ℝ := fun D E i => Real.log
    (middleRatio B (Ideal.absNorm (rows i)) D₁ (Ideal.absNorm D.val) D₂ (Ideal.absNorm E.val))
  let y : n → ℝ := fun j => Real.log (Real.sqrt ((Ideal.absNorm (left j) : ℝ) / N))
  let z : p → ℝ := fun k => Real.log (Real.sqrt ((Ideal.absNorm (right k) : ℝ) / N))
  have hx (D : S) (E : T) (i : m) : |x D E i| ≤ 4 :=
    middleRatio_log_bound _ (middleRatio_bounds _ _ _ _ _ _ hB0 (hrows i).2 hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property))
  have hy (j : n) : |y j| ≤ 4 := middleRatio_log_bound _ (column_sqrt_ratio_bounds N _ hN0 (hleft j).2)
  have hz (k : p) : |z k| ≤ 4 := middleRatio_log_bound _ (column_sqrt_ratio_bounds N _ hN0 (hright k).2)
  have he := hb R hR ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT rows left right hr hl hri
    (fun i => ⟨(hrows i).1, (hrows i).2.2⟩) (fun j => ⟨(hleft j).1, (hleft j).2.2⟩)
    (fun k => ⟨(hright k).1, (hright k).2.2⟩) a b x y z hx hy hz
  have harg (D : S) (E : T) (i : m) (j : n) (k : p) : R * Real.exp (x D E i + (y j + z k)) =
      Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
        (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)) :=
    dual_middle_argument _ _ _ _ _ _ _ _ _ _ _ _ hM hB0 (hrows i).2 hN0 (hleft j).2 (hright k).2 hF
      hD₁0 (hS D.val D.property) hD₂0 (hT E.val E.property)
  simpa only [harg, R] using he

theorem principal_middle_prefactor_bound (M B b D₁ d D₂ e : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d) (hD₂ : 0 < D₂) (he : D₂ ≤ e) :
    Real.sqrt (M / b) / (d * e) ≤ 2 * Real.sqrt (M / B) / (D₁ * D₂) := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd
  have he0 : 0 < e := hD₂.trans_le he
  have hq : M / b ≤ 4 * (M / B) := by
    calc
      _ ≤ (4 * M) / B := (div_le_div_iff₀ hb0 hB).mpr (by nlinarith [mul_nonneg hM.le (show 0 ≤ 4 * b - B by linarith)])
      _ = _ := by ring
  have hs : Real.sqrt (M / b) ≤ 2 * Real.sqrt (M / B) := by
    have hh := Real.sqrt_le_sqrt hq
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)
    rw [hs4] at hh
    exact hh
  calc
    _ ≤ (2 * Real.sqrt (M / B)) / (d * e) := div_le_div_of_nonneg_right hs (mul_pos hd0 he0).le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (mul_pos hD₁ hD₂)
      (mul_le_mul hd he hD₂.le hd0.le)

theorem principal_middle_prefactor_sum {m : Type*} [Fintype m]
    (S T : Finset (Ideal O)) (rows : m → Ideal O) (f : S → T → m → ℝ)
    (hf : ∀ D E i, 0 ≤ f D E i) (M B D₁ D₂ : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i) : ℝ))
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ)) (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ)) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) * f D E i) ≤
      (2 * Real.sqrt (M / B) / (D₁ * D₂)) * ∑ D : S, ∑ E : T, ∑ i, f D E i := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (hf D E i)
  exact principal_middle_prefactor_bound M B _ D₁ _ D₂ _ hM hB (hrows i) hD₁
    (hS D.val D.property) hD₂ (hT E.val E.property)

def originalMiddleConstant (W : 𝓢(ℝ, ℂ)) : ℝ := (actual_middle_radial_block_bound.{0, 0, 0} W 0).choose

def dualMiddleConstant (W : 𝓢(ℝ, ℂ)) : ℝ := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 0).choose

theorem dual_principal_prefactor_identity (M F b i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hi : 0 < i) (hj : 0 < j) :
    (M / (Real.sqrt (i * j) * F)) * Real.sqrt (F * i * j / (M * b)) =
      Real.sqrt ((M / F) / b) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ i * j by positivity),
    Real.sq_sqrt (show 0 ≤ F * i * j / (M * b) by positivity),
    Real.sq_sqrt (show 0 ≤ (M / F) / b by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a : n → ℂ) (b : p → ℂ) (h : O) (hh : h ≠ 0)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows hh

theorem actual_original_middle_weighted_bound
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
        (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
    (2 * Real.sqrt (M / B) / (D₁ * D₂)) * originalMiddleConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hk := (actual_middle_radial_block_bound.{0, 0, 0} W 0).choose_spec.2 ε hε S T D₁ D₂ B N M
    hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright a b h hh
  change _ ≤ originalMiddleConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) at hk
  simp only [pow_zero, one_mul] at hk
  apply (principal_middle_prefactor_sum S T rows _ (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM
    (by linarith) (by linarith) (by linarith) (fun i => (hrows i).2.1)
    (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 * Real.sqrt (M / B) / (D₁ * D₂) by positivity)

theorem actual_dual_middle_weighted_bound
    (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
        (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
            ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
    (2 * Real.sqrt ((M / F) / B) / (D₁ * D₂)) * dualMiddleConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hk := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 0).choose_spec.2 ε hε S T D₁ D₂ B N M F
    hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright a b h hh
  change _ ≤ dualMiddleConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) at hk
  simp only [pow_zero, one_mul] at hk
  apply (principal_middle_prefactor_sum S T rows _ (fun _ _ _ => norm_nonneg _) (M / F) B D₁ D₂ (div_pos hM hF)
    (by linarith) (by linarith) (by linarith) (fun i => (hrows i).2.1)
    (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 * Real.sqrt ((M / F) / B) / (D₁ * D₂) by positivity)

end CanonicalQuadraticSieve

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma abs_le_inv_of_mul_sq_le_one {v t : ℝ} (hv : 0<v) (h : v^2*t^2≤1) :
    |t|≤1/v := by
  apply (le_div_iff₀ hv).mpr
  have he : |v*t|≤1 := (sq_le_one_iff_abs_le_one _).mp (by simpa only [mul_pow] using h)
  simpa only [abs_mul,abs_of_pos hv,mul_comm] using he

lemma heightLog_first_bounds (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : 0<v)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    |heightLogDx A B C D x y v|≤1/v ∧
    |heightLogDy A B C D x y v|≤1/v ∧
    |heightLogDv A B C D x y v|≤1/v := by
  have he := heightLog_eikonal A B C D x y v hrel hv.ne' hq
  have hx := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDx A B C D x y v))
  have hy := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDy A B C D x y v))
  have hz := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDv A B C D x y v))
  exact ⟨abs_le_inv_of_mul_sq_le_one hv (by nlinarith),
    abs_le_inv_of_mul_sq_le_one hv (by nlinarith),
    abs_le_inv_of_mul_sq_le_one hv (by nlinarith)⟩

lemma heightLog_second_bounds (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : 0<v)
    (hA : 0≤A) (hq : 0<quadraticHeightDenominator A B C D x y v)
    (hAv : A*v^2≤quadraticHeightDenominator A B C D x y v) :
    |heightLogDxx A B C D x y v|≤7/v^2 ∧
    |heightLogDyy A B C D x y v|≤7/v^2 ∧
    |heightLogDvv A B C D x y v|≤7/v^2 := by
  let q := quadraticHeightDenominator A B C D x y v
  let r := v^2*A/q
  have hr0 : 0≤ r := div_nonneg (mul_nonneg (sq_nonneg v) hA) hq.le
  have hr1 : r≤1 := (div_le_one hq).mpr (by simpa only [mul_comm] using hAv)
  have he := heightLog_eikonal A B C D x y v hrel hv.ne' hq.ne'
  have hx := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDx A B C D x y v))
  have hy := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDy A B C D x y v))
  have hz := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDv A B C D x y v))
  have hx1 : v^2*(heightLogDx A B C D x y v)^2≤1 := by nlinarith
  have hy1 : v^2*(heightLogDy A B C D x y v)^2≤1 := by nlinarith
  have hxx : v^2*heightLogDxx A B C D x y v =
      v^2*(heightLogDx A B C D x y v)^2-2*r := by
    dsimp [heightLogDxx,heightLogDx,r,q]
    field_simp
    ; ring
  have hyy : v^2*heightLogDyy A B C D x y v =
      v^2*(heightLogDy A B C D x y v)^2-2*r := by
    dsimp [heightLogDyy,heightLogDy,r,q]
    field_simp
    ; ring
  have hvv : v^2*heightLogDvv A B C D x y v = -1-2*r+4*r^2 := by
    dsimp [heightLogDvv,r,q]
    field_simp [hv.ne',hq.ne']
    ; ring
  have hconv (a : ℝ) (ha : |v^2*a|≤7) : |a|≤7/v^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hv)).mpr
    simpa only [abs_mul,abs_of_nonneg (sq_nonneg v),mul_comm] using ha
  refine ⟨hconv _ (abs_le.mpr ⟨?_,?_⟩), hconv _ (abs_le.mpr ⟨?_,?_⟩),
    hconv _ (abs_le.mpr ⟨?_,?_⟩)⟩
  all_goals nlinarith [sq_nonneg r,mul_nonneg hr0 (sub_nonneg.mpr hr1)]

lemma actual_quadraticHeight_nonneg (u : Fin 2 → ℂ) (x y v : ℝ) :
    Complex.normSq (u 0)*v^2 ≤
      quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  rw [← heightDenominator_eq_quadratic]
  unfold heightDenominator
  rw [Complex.normSq_eq_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

open Filter
open scoped BigOperators Classical Topology Matrix

abbrev SpatialCoordinates := Fin 3 → ℝ

def axisSlice (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ → ℂ :=
  fun t => f (Function.update p j t)

def spatialLogD (A B C D : ℝ) (p : SpatialCoordinates) : Fin 3 → ℝ :=
  ![heightLogDx A B C D (p 0) (p 1) (p 2),
    heightLogDy A B C D (p 0) (p 1) (p 2),
    heightLogDv A B C D (p 0) (p 1) (p 2)]
def spatialLogDD (A B C D : ℝ) (p : SpatialCoordinates) : Fin 3 → ℝ :=
  ![heightLogDxx A B C D (p 0) (p 1) (p 2),
    heightLogDyy A B C D (p 0) (p 1) (p 2),
    heightLogDvv A B C D (p 0) (p 1) (p 2)]

lemma spatial_axis_hasDerivAt (s : ℂ) (A B C D : ℝ) (p : SpatialCoordinates) (j : Fin 3)
    (hv : p 2≠0) (hq : quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)≠0) :
    HasDerivAt (axisSlice (fun q => spatialHeightPower s A B C D (q 0) (q 1) (q 2)) p j)
      (spatialHeightPower s A B C D (p 0) (p 1) (p 2)*s*(spatialLogD A B C D p j:ℂ)) (p j) := by
  unfold axisSlice
  fin_cases j
  · have h := hasDerivAt_logRatioPower s (hasDerivAt_const (p 0) (p 2))
      (quadraticHeightDenominator_hasDerivAt_x A B C D (p 0) (p 1) (p 2)) hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,heightLogDx] using h
  · have h := hasDerivAt_logRatioPower s (hasDerivAt_const (p 1) (p 2))
      (quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) (p 1) (p 2)) hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,heightLogDy] using h
  · have h := hasDerivAt_logRatioPower s (hasDerivAt_id (p 2))
      (quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) (p 2)) hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,heightLogDv] using h

lemma spatial_axis_hasDerivAt_deriv (s : ℂ) (A B C D : ℝ) (p : SpatialCoordinates) (j : Fin 3)
    (hv : p 2≠0) (hq : quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)≠0) :
    HasDerivAt (deriv (axisSlice (fun q => spatialHeightPower s A B C D (q 0) (q 1) (q 2)) p j))
      (spatialHeightPower s A B C D (p 0) (p 1) (p 2)*
        (s^2*(spatialLogD A B C D p j:ℂ)^2+s*(spatialLogDD A B C D p j:ℂ))) (p j) := by
  unfold axisSlice
  fin_cases j
  · have h := hasDerivAt_deriv_logRatioPower s (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D t (p 1) (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+B)) (p 0) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t (p 1) (p 2))
      (hasDerivAt_const (p 0) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 0)).const_mul A |>.add_const B).const_mul 2)
      hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,spatialLogDD,heightLogDx,heightLogDxx] using h
  · have h := hasDerivAt_deriv_logRatioPower s (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D (p 0) t (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+C)) (p 1) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) t (p 2))
      (hasDerivAt_const (p 1) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 1)).const_mul A |>.add_const C).const_mul 2)
      hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,spatialLogDD,heightLogDy,heightLogDyy] using h
  · have h := hasDerivAt_deriv_logRatioPower s (fun t => t)
      (fun t => quadraticHeightDenominator A B C D (p 0) (p 1) t) (fun _ => 1)
      (fun t => 2*A*t) (p 2) 0 (2*A)
      (fun t => hasDerivAt_id t)
      (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) t)
      (hasDerivAt_const (p 2) 1)
      (by simpa only [id_eq,mul_one] using (hasDerivAt_id (p 2)).const_mul (2*A))
      hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,spatialLogDD,heightLogDv,heightLogDvv,div_eq_mul_inv] using h

def rowSmoothPower (s : ℂ) (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℂ :=
  spatialHeightPower s (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2)

def rowLogD (u : Fin 2 → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ :=
  spatialLogD (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) p j

def rowLogDD (u : Fin 2 → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ :=
  spatialLogDD (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) p j

lemma row_denominator_pos (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) :
    0 < quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
      (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2) := by
  rw [← heightDenominator_eq_quadratic]
  exact heightDenominator_pos _ _ hv u hu

lemma rowLogD_bound (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    |rowLogD u p j| ≤ 1/(p 2) := by
  have h := heightLog_first_bounds _ _ _ _ (p 0) (p 1) (p 2)
    (complex_row_quadratic_relation (u 0) (u 1)) hv (row_denominator_pos u hu p hv).ne'
  fin_cases j <;> simp only [rowLogD,spatialLogD,]
  · exact h.1
  · exact h.2.1
  · exact h.2.2

lemma rowLogDD_bound (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    |rowLogDD u p j| ≤ 7/(p 2)^2 := by
  have h := heightLog_second_bounds _ _ _ _ (p 0) (p 1) (p 2)
    (complex_row_quadratic_relation (u 0) (u 1)) hv (Complex.normSq_nonneg _)
    (row_denominator_pos u hu p hv) (actual_quadraticHeight_nonneg u (p 0) (p 1) (p 2))
  fin_cases j <;> simp only [rowLogDD,spatialLogDD,]
  · exact h.1
  · exact h.2.1
  · exact h.2.2

lemma row_axis_hasDerivAt (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    HasDerivAt (axisSlice (rowSmoothPower s u) p j)
      (rowSmoothPower s u p*s*(rowLogD u p j:ℂ)) (p j) :=
  spatial_axis_hasDerivAt _ _ _ _ _ p j hv.ne' (row_denominator_pos u hu p hv).ne'

lemma row_axis_hasDerivAt_deriv (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    HasDerivAt (deriv (axisSlice (rowSmoothPower s u) p j))
      (rowSmoothPower s u p*(s^2*(rowLogD u p j:ℂ)^2+s*(rowLogDD u p j:ℂ))) (p j) :=
  spatial_axis_hasDerivAt_deriv _ _ _ _ _ p j hv.ne' (row_denominator_pos u hu p hv).ne'

end CubicEisenstein

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma hasDerivAt_deriv_tsum_of_bounds {ι : Type*} (f : ι → ℝ → ℂ)
    (M₁ M₂ : ι → ℝ) (U : Set ℝ) (x : ℝ)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hx : x ∈ U)
    (hM₁ : Summable M₁) (hM₂ : Summable M₂)
    (hfirst : ∀i y, y∈U → DifferentiableAt ℝ (f i) y)
    (hsecond : ∀i y, y∈U → DifferentiableAt ℝ (deriv (f i)) y)
    (hbound₁ : ∀i y, y∈U → ‖deriv (f i) y‖≤M₁ i)
    (hbound₂ : ∀i y, y∈U → ‖deriv (deriv (f i)) y‖≤M₂ i)
    (hsum : Summable (fun i => f i x)) :
    HasDerivAt (deriv (fun y => ∑'i,f i y)) (∑'i,deriv (deriv (f i)) x) x := by
  have hfirstSum (y : ℝ) (hy : y∈U) :=
    hasDerivAt_tsum_of_isPreconnected hM₁ hU hUc
      (fun i z hz => (hfirst i z hz).hasDerivAt) hbound₁ hx hsum hy
  have hsumFirst : Summable (fun i => deriv (f i) x) :=
    Summable.of_norm_bounded hM₁ (fun i => hbound₁ i x hx)
  have hsecondSum := hasDerivAt_tsum_of_isPreconnected hM₂ hU hUc
    (fun i z hz => (hsecond i z hz).hasDerivAt) hbound₂ hx hsumFirst hx
  apply hsecondSum.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact (hfirstSum y hy).deriv

lemma norm_row_axis_deriv (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (axisSlice (rowSmoothPower s u) p j) (p j)‖ ≤
      ‖rowSmoothPower s u p‖ * (‖s‖ * (1/(p 2))) := by
  rw [(row_axis_hasDerivAt s u hu p hv j).deriv,norm_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖rowSmoothPower s u p‖*‖s‖*(1/(p 2)) :=
      mul_le_mul_of_nonneg_left (rowLogD_bound u hu p hv j) (by positivity)
    _ = _ := by ring

lemma norm_row_axis_deriv2 (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (deriv (axisSlice (rowSmoothPower s u) p j)) (p j)‖ ≤
      ‖rowSmoothPower s u p‖ * (‖s‖^2 * (1/(p 2))^2 + ‖s‖ * (7/(p 2)^2)) := by
  rw [(row_axis_hasDerivAt_deriv s u hu p hv j).deriv,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ‖s^2*(rowLogD u p j:ℂ)^2‖+‖s*(rowLogDD u p j:ℂ)‖ := norm_add_le _ _
    _ = ‖s‖^2*|rowLogD u p j|^2 + ‖s‖*|rowLogDD u p j| := by
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ _ := by
      have hfirst := rowLogD_bound u hu p hv j
      have hsecond := rowLogDD_bound u hu p hv j
      gcongr

def smoothSummand (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates) : ℂ :=
  (cosetCharacter r)⁻¹ * rowSmoothPower s (embeddedRow r) p

lemma smoothSummand_eq_actual (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothSummand s r p =
      summand (upperSection ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv) s r := by
  rw [smoothSummand,← eigenfunction_summand_eq_actual_series]
  congr 1
  exact (actualHeightPower_eq_spatial s (embeddedRow r) (embeddedRow_ne_zero r)
    (p 0) (p 1) (p 2) hv).symm

lemma smooth_axis_differentiable (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice (smoothSummand s r) p j) (p j) :=
  ((row_axis_hasDerivAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).const_mul _).differentiableAt

lemma smooth_axis_deriv_differentiable (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (deriv (axisSlice (smoothSummand s r) p j)) (p j) := by
  change DifferentiableAt ℝ (deriv (fun t => (cosetCharacter r)⁻¹ *
    axisSlice (rowSmoothPower s (embeddedRow r)) p j t)) (p j)
  rw [deriv_const_mul_field']
  exact ((row_axis_hasDerivAt_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).const_mul _).differentiableAt

lemma norm_smooth_axis_deriv (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (axisSlice (smoothSummand s r) p j) (p j)‖ ≤
      ‖smoothSummand s r p‖ * (‖s‖ * (1/(p 2))) := by
  have h := norm_row_axis_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j
  unfold axisSlice at h ⊢
  simpa only [smoothSummand,deriv_const_mul_field,norm_mul,norm_inv,
    norm_cosetCharacter,inv_one,one_mul] using h

lemma norm_smooth_axis_deriv2 (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)‖ ≤
      ‖smoothSummand s r p‖ * (‖s‖^2 * (1/(p 2))^2 + ‖s‖ * (7/(p 2)^2)) := by
  have h := norm_row_axis_deriv2 s (embeddedRow r) (embeddedRow_ne_zero r) p hv j
  unfold axisSlice at h ⊢
  simpa only [smoothSummand,deriv_const_mul_field',deriv_const_mul_field,norm_mul,norm_inv,
    norm_cosetCharacter,inv_one,one_mul] using h

lemma smoothSummand_axis_update (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates)
    (j : Fin 3) (t : ℝ) :
    axisSlice (smoothSummand s r) (Function.update p j t) j =
      axisSlice (smoothSummand s r) p j := by
  funext z
  simp only [axisSlice,Function.update_idem]

end CubicEisenstein

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

def clampedCoordinates (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) : UpperCoordinates :=
  ⟨((p 0:ℂ)+(p 1:ℂ)*Complex.I,max deltaLoss (p 2)),lt_of_lt_of_le hδ (le_max_left _ _)⟩

lemma continuous_clampedCoordinates (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    Continuous (clampedCoordinates deltaLoss hδ) := by
  apply Continuous.subtype_mk
  exact ((Complex.continuous_ofReal.comp (continuous_apply 0)).add
    ((Complex.continuous_ofReal.comp (continuous_apply 1)).mul_const Complex.I)).prodMk
      (continuous_const.max (continuous_apply 2))

lemma continuous_axis_update (p : SpatialCoordinates) (j : Fin 3) :
    Continuous (fun t : ℝ => Function.update p j t) := by
  apply continuous_pi
  intro k
  by_cases h : k=j
  · subst k
    simp only [Function.update_self]
    fun_prop
  · simpa only [Function.update_of_ne h] using (continuous_const : Continuous (fun _ : ℝ => p k))

lemma smoothSummand_eq_clamped (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates)
    (deltaLoss : ℝ) (hδ : 0<deltaLoss) (hp : deltaLoss≤p 2) :
    smoothSummand s r p = summand (coordinateSection (clampedCoordinates deltaLoss hδ p)) s r := by
  have hv : 0<p 2 := lt_of_lt_of_le hδ hp
  simpa only [coordinateSection,clampedCoordinates,max_eq_right hp] using smoothSummand_eq_actual s r p hv

theorem axis_summable_derivative_bounds (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ∃ ε : ℝ, 0<ε ∧ ∃ M₀ M₁ M₂ : CuspCosets → ℝ,
      Summable M₀ ∧ Summable M₁ ∧ Summable M₂ ∧
      ∀ t ∈ Metric.ball (p j) ε,
        0 < (Function.update p j t) 2 ∧ ∀ r : CuspCosets,
        ‖axisSlice (smoothSummand s r) p j t‖≤M₀ r ∧
        ‖deriv (axisSlice (smoothSummand s r) p j) t‖≤M₁ r ∧
        ‖deriv (deriv (axisSlice (smoothSummand s r) p j)) t‖≤M₂ r := by
  let deltaLoss : ℝ := p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let path := fun t => clampedCoordinates deltaLoss hδ (Function.update p j t)
  have hpath : Continuous path := (continuous_clampedCoordinates deltaLoss hδ).comp (continuous_axis_update p j)
  let C := rowBound (coordinateSection (path (p j)))+1
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection (path (p j)))]
  have hb : ∀ᶠ t in 𝓝 (p j), rowBound (coordinateSection (path t))<C :=
    (continuous_coordinate_rowBound.comp hpath).continuousAt.eventually_lt_const (by dsimp [C]; linarith)
  have hh : ∀ᶠ t in 𝓝 (p j), deltaLoss < (Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    change deltaLoss < (Function.update p j (p j)) 2
    rw [Function.update_eq_self]
    dsimp [deltaLoss]
    linarith
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff_ball.mp (hh.and hb)
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C s.re s.re hC hs hs
  let c₁ := ‖s‖*(1/deltaLoss)
  let c₂ := ‖s‖^2*(1/deltaLoss)^2 + ‖s‖*(7/deltaLoss^2)
  refine ⟨ε,hε,M,fun r => M r*c₁,fun r => M r*c₂,hM,hM.mul_right _,hM.mul_right _,?_⟩
  intro t ht
  obtain ⟨hht,hbt⟩ := hball t ht
  have hpos : 0 < (Function.update p j t) 2 := lt_trans hδ hht
  refine ⟨hpos,fun r => ?_⟩
  have hm : ‖smoothSummand s r (Function.update p j t)‖≤M r := by
    rw [smoothSummand_eq_clamped s r _ deltaLoss hδ hht.le]
    exact hbound (path t,s) hbt.le le_rfl le_rfl r
  have hfrac : 1 / (Function.update p j t) 2 ≤ 1/deltaLoss := one_div_le_one_div_of_le hδ hht.le
  have hfrac₂ : 7 / ((Function.update p j t) 2)^2 ≤ 7/deltaLoss^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    nlinarith
  have hd₁ := norm_smooth_axis_deriv s r (Function.update p j t) hpos j
  have hd₂ := norm_smooth_axis_deriv2 s r (Function.update p j t) hpos j
  rw [smoothSummand_axis_update,Function.update_self] at hd₁ hd₂
  refine ⟨hm,hd₁.trans ?_,hd₂.trans ?_⟩
  · apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    exact mul_le_mul_of_nonneg_left hfrac (norm_nonneg s)
  · apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    dsimp [c₂]
    gcongr

lemma smooth_axis_differentiable_at (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) (hv : 0<(Function.update p j t) 2) :
    DifferentiableAt ℝ (axisSlice (smoothSummand s r) p j) t := by
  have h := smooth_axis_differentiable s r (Function.update p j t) hv j
  simpa only [smoothSummand_axis_update,Function.update_self] using h

lemma smooth_axis_deriv_differentiable_at (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) (hv : 0<(Function.update p j t) 2) :
    DifferentiableAt ℝ (deriv (axisSlice (smoothSummand s r) p j)) t := by
  have h := smooth_axis_deriv_differentiable s r (Function.update p j t) hv j
  simpa only [smoothSummand_axis_update,Function.update_self] using h

end CubicEisenstein

end

end OAI

end

