module

public import Green64.Library.Weights.SelectedOrdinaryQuotient

@[expose] public section

/-!
# Weights / LiteralPBandTwoCore

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## LiteralPBandTwoCore -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- All primality and group-disjointness premises are discharged for the
LITERAL original P bands, including SMALL and BIG groups. This applies
at every r>=1 (in particular r=6), every positive L, and every original
probe pattern and actual free marked list. -/
theorem b589_literal_P_both_ordinary_quotients434
    (r : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m)
    (w wp : ℕ) (hw : 0 < w) (hwp : 0 < wp)
    (a b : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (ha : a ∈ bigMarkLists (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (hb : b ∈ bigMarkLists (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp) :
    let P := sourceOriginalPAllActualBands r L
    let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ nu a
    let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ nu b
    (XB ∣ w ∧ 0 < w/XB ∧
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) w =
        sourceOriginalOrdinaryPart (Finset.univ.biUnion P) (w/XB)) ∧
    (XA ∣ wp ∧ 0 < wp/XA ∧
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) wp =
        sourceOriginalOrdinaryPart (Finset.univ.biUnion P) (wp/XA)) := by
  exact b589_actual_original_probe_both_ordinary_quotients434
    (sourceOriginalPAllActualBands r L)
    (source_original_P_all_actual_band_prime r L)
    (source_original_P_actual_all_disjoint r L hr hL)
    J ell m hmJ nu w wp hw hwp a b ha hb

/-- The TWO exact original native Q cores on their actual physical
marked endpoints cost only the two stripped quotient divisor squares.
This includes full D20, the genuine two independent QSkip Fourier arrays,
every allocation, original K supports, exact factorials and all characters.
It is a pointwise arithmetic input to the joint CRT moment, not RMS saving. -/
theorem b589_literal_P_original_two_core_stripped_bound434
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m)
    (w wp : ℕ) (hw : 0 < w) (hwp : 0 < wp)
    (a a' : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (ha : a ∈ bigMarkLists (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (ha' : a' ∈ bigMarkLists (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp)
    (b b' : Fin (d+1)) (slot slot' : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (δ' : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b' slot').length → Bool)
    (ξ' : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b' slot').length → ℝ)
    (K K' : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (q q' : ℕ) (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (σ₀ σ₁ σ₀' σ₁' : ℝ) :
    let P := sourceOriginalPAllActualBands r L
    let F := sourceNativePrimeCore r d L b slot δ ξ K
      (sourceNativeOriginalFullD20Alpha434 Δ W y) q χ σ₀ σ₁
    let F' := sourceNativePrimeCore r d L b' slot' δ' ξ' K'
      (sourceNativeOriginalFullD20Alpha434 Δ W y) q' χ' σ₀' σ₁'
    ‖primeSlotCoreValue P F w * star (primeSlotCoreValue P F' wp)‖ ≤
      ((w/sourceOriginalProbeFreeSourceX434 J ell m hmJ nu a).divisors.card : ℝ)^2 *
      ((wp/sourceOriginalProbeFreeTargetX434 J ell m hmJ nu a').divisors.card : ℝ)^2 := by
  dsimp only
  have hsource := b589_actual_original_source_Qcore_stripped434
    (sourceOriginalPAllActualBands r L)
    (source_original_P_all_actual_band_prime r L)
    (source_original_P_actual_all_disjoint r L hr hL)
    J ell m hmJ nu w hw a ha
    r d L hr hL b slot δ ξ K Δ W y hWy q χ σ₀ σ₁
  have htarget := b589_actual_original_target_Qcore_stripped434
    (sourceOriginalPAllActualBands r L)
    (source_original_P_all_actual_band_prime r L)
    (source_original_P_actual_all_disjoint r L hr hL)
    J ell m hmJ nu wp hwp a' ha'
    r d L hr hL b' slot' δ' ξ' K' Δ W y hWy q' χ' σ₀' σ₁'
  rw [norm_mul,norm_star]
  exact mul_le_mul hsource htarget (norm_nonneg _) (sq_nonneg _)
end Green64Analytic.ShiftTwoTerminal

end

end

