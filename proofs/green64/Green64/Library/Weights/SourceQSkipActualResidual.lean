module

public import Green64.Library.Weights.Part096
public import Mathlib

@[expose] public section

/-!
# Weights / SourceQSkipActualResidual

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceQSkipActualResidual -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
open Green64Analytic.QSkipFactorial
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- The literal sourceActualSortedQ/sourceEndpointFibre c(v), all original
labels, sorted scales, Boolean allocations, Fourier phases, prime multiplicity
collisions, and full (r!)^(-(d+1)) factorial. No squarefree assumption. -/
theorem source_actual_sorted_QSkip_residual_norm_le_one434
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (b : Fin (d+1)) (i : Fin r)
    (δ : Fin (sourceOrderedLabels r
      (sourceActualSortedScales r d L) b i).length → Bool)
    (ξ : Fin (sourceOrderedLabels r
      (sourceActualSortedScales r d L) b i).length → ℝ)
    (v : ℕ) :
    let n := (sourceOrderedLabels r
      (sourceActualSortedScales r d L) b i).length
    let Q := sourceActualSortedQ r d L b i
    let s := sourceActualSortedFrequencyScales r d L b i
    ‖sourceEndpointFibre
       (Finset.univ : Finset (OrderedQSkip n Q δ))
       orderedSkipProduct
       (fun a => sourceActualSortedFactorial r d *
         orderedSkipPhase s ξ a) v‖ ≤ 1 := by
  dsimp only
  let n := (sourceOrderedLabels r
    (sourceActualSortedScales r d L) b i).length
  let bands := sourceOriginalQActualBands r d L
  let band : Fin n → Fin (d+1) :=
    fun z => (sourceSortedLabelEquiv r
      (sourceActualSortedScales r d L) b i z).val.1
  let slot : Fin n → Fin r :=
    fun z => (sourceSortedLabelEquiv r
      (sourceActualSortedScales r d L) b i z).val.2
  have hprime : ∀ g p, p ∈ bands g → p.Prime := by
    intro g p hp
    exact sourceOriginalQActualBands_prime434 r d L g p hp
  have hdisj : ∀ g h p,
      p ∈ bands g → p ∈ bands h → g = h := by
    intro g h p hp hq
    exact source_original_Q_actual_all_disjoint434 r d L hr hL
      g h p hp hq
  have hlabel : Function.Injective (fun z : Fin n => (band z, slot z)) := by
    intro z w h
    apply (sourceSortedLabelEquiv r
      (sourceActualSortedScales r d L) b i).injective
    apply Subtype.ext
    exact h
  have hbound := original_ordered_QSkip_source_fibre_bound434
    r d n δ band slot bands hprime hdisj hlabel
    (sourceActualSortedFrequencyScales r d L b i) ξ v
  change
    ‖sourceEndpointFibre
       (Finset.univ : Finset (OrderedQSkip n
         (fun z => bands (band z)) δ))
       orderedSkipProduct
       (fun a => sourceActualSortedFactorial r d *
         orderedSkipPhase
           (sourceActualSortedFrequencyScales r d L b i) ξ a) v‖ ≤ 1
  exact hbound
end Green64Analytic.ShiftTwoTerminal

end

end

