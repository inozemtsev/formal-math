module

public import Green64.Library.Weights.Part054

@[expose] public section

/-!
# Weights / B26FullKernelTranspose

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26FullKernelTranspose -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option stderrAsMessages false

private theorem freed_swap
    {G : Type} [DecidableEq G] (J m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) :
    sourceOriginalProbeFreedSlots434 J m hmJ ν.swap g =
      sourceOriginalProbeFreedSlots434 J m hmJ ν g := by
  simp [sourceOriginalProbeFreedSlots434, or_comm]

/-- Exchange the roles of the two original probe blocks without
changing any labelled auxiliary prime or its physical freed slot. -/
noncomputable def sourceOriginalProbeSwapAux434
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (J m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν)) :
    SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν.swap) :=
  fun g i => aux g ⟨i.val, by
    have hi := i.property
    change i.val ∈ sourceOriginalProbeFreedSlots434 J m hmJ ν.swap g at hi
    change i.val ∈ sourceOriginalProbeFreedSlots434 J m hmJ ν g
    simpa only [freed_swap] using hi⟩

private theorem full_free_eval
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (s : ∀ g, Fin (J+ell) → {p : ℕ // p ∈ P g})
    (g : G) (j : Fin m) (hj : (g,j) ∈ ν.1 ∨ (g,j) ∈ ν.2) :
    sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν s g
      (sourceOriginalProbeFreeIndex434 J ell m hmJ ν g j hj) =
      (s g ((j.castLE hmJ).castAdd ell)).val := by
  simp [sourceOriginalProbeMemoryFreeValues434,
    sourceOriginalProbeMemoryFreeEquiv434, sourceOriginalProbeFreeIndex434]

private theorem full_target
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (s : ∀ g, Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν s) =
    sourceOriginalProbeOriginalTargetX434 J ell m hmJ ν
      (fun g i => (s g i).val) := by
  unfold sourceOriginalProbeFreeTargetX434 sourceOriginalProbeOriginalTargetX434
  apply Finset.prod_congr rfl
  intro z hz
  exact full_free_eval P J ell m hmJ ν s _ _ (Or.inl z.property)

private theorem full_source
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (s : ∀ g, Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν s) =
    sourceOriginalProbeOriginalSourceX434 J ell m hmJ ν
      (fun g i => (s g i).val) := by
  unfold sourceOriginalProbeFreeSourceX434 sourceOriginalProbeOriginalSourceX434
  apply Finset.prod_congr rfl
  intro z hz
  exact full_free_eval P J ell m hmJ ν s _ _ (Or.inr z.property)

/-- Exact endpoint roles of the actual Memory K: its first GLOBAL
uses the target A probes; its second uses the source B probes.
The endpoints are the full independently permuted J+ell lists. -/
theorem source_original_B26_full_K_endpoint_roles434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν))
    (s t : ∀ g, Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν Q hA hB xi aux s t =
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V ν hB xi) hA hB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      (sourceOriginalProbeDA434 m ν
        (sourceOriginalProbeMemoryAuxValues434 P J m hmJ ν aux))
      (sourceOriginalProbeOriginalTargetX434 J ell m hmJ ν (fun g i => (t g i).val))
      (sourceOriginalProbeDB434 m ν
        (sourceOriginalProbeMemoryAuxValues434 P J m hmJ ν aux))
      (sourceOriginalProbeOriginalSourceX434 J ell m hmJ ν (fun g i => (s g i).val))
      (ν.1.card+ν.2.card) := by
  simp only [sourceOriginalProbeMemoryCanonicalK434, sourceOriginalProbeCanonicalKnu434,
    sourceOriginalProbeConcreteKnu434, sourceAuxiliaryOriginalComparisonKnu434,
    sourceOriginalActualPrimitiveComparisonKernel434, full_target, full_source]

/-- Full K transpose exchanges the actual probe blocks, their
active cells, cell probabilities, widths, and auxiliary roles. -/
theorem source_original_B26_full_K_transpose434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν))
    (s t : ∀ g, Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν.swap Q hB hA xi
      (sourceOriginalProbeSwapAux434 P J m hmJ ν aux) s t =
    sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν Q hA hB xi aux t s := by
  rw [source_original_B26_full_K_endpoint_roles434,
    source_original_B26_full_K_endpoint_roles434]
  dsimp [sourceOriginalActualPrimitiveComparisonKernel434,
    sourceOriginalProbeActiveCellsA434, sourceOriginalProbeActiveCellsB434,
    sourceOriginalProbeCellA434, sourceOriginalProbeCellB434,
    sourceOriginalProbeDA434, sourceOriginalProbeDB434,
    sourceOriginalProbeMemoryAuxValues434, sourceOriginalProbeMemoryAuxSlot434,
    sourceOriginalProbeSwapAux434, sourceOriginalProbeOriginalTargetX434,
    sourceOriginalProbeOriginalSourceX434]
  change -((-1:ℂ)^(ν.2.card+ν.1.card)) * _ * _ = _
  rw [Nat.add_comm ν.2.card ν.1.card]
  unfold sourceOriginalProbeCellA434 sourceOriginalProbeCellB434
  rw [mul_right_comm]
  congr 2 <;> rfl

/-- The negative original edge conjugates the WHOLE transposed K
and both original phases, not only the RAW parity coefficient. -/
theorem source_original_B26_full_K_negative_orientation434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi ζ theta : ℝ) (D : ℕ) (k : ℤ)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν))
    (s t : ∀ g, Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    originalEdgeScalar
      (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν Q hA hB xi aux t s)
      ζ theta D (-1) k =
    star (originalEdgeScalar
      (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν.swap Q hB hA xi
        (sourceOriginalProbeSwapAux434 P J m hmJ ν aux) s t) ζ theta D 1 k) := by
  rw [source_original_B26_full_K_transpose434,
    source_original_edge_scalar_negative_conjugate434]

end Green64Analytic.CorrelationSquare

end

