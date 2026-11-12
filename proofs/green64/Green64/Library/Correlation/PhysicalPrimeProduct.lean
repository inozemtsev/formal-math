module

public import Green64.Library.Analysis.Estimates.GhostPrimeFiber
public import Green64.Library.Weights.Part057

@[expose] public section

/-!
# Correlation / PhysicalPrimeProduct

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalPrimeProduct -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

private theorem filterFiniteSum
    {I U : Type} [DecidableEq I] (s : Finset I) (f : I → Multiset U)
    (p : U → Prop) [DecidablePred p] :
    (∑ i ∈ s,f i).filter p = ∑ i ∈ s,(f i).filter p := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha,Multiset.filter_add,ih,Finset.sum_insert ha]

private theorem mapFiniteSum
    {I U V : Type} [DecidableEq I] (s : Finset I) (f : I → Multiset U) (h : U → V) :
    (∑ i ∈ s,f i).map h = ∑ i ∈ s,(f i).map h := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha,Multiset.map_add,ih,Finset.sum_insert ha]

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- Exact labelled-prime product state in transported coordinates. -/
abbrev SourceOriginalPrimeReturnProductState434 :=
  (p : P) → SourceOriginalGhostReturnState434 (ZMod (modulus p))

def sourceOriginalPrimeProductPending434 (shift : ℤ)
    (s : SourceOriginalPrimeReturnProductState434 modulus) : Multiset (Atom P modulus) :=
  ∑ p,sourceOriginalOnePrimePending434 modulus p shift (s p)

def sourceOriginalPrimeProductSeen434
    (s : SourceOriginalPrimeReturnProductState434 modulus) : Finset P :=
  Finset.univ.filter (fun p => sourceOriginalOnePrimeSeen434 (s p)=true)

/-- Prime filtering of the actual multiset product recovers precisely
one coordinate; all other coordinates vanish, without a counting bound. -/
theorem source_original_PRIME_PRODUCT_pending_filter434
    (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus) (p : P) :
    (sourceOriginalPrimeProductPending434 modulus shift s).filter (fun z => z.1=p) =
      sourceOriginalOnePrimePending434 modulus p shift (s p) := by
  unfold sourceOriginalPrimeProductPending434
  rw [filterFiniteSum]
  rw [Finset.sum_eq_single p]
  · cases s p <;> simp [sourceOriginalOnePrimePending434]
  · intro q hq hqp
    cases s q <;> simp [sourceOriginalOnePrimePending434,hqp]
  · simp

theorem source_original_PRIME_PRODUCT_pending_finset_filter434
    (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus) (p : P) :
    ((sourceOriginalPrimeProductPending434 modulus shift s).toFinset.filter (fun z => z.1=p)) =
      (sourceOriginalOnePrimePending434 modulus p shift (s p)).toFinset := by
  have hh := congrArg Multiset.toFinset
    (source_original_PRIME_PRODUCT_pending_filter434 modulus shift s p)
  simpa only [Multiset.toFinset_filter] using hh

theorem source_original_PRIME_PRODUCT_zero_fiber434
    (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus) (p : P) :
    (((sourceOriginalPrimeProductPending434 modulus shift s).toFinset.filter
      (fun z => z.2=0)).filter (fun z => z.1=p)) =
      sourceOriginalOnePrimeZero434 modulus p shift (s p) := by
  have he : (((sourceOriginalPrimeProductPending434 modulus shift s).toFinset.filter
      (fun z => z.2=0)).filter (fun z => z.1=p)) =
      (((sourceOriginalPrimeProductPending434 modulus shift s).toFinset.filter
      (fun z => z.1=p)).filter (fun z => z.2=0)) := by
    ext z
    simp only [Finset.mem_filter]
    tauto
  rw [he,source_original_PRIME_PRODUCT_pending_finset_filter434]
  rfl

theorem source_original_PRIME_PRODUCT_seen_mem434
    (s : SourceOriginalPrimeReturnProductState434 modulus) (p : P) :
    p ∈ sourceOriginalPrimeProductSeen434 modulus s ↔ sourceOriginalOnePrimeSeen434 (s p)=true := by
  simp [sourceOriginalPrimeProductSeen434]

/-- The original integer translation acts coordinatewise on the
whole prime product, with exactly the accumulated physical shift. -/
theorem source_original_PRIME_PRODUCT_translate434
    (shift step : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus) :
    (sourceOriginalPrimeProductPending434 modulus shift s).map (translateAtom step) =
      sourceOriginalPrimeProductPending434 modulus (shift+step) s := by
  unfold sourceOriginalPrimeProductPending434
  rw [mapFiniteSum]
  apply Finset.sum_congr rfl
  intro p hp
  exact source_original_PHYSICAL_SINGLE_PRIME_translate434 modulus p shift step (s p)

/-- Literal G pending reconstruction is the sum of its prime-fibre
reconstructions. This is an equality for arbitrary old/deleted/born sets. -/
theorem source_original_GHOST_PIECE_prime_fiber_output434
    (old deleted : Finset (Atom P modulus)) (born : Finset P) :
    sourceOriginalGhostPiecePending434 modulus old deleted born =
      ∑ p,sourceOriginalGhostPiecePending434 modulus
        (old.filter (fun z => z.1=p)) (deleted.filter (fun z => z.1=p))
        (born.filter (fun t => t=p)) := by
  have he (p : P) : (old.filter (fun z => z.1=p)) \ (deleted.filter (fun z => z.1=p)) =
      (old \ deleted).filter (fun z => z.1=p) := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_sdiff]
    tauto
  unfold sourceOriginalGhostPiecePending434
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_fiberwise,Finset.sum_fiberwise]
end Green64Analytic.CorrelationSquare

end

end

