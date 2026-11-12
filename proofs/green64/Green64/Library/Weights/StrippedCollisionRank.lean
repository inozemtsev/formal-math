module

public import Green64.Library.Weights.WeightedStrippedRank
public import Green64.Library.Weights.Part099

@[expose] public section

/-!
# Weights / StrippedCollisionRank

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## StrippedCollisionRank -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

private theorem sum_pair_rank_reorder
    {A B I : Type} [DecidableEq A] [DecidableEq B] [DecidableEq I]
    (s : Finset A) (t : Finset B) (R : Finset I) (f : A → B → I → ℂ) :
    (∑ a ∈ s,∑ b ∈ t,∑ i ∈ R,f a b i) =
      ∑ i ∈ R,∑ a ∈ s,∑ b ∈ t,f a b i := by
  calc
    _ = ∑ a ∈ s,∑ i ∈ R,∑ b ∈ t,f a b i := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

private theorem complementary_rank_sum
    {I : Type} [DecidableEq I] (R : Finset I) (c f : I → ℂ)
    (gate : Prop) [Decidable gate] :
    (if gate then 0 else ∑ i ∈ R,c i*f i) =
      ∑ i ∈ R,c i*(if gate then 0 else f i) := by
  by_cases h : gate <;> simp [h]

private theorem weighted_conditional_rank_sum
    {I : Type} [DecidableEq I] (R : Finset I) (c f : I → ℂ)
    (a : ℂ) (gate : Prop) [Decidable gate] :
    (if gate then a*(∑ i ∈ R,c i*f i) else 0) =
      ∑ i ∈ R,c i*(if gate then a*f i else 0) := by
  by_cases h : gate
  · simp only [h,ite_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp [h]

/-- The rank collision correction is exactly the independently constructed
literal bad-free canonical Knu slice, not a triangle estimate over ranks. -/
theorem parity_canonical_free_collision_indexed_rank434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) :
    parityCanonicalFreeCollisionSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp =
      ∑ r ∈ parityCanonicalRankIndices434 m nu Q hA hB xi P V,
        parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
          (sourceOriginalProbeCellA434 m P V nu hA) (sourceOriginalProbeCellB434 m P V nu hB)
          r.1.2 r.2.2 (sourceOriginalProbeDA434 m nu aux) (sourceOriginalProbeDB434 m nu aux)
          (nu.1.card+nu.2.card) *
        parityFreeCollisionRankMarkedPair434 J ell m hmJ nu hA hB r P V aux q w wp := by
  unfold parityCanonicalFreeCollisionSlice434 parityFreeCollisionRankMarkedPair434
  dsimp only
  simp_rw [parity_canonical_Knu_indexed_rank434 J ell m hmJ nu Q hA hB xi P V aux,
    complementary_rank_sum]
  rw [sum_pair_rank_reorder,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [←Finset.mul_sum]
  ring

/-- The full original unbanned kernel is exactly the product rank sum.
Original ordered marks, damping and both reciprocal cell masses are retained. -/
theorem parity_canonical_unbanned_indexed_rank434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) :
    b615OriginalUnbannedMarkedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp =
      ∑ r ∈ parityCanonicalRankIndices434 m nu Q hA hB xi P V,
        parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
          (sourceOriginalProbeCellA434 m P V nu hA) (sourceOriginalProbeCellB434 m P V nu hB)
          r.1.2 r.2.2 (sourceOriginalProbeDA434 m nu aux) (sourceOriginalProbeDB434 m nu aux)
          (nu.1.card+nu.2.card) *
        (star (actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
          q V (parityFirstRankMark434 J ell m hmJ nu hB r.2.1 r.2.2) w) *
          actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
            q V (paritySecondRankMark434 J ell m hmJ nu hA r.1.1 r.1.2) wp) := by
  rw [←parity_canonical_unbanned_collision_partition434,
    parity_canonical_stripped_indexed_rank434,parity_canonical_free_collision_indexed_rank434,
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [←mul_add,parity_rank_pair_ban_partition434]

/-- Exact weighted rank correction equals the original literal collision
functional. This permits estimating the original Knu before summing ranks. -/
theorem parity_weighted_rank_collision_literal434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ)
    (N : Finset ℕ) (a : ℕ → ℕ → ℂ)
    (gate : ℕ → ℕ → Prop) [∀ w wp,Decidable (gate w wp)] :
    parityWeightedRankCollision434 J ell m hmJ nu Q hA hB xi P V aux q N a gate =
      ∑ w ∈ N,∑ wp ∈ N,if gate w wp then
        a w wp*parityCanonicalFreeCollisionSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp
        else 0 := by
  symm
  unfold parityWeightedRankCollision434
  simp_rw [parity_canonical_free_collision_indexed_rank434 J ell m hmJ nu Q hA hB xi P V aux q,
    weighted_conditional_rank_sum]
  rw [sum_pair_rank_reorder]
  simp only [←Finset.mul_sum]

/-- The independently defined main rank functional equals the literal
unbanned marked kernel with unchanged arithmetic and signed guard. -/
theorem parity_weighted_rank_main_unbanned434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ)
    (N : Finset ℕ) (a : ℕ → ℕ → ℂ)
    (gate : ℕ → ℕ → Prop) [∀ w wp,Decidable (gate w wp)] :
    parityWeightedRankMain434 J ell m hmJ nu Q hA hB xi P V aux q N a gate =
      ∑ w ∈ N,∑ wp ∈ N,if gate w wp then
        a w wp*b615OriginalUnbannedMarkedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp
        else 0 := by
  symm
  unfold parityWeightedRankMain434
  simp_rw [parity_canonical_unbanned_indexed_rank434 J ell m hmJ nu Q hA hB xi P V aux q,
    weighted_conditional_rank_sum]
  rw [sum_pair_rank_reorder]
  simp only [←Finset.mul_sum]
end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

/-- Genuine r20 weighted Stripped comparison is the independent rank main
term minus the original literal weighted auxiliary collision, with full
auxiliary probability, c-dependent cutoff/phase and exact shift2*k*c. -/
theorem parity_actual_weighted_stripped_rank_literal_collision434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) :
    let c := parityActualProbeAuxD434 L J m hmJ nu aux
    let N := parityPositiveNaturalPositions434
      (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
    let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
    let P := b645ActualBand434 L hS
    let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
    let fullaux := parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
      (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)
    let a := parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c
    let gate := fun w wp : ℕ => (2*k) ≠ 0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ)
    parityActualWeightedStrippedComparison434 L hS J m hmJ nu Q h xi rho xi3 Ck Z k F G tw psi aux =
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
      (parityWeightedRankMain434 J 1 m hmJ fullnu Q h h xi P V fullaux (1/2) N a gate -
        (∑ w ∈ N,∑ wp ∈ N,if gate w wp then
          a w wp*parityCanonicalFreeCollisionSlice434 J 1 m hmJ fullnu Q h h xi P V fullaux (1/2) w wp
          else 0)) := by
  dsimp only
  rw [parity_actual_weighted_stripped_rank_difference434]
  rw [parity_weighted_rank_collision_literal434]
end Green64Analytic.Parity

end

end

