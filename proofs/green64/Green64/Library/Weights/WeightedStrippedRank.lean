module

public import Green64.Library.Weights.StrippedRankPair
public import Green64.Library.Weights.Part115

@[expose] public section

/-!
# Weights / WeightedStrippedRank

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## WeightedStrippedRank -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

/-- The actual two-global rank sum with independent endpoint tests. The
arithmetic weight and displacement are allowed their true auxiliary dependence. -/
def parityWeightedRankMain434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ)
    (N : Finset ℕ) (a : ℕ → ℕ → ℂ)
    (gate : ℕ → ℕ → Prop) [∀ w wp,Decidable (gate w wp)] : ℂ :=
  ∑ r ∈ parityCanonicalRankIndices434 m nu Q hA hB xi P V,
    parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
      (sourceOriginalProbeCellA434 m P V nu hA) (sourceOriginalProbeCellB434 m P V nu hB)
      r.1.2 r.2.2 (sourceOriginalProbeDA434 m nu aux) (sourceOriginalProbeDB434 m nu aux)
      (nu.1.card+nu.2.card) *
    (∑ w ∈ N,∑ wp ∈ N,if gate w wp then
      a w wp *
        (star (actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
          q V (parityFirstRankMark434 J ell m hmJ nu hB r.2.1 r.2.2) w) *
          actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
            q V (paritySecondRankMark434 J ell m hmJ nu hA r.1.1 r.1.2) wp)
      else 0)

/-- The original weighted collision correction with exactly the same
rank scalar, both reciprocal cell masses, arithmetic weight and displacement. -/
def parityWeightedRankCollision434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ)
    (N : Finset ℕ) (a : ℕ → ℕ → ℂ)
    (gate : ℕ → ℕ → Prop) [∀ w wp,Decidable (gate w wp)] : ℂ :=
  ∑ r ∈ parityCanonicalRankIndices434 m nu Q hA hB xi P V,
    parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
      (sourceOriginalProbeCellA434 m P V nu hA) (sourceOriginalProbeCellB434 m P V nu hB)
      r.1.2 r.2.2 (sourceOriginalProbeDA434 m nu aux) (sourceOriginalProbeDB434 m nu aux)
      (nu.1.card+nu.2.card) *
    (∑ w ∈ N,∑ wp ∈ N,if gate w wp then
      a w wp * parityFreeCollisionRankMarkedPair434 J ell m hmJ nu hA hB r P V aux q w wp
      else 0)

private theorem weighted_pair_rank_interchange
    {A B I : Type} [DecidableEq A] [DecidableEq B] [DecidableEq I]
    (s : Finset A) (t : Finset B) (R : Finset I)
    (z : A → B → ℂ) (c : I → ℂ) (f g : I → A → B → ℂ)
    (gate : A → B → Prop) [∀ a b,Decidable (gate a b)] :
    (∑ a ∈ s,∑ b ∈ t,if gate a b then z a b*(∑ i ∈ R,c i*(f i a b-g i a b)) else 0) =
    (∑ i ∈ R,c i*(∑ a ∈ s,∑ b ∈ t,if gate a b then z a b*f i a b else 0)) -
      (∑ i ∈ R,c i*(∑ a ∈ s,∑ b ∈ t,if gate a b then z a b*g i a b else 0)) := by
  have hp (a : A) (b : B) :
      (if gate a b then z a b*(∑ i ∈ R,c i*(f i a b-g i a b)) else 0) =
      ∑ i ∈ R,c i*((if gate a b then z a b*f i a b else 0) -
        (if gate a b then z a b*g i a b else 0)) := by
    by_cases h : gate a b
    · simp only [h,ite_true,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · simp [h]
  simp_rw [hp]
  have hs :
      (∑ a ∈ s,∑ b ∈ t,∑ i ∈ R,c i*((if gate a b then z a b*f i a b else 0) -
        (if gate a b then z a b*g i a b else 0))) =
      ∑ i ∈ R,∑ a ∈ s,∑ b ∈ t,c i*((if gate a b then z a b*f i a b else 0) -
        (if gate a b then z a b*g i a b else 0)) := by
    calc
      _ = ∑ a ∈ s,∑ i ∈ R,∑ b ∈ t,c i*((if gate a b then z a b*f i a b else 0) -
          (if gate a b then z a b*g i a b else 0)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  rw [hs,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [←Finset.mul_sum,Finset.sum_sub_distrib,mul_sub]

/-- The finite weighted equality is proved from the original stripped slice,
not used as a definition of that slice or of the two independent rank functionals. -/
theorem parity_weighted_stripped_rank_difference434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ)
    (N : Finset ℕ) (a : ℕ → ℕ → ℂ)
    (gate : ℕ → ℕ → Prop) [∀ w wp,Decidable (gate w wp)] :
    (∑ w ∈ N,∑ wp ∈ N,if gate w wp then
      a w wp*sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp
      else 0) =
    parityWeightedRankMain434 J ell m hmJ nu Q hA hB xi P V aux q N a gate -
      parityWeightedRankCollision434 J ell m hmJ nu Q hA hB xi P V aux q N a gate := by
  unfold parityWeightedRankMain434 parityWeightedRankCollision434
  simp_rw [parity_canonical_stripped_rank_difference434 J ell m hmJ nu Q hA hB xi P V aux q]
  exact weighted_pair_rank_interchange _ _ _ _ _ _ _ _
end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

/-- Exact r20 specialization for the original weighted Stripped construction.
Every actual auxiliary draw is retained. Only its scalar probability is
extracted; the original c-dependent arithmetic, cutoff and shift stay inside. -/
theorem parity_actual_weighted_stripped_rank_difference434
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
        parityWeightedRankCollision434 J 1 m hmJ fullnu Q h h xi P V fullaux (1/2) N a gate) := by
  dsimp only
  rw [←parity_weighted_stripped_rank_difference434]
  unfold parityActualWeightedStrippedComparison434
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wp hwp
  split_ifs <;> ring
end Green64Analytic.Parity

end

end

