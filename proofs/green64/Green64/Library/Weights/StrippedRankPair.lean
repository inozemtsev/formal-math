module

public import Green64.Library.Weights.Part046
public import Green64.Library.Weights.Part054

@[expose] public section

/-!
# Weights / StrippedRankPair

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## StrippedRankPair -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

/-- The two global cells and their original positive-conductor primitive characters. -/
abbrev ParityPrimitiveRankIndex434 (Q : ℕ) :=
  (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))) ×
    (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)))

/-- The genuine active-cell rank carrier, independent of every auxiliary draw. -/
def parityCanonicalRankIndices434 {G : Type} [Fintype G] [DecidableEq G]
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m) (Q : ℕ)
    (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ) :
    Finset (ParityPrimitiveRankIndex434 Q) :=
  (sourceOriginalProbeActiveCellsA434 m P V nu hA xi ×ˢ
    sourceOriginalActualPrimitiveCharacters434 Q) ×ˢ
  (sourceOriginalProbeActiveCellsB434 m P V nu hB xi ×ˢ
    sourceOriginalActualPrimitiveCharacters434 Q)

/-- Reindexing the already proved primitive expansion; both inverse cell masses
remain in the original rank scalar. No auxiliary ban has been removed. -/
theorem parity_canonical_Knu_indexed_rank434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    sourceOriginalProbeCanonicalKnu434 J ell m hmJ nu Q hA hB xi P V aux a b =
      ∑ r ∈ parityCanonicalRankIndices434 m nu Q hA hB xi P V,
        parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
          (sourceOriginalProbeCellA434 m P V nu hA) (sourceOriginalProbeCellB434 m P V nu hB)
          r.1.2 r.2.2 (sourceOriginalProbeDA434 m nu aux) (sourceOriginalProbeDB434 m nu aux)
          (nu.1.card+nu.2.card) *
        (star (parityFirstRankMark434 J ell m hmJ nu hB r.2.1 r.2.2 a) *
          paritySecondRankMark434 J ell m hmJ nu hA r.1.1 r.1.2 b) := by
  simpa only [sourceOriginalProbeCanonicalKnu434,parityCanonicalRankIndices434,
    Finset.sum_product,mul_assoc] using
    parity_actual_concrete_Knu_rank_expansion434 J ell m hmJ nu Q
      (sourceOriginalProbeActiveCellsA434 m P V nu hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V nu hB xi) hA hB P V aux a b

/-- The full marked rank pair with the literal free auxiliary exclusion. -/
def parityFreeBannedRankMarkedPair434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) : ℂ :=
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  bigMarkPrefactor P t q V w * bigMarkPrefactor P t q V wp *
    (∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,
      if sourceB574FreeAuxBan434 J ell m hmJ nu aux a b then
        star (parityFirstRankMark434 J ell m hmJ nu hB r.2.1 r.2.2 a) *
          paritySecondRankMark434 J ell m hmJ nu hA r.1.1 r.1.2 b
      else 0)

/-- The complementary collision contribution, defined on the same complete
ordered marked lists. A quantitative estimate is a separate obligation. -/
def parityFreeCollisionRankMarkedPair434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) : ℂ :=
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  bigMarkPrefactor P t q V w * bigMarkPrefactor P t q V wp *
    (∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,
      if sourceB574FreeAuxBan434 J ell m hmJ nu aux a b then 0
      else star (parityFirstRankMark434 J ell m hmJ nu hB r.2.1 r.2.2 a) *
        paritySecondRankMark434 J ell m hmJ nu hA r.1.1 r.1.2 b)

/-- Removing the free ban creates exactly the explicit collision term.
The resulting two endpoint tests contain no auxiliary parameter. -/
theorem parity_rank_pair_ban_partition434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) :
    parityFreeBannedRankMarkedPair434 J ell m hmJ nu hA hB r P V aux q w wp +
      parityFreeCollisionRankMarkedPair434 J ell m hmJ nu hA hB r P V aux q w wp =
    star (actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
      q V (parityFirstRankMark434 J ell m hmJ nu hB r.2.1 r.2.2) w) *
    actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
      q V (paritySecondRankMark434 J ell m hmJ nu hA r.1.1 r.1.2) wp := by
  rw [←parity_actual_rank_marked_pair434 J ell m hmJ nu hA hB r.1.1 r.2.1
    r.1.2 r.2.2 P V q w wp]
  unfold parityFreeBannedRankMarkedPair434 parityFreeCollisionRankMarkedPair434
  dsimp only
  rw [←mul_add]
  congr 1
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp

private theorem pair_rank_interchange
    {A B I : Type} [DecidableEq A] [DecidableEq B] [DecidableEq I]
    (s : Finset A) (t : Finset B) (R : Finset I)
    (p : ℂ) (c : I → ℂ) (f : I → A → B → ℂ)
    (gate : A → B → Prop) [∀ a b,Decidable (gate a b)] :
    p * (∑ a ∈ s,∑ b ∈ t,if gate a b then ∑ i ∈ R,c i*f i a b else 0) =
    ∑ i ∈ R,c i*(p*(∑ a ∈ s,∑ b ∈ t,if gate a b then f i a b else 0)) := by
  have hg (a : A) (b : B) :
      (if gate a b then ∑ i ∈ R,c i*f i a b else 0) =
      ∑ i ∈ R,c i*(if gate a b then f i a b else 0) := by
    by_cases h : gate a b <;> simp [h]
  simp_rw [hg]
  have hs :
      (∑ a ∈ s,∑ b ∈ t,∑ i ∈ R,c i*(if gate a b then f i a b else 0)) =
      ∑ i ∈ R,∑ a ∈ s,∑ b ∈ t,c i*(if gate a b then f i a b else 0) := by
    calc
      _ = ∑ a ∈ s,∑ i ∈ R,∑ b ∈ t,c i*(if gate a b then f i a b else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  rw [hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [←Finset.mul_sum]
  ring

/-- Exact rank expansion of the original stripped physical slice, including
the original free ban, all ordered marks and both damping/mass prefactors. -/
theorem parity_canonical_stripped_indexed_rank434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) :
    sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp =
      ∑ r ∈ parityCanonicalRankIndices434 m nu Q hA hB xi P V,
        parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
          (sourceOriginalProbeCellA434 m P V nu hA) (sourceOriginalProbeCellB434 m P V nu hB)
          r.1.2 r.2.2 (sourceOriginalProbeDA434 m nu aux) (sourceOriginalProbeDB434 m nu aux)
          (nu.1.card+nu.2.card) *
        parityFreeBannedRankMarkedPair434 J ell m hmJ nu hA hB r P V aux q w wp := by
  unfold sourceB574CanonicalStrippedSlice434 sourceB574CanonicalFreeKernel434
    parityFreeBannedRankMarkedPair434
  dsimp only
  simp_rw [parity_canonical_Knu_indexed_rank434 J ell m hmJ nu Q hA hB xi P V aux]
  exact pair_rank_interchange _ _ _ _ _ _ _

/-- Exact separation into auxiliary-independent endpoint products and an
explicit weighted collision correction; no vanishing/error premise. -/
theorem parity_canonical_stripped_rank_difference434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) :
    sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp =
      ∑ r ∈ parityCanonicalRankIndices434 m nu Q hA hB xi P V,
        parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
          (sourceOriginalProbeCellA434 m P V nu hA) (sourceOriginalProbeCellB434 m P V nu hB)
          r.1.2 r.2.2 (sourceOriginalProbeDA434 m nu aux) (sourceOriginalProbeDB434 m nu aux)
          (nu.1.card+nu.2.card) *
        (star (actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
          q V (parityFirstRankMark434 J ell m hmJ nu hB r.2.1 r.2.2) w) *
          actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
            q V (paritySecondRankMark434 J ell m hmJ nu hA r.1.1 r.1.2) wp -
          parityFreeCollisionRankMarkedPair434 J ell m hmJ nu hA hB r P V aux q w wp) := by
  rw [parity_canonical_stripped_indexed_rank434]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact eq_sub_of_add_eq (parity_rank_pair_ban_partition434 J ell m hmJ nu hA hB r P V aux q w wp)
end Green64Analytic.SourceBlockSieve

end

end

