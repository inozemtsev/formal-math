module

public import Green64.Library.Weights.LiteralPBandTwoCore
public import Green64.Library.Sieve.Foundations.StrippedCRTCount

@[expose] public section

/-!
# Weights / SelectedUnitGates

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualSelectedUnitGates -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 4000000

private theorem b596_selected_mark_positive_shift_unit
    {G I : Type} [Fintype G] [DecidableEq G] [Fintype I]
    (P : G → Finset ℕ) (t : G → ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (D w : ℕ) (k : ℤ) (hk : k ≠ 0) (hclean : D.Coprime w)
    (hlarge : ∀ g p, p ∈ P g → (2*k).natAbs < p)
    (a : ∀ g, Fin (t g) → ℕ) (ha : a ∈ bigMarkLists P t w)
    (e : I ↪ (Σ g : G, Fin (t g))) :
    (0 < ∏ z : I, a (e z).1 (e z).2) ∧
      (∏ z : I, a (e z).1 (e z).2).Coprime (2*k*(D:ℤ)).natAbs := by
  have hmem : ∀ g i, a g i ∈ P g := by
    intro g i
    have hg := Fintype.mem_piFinset.mp ha g
    have hi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 i
    exact (Finset.mem_filter.mp hi).1
  have hdvd : ∀ g i, a g i ∣ w := by
    intro g i
    have hg := Fintype.mem_piFinset.mp ha g
    have hi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 i
    exact (Finset.mem_filter.mp hi).2
  constructor
  · exact Finset.prod_pos (fun z hz => (hPrime _ _ (hmem _ _)).pos)
  · apply Nat.coprime_prod_left_iff.mpr
    intro z hz
    have hp := hPrime (e z).1 (a (e z).1 (e z).2) (hmem _ _)
    apply hp.coprime_iff_not_dvd.mpr
    intro hdiv
    have hmul : a (e z).1 (e z).2 ∣ (2*k).natAbs*D := by
      simpa only [Int.natAbs_mul,Int.natAbs_natCast] using hdiv
    rcases hp.dvd_mul.mp hmul with hsmall | hD
    · have hpos : 0 < (2*k).natAbs :=
        Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hk)
      exact (not_le_of_gt (hlarge _ _ (hmem _ _))) (Nat.le_of_dvd hpos hsmall)
    · have hg : a (e z).1 (e z).2 ∣ Nat.gcd D w := Nat.dvd_gcd hD (hdvd _ _)
      have he : Nat.gcd D w=1 := hclean
      rw [he] at hg
      exact hp.not_dvd_one hg

/-- For the literal original selected products, clean physical endpoints
and original large P primes imply every unit and positivity gate of B595.
The two products are not assumed coprime: this follows from their actual
opposite endpoints and the signed graph w'=w+2kD. Negative k is retained. -/
theorem b596_literal_selected_positive_shift_units434
    (r : ℕ) (L : ℝ) (hr : 1≤ r) (hL : 0<L)
    (J ell m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m)
    (D w wp : ℕ) (k : ℤ) (hk : k≠0)
    (hw : 0<w) (hwp : 0<wp)
    (hclean : D.Coprime w) (hclean' : D.Coprime wp)
    (hgraph : (wp:ℤ)=(w:ℤ)+2*k*(D:ℤ))
    (hlarge : ∀ g p, p∈sourceOriginalPAllActualBands r L g → (2*k).natAbs<p)
    (a b : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (ha : a∈bigMarkLists (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (hb : b∈bigMarkLists (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp) :
    let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ nu a
    let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ nu b
    0<XA ∧ 0<XB ∧ XA.Coprime XB ∧
      XA.Coprime (2*k*(D:ℤ)).natAbs ∧ XB.Coprime (2*k*(D:ℤ)).natAbs := by
  dsimp only
  have hs := b596_selected_mark_positive_shift_unit
    (sourceOriginalPAllActualBands r L)
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
    (source_original_P_all_actual_band_prime r L)
    D w k hk hclean hlarge a ha
    (sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ nu)
  have ht := b596_selected_mark_positive_shift_unit
    (sourceOriginalPAllActualBands r L)
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
    (source_original_P_all_actual_band_prime r L)
    D wp k hk hclean' hlarge b hb
    (sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ nu)
  have hdiv := b589_literal_P_both_ordinary_quotients434
    r L hr hL J ell m hmJ nu w wp hw hwp a b ha hb
  refine ⟨ht.1,hs.1,?_,ht.2,hs.2⟩
  have htarget :
      ((sourceOriginalProbeFreeTargetX434 J ell m hmJ nu b):ℤ) ∣
        (w:ℤ)+2*k*(D:ℤ) := by
    rw [←hgraph]
    exact Int.natCast_dvd_natCast.mpr hdiv.2.1
  have hunit := b587_actual_stripped_quotient_unit434
    (sourceOriginalProbeFreeTargetX434 J ell m hmJ nu b) 1 D w k
    (one_dvd w) ht.2 htarget
  have hunit' : (sourceOriginalProbeFreeTargetX434 J ell m hmJ nu b).Coprime w := by
    simpa only [Nat.div_one] using hunit
  exact Nat.Coprime.of_dvd_right hdiv.1.1 hunit'
end Green64Analytic.ShiftTwoTerminal

end

end

