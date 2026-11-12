module

public import Green64.Library.Analysis.Estimates.HarmonicLift
public import Green64.Library.Weights.SelectedUnitGates
public import Green64.Library.Analysis.Estimates.Part010

@[expose] public section

/-!
# Weights / FullBanSelectedUnits

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## FullBanSelectedUnits -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6000000

private theorem b601_aux_membership
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (haux : aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P)) :
    ∀ z, aux z ∈ P (sourceOriginalProbeAuxGroup434 m nu z) := by
  intro z
  have hz := Fintype.mem_piFinset.mp haux z
  cases z <;> exact hz

/-- The complete original auxiliary product is positive, with every
label and numerical repetition retained. -/
theorem b601_original_aux_positive434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (haux : aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P)) :
    0 < sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux := by
  rw [←source_original_probe_aux_product_split434]
  exact Finset.prod_pos (fun z _ =>
    (hPrime _ _ (b601_aux_membership P m nu aux haux z)).pos)

private theorem b601_banned_mark_coprime
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (haux : aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P))
    (w : ℕ)
    (a : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (ha : a ∈ bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (hban : ∀ z i, aux z ≠ a (sourceOriginalProbeAuxGroup434 m nu z) i) :
    ∀ g i, (a g i).Coprime
      (sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux) := by
  have hamem : ∀ g i, a g i ∈ P g := by
    intro g i
    exact (Finset.mem_filter.mp
      (Fintype.mem_piFinset.mp (Finset.mem_filter.mp
        (Fintype.mem_piFinset.mp ha g)).1 i)).1
  have hauxmem := b601_aux_membership P m nu aux haux
  intro g i
  rw [←source_original_probe_aux_product_split434]
  apply Nat.coprime_prod_right_iff.mpr
  intro z hz
  have hp := hPrime g (a g i) (hamem g i)
  have hq := hPrime _ (aux z) (hauxmem z)
  have hne : aux z ≠ a g i := by
    intro he
    have hgroup : sourceOriginalProbeAuxGroup434 m nu z = g :=
      hDisj _ _ (aux z) (hauxmem z) (he.symm ▸ hamem g i)
    subst g
    exact hban z i he
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  rcases (Nat.dvd_prime hq).mp hd with hone | he
  · exact hp.ne_one hone
  · exact hne he.symm

/-- The FULL actual ban implies coprimality of EVERY original free mark
with the complete auxiliary product. The endpoints themselves may be
dirty. Disjoint P groups are used before reducing to the same-group ban. -/
theorem b601_original_full_ban_marks_coprime434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (haux : aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P))
    (w wp : ℕ)
    (a b : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (ha : a ∈ bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (hb : b ∈ bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp)
    (hban : sourceB574FreeAuxBan434 J ell m hmJ nu aux a b) :
    let D := sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux
    (∀ g i, (a g i).Coprime D) ∧ (∀ g i, (b g i).Coprime D) := by
  dsimp only
  constructor
  · exact b601_banned_mark_coprime P hPrime hDisj J ell m hmJ nu aux haux
      w a ha (fun z i => (hban z i).1)
  · exact b601_banned_mark_coprime P hPrime hDisj J ell m hmJ nu aux haux
      wp b hb (fun z i => (hban z i).2)

private theorem b601_selected_shift_unit
    {G I : Type} [Fintype G] [DecidableEq G] [Fintype I]
    (P : G → Finset ℕ) (t : G → ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (D w : ℕ) (k : ℤ) (hk : k ≠ 0)
    (hlarge : ∀ g p, p ∈ P g → (2*k).natAbs < p)
    (a : ∀ g, Fin (t g) → ℕ) (ha : a ∈ bigMarkLists P t w)
    (hunit : ∀ g i, (a g i).Coprime D)
    (e : I ↪ (Σ g : G, Fin (t g))) :
    (0 < ∏ z : I, a (e z).1 (e z).2) ∧
      (∏ z : I, a (e z).1 (e z).2).Coprime (2*k*(D:ℤ)).natAbs := by
  have hmem : ∀ g i, a g i ∈ P g := by
    intro g i
    exact (Finset.mem_filter.mp
      (Fintype.mem_piFinset.mp (Finset.mem_filter.mp
        (Fintype.mem_piFinset.mp ha g)).1 i)).1
  constructor
  · exact Finset.prod_pos (fun z _ => (hPrime _ _ (hmem _ _)).pos)
  · apply Nat.coprime_prod_left_iff.mpr
    intro z hz
    have hp := hPrime (e z).1 (a (e z).1 (e z).2) (hmem _ _)
    have hkunit : (a (e z).1 (e z).2).Coprime (2*k).natAbs := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hd
      have hpos : 0 < (2*k).natAbs :=
        Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hk)
      exact (not_le_of_gt (hlarge _ _ (hmem _ _))) (Nat.le_of_dvd hpos hd)
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      hkunit.mul_right (hunit (e z).1 (e z).2)

/-- Actual full-ban selected positivity and all three unit gates.
No gcd(D,w) or gcd(D,w') assumption is imposed. Original auxiliaries,
free arrays, selected embeddings and signed physical shift are literal. -/
theorem b601_literal_full_ban_selected_units434
    (r : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (haux : aux ∈ Fintype.piFinset
      (sourceOriginalProbeAuxPrimeSets434 m nu (sourceOriginalPAllActualBands r L)))
    (D w wp : ℕ)
    (hD : D = sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux)
    (k : ℤ) (hk : k ≠ 0) (hw : 0 < w) (hwp : 0 < wp)
    (hgraph : (wp:ℤ) = (w:ℤ) + 2*k*(D:ℤ))
    (hlarge : ∀ g p, p ∈ sourceOriginalPAllActualBands r L g → (2*k).natAbs < p)
    (a b : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (ha : a ∈ bigMarkLists (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (hb : b ∈ bigMarkLists (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp)
    (hban : sourceB574FreeAuxBan434 J ell m hmJ nu aux a b) :
    let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ nu a
    let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ nu b
    0 < XA ∧ 0 < XB ∧ XA.Coprime XB ∧
      XA.Coprime (2*k*(D:ℤ)).natAbs ∧ XB.Coprime (2*k*(D:ℤ)).natAbs := by
  have hu := b601_original_full_ban_marks_coprime434
    (sourceOriginalPAllActualBands r L)
    (source_original_P_all_actual_band_prime r L)
    (source_original_P_actual_all_disjoint r L hr hL)
    J ell m hmJ nu aux haux w wp a b ha hb hban
  rw [←hD] at hu
  have hs := b601_selected_shift_unit
    (sourceOriginalPAllActualBands r L)
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
    (source_original_P_all_actual_band_prime r L)
    D w k hk hlarge a ha hu.1
    (sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ nu)
  have ht := b601_selected_shift_unit
    (sourceOriginalPAllActualBands r L)
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
    (source_original_P_all_actual_band_prime r L)
    D wp k hk hlarge b hb hu.2
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

