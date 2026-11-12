module

public import Green64.Library.Sieve.Foundations.Part008
public import Green64.Library.Weights.Part106
public import Green64.Library.Sieve.Foundations.Part005
public import Green64.Library.Weights.Part003
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section

/-!
# Weights / Part117

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SmoothAllocationTailCapacity -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 35000

/-- Parity(4.4) terminal lemma, derived from the genuine SOURCE B590 smooth
f0/f1 support. For the LAST skipped slot j, all later Q primes belong
to e; the tail-capacity budget removes its remaining logarithmic debt.
The two assumptions are explicit finite original Q-slot geometry:
  total ordinary Q log >= log E;
  log p_j + s_j - log(total after j) <= B for every skipped j.
They are NOT hidden in a new smooth gate. Full literal moving-Q band
arithmetic must discharge these conditions to obtain Parity(4.5). -/
theorem parity_smooth_Q_allocation_terminal_residual_le_of_tail434
    {n : ℕ} (r : ℕ) (E B : ℝ)
    (scales : Fin n → ℝ) (delta : Fin n → Bool) (p : Fin n → ℕ)
    (hScales : ∀ i, 0 < scales i)
    (hWeight : parityOriginalQAllocationBranchWeight434 r E scales delta p ≠ 0)
    (hB : 0 ≤ B)
    (hTotal : Real.log E ≤ ∑ i : Fin n, Real.log (p i : ℝ))
    (hTail : ∀ j : Fin n, delta j = false →
        Real.log (p j : ℝ) + scales j ≤ B +
          ∑ i ∈ (Finset.univ.filter (fun i : Fin n => j < i)),
            Real.log (p i : ℝ)) :
    Real.log E - (∑ i : Fin n,
      if delta i then Real.log (p i : ℝ) else 0) ≤ B := by
  let S : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => delta i = false)
  rcases S.eq_empty_or_nonempty with hEmpty | hNonempty
  · have hAll : ∀ i : Fin n, delta i = true := by
      intro i
      cases h : delta i with
      | true => rfl
      | false =>
          have hi : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i,h⟩
          rw [hEmpty] at hi
          simp at hi
    have hSum : (∑ i : Fin n, if delta i then Real.log (p i : ℝ) else 0) =
        ∑ i : Fin n, Real.log (p i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hAll i]
    rw [hSum]
    linarith
  · let j := S.max' hNonempty
    have hj : j ∈ S := Finset.max'_mem S hNonempty
    have hjFalse : delta j = false := (Finset.mem_filter.mp hj).2
    have hLater : ∀ i : Fin n, j < i → delta i = true := by
      intro i hji
      cases h : delta i with
      | true => rfl
      | false =>
          have hi : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i,h⟩
          have hle : i ≤ j := Finset.le_max' S i hi
          exact False.elim ((not_lt_of_ge hle) hji)
    let f : Fin n → ℝ := fun i => if delta i then Real.log (p i : ℝ) else 0
    have hPart := parity_original_sorted_Q_slot_sum_before_at_after434 j f
    have hjZero : f j = 0 := by simp [f,hjFalse]
    have hLaterEq :
        (∑ i ∈ (Finset.univ.filter (fun i : Fin n => j < i)), f i) =
        ∑ i ∈ (Finset.univ.filter (fun i : Fin n => j < i)),
          Real.log (p i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [f,hLater i (Finset.mem_filter.mp hi).2]
    simp only [hjZero, add_zero, hLaterEq] at hPart
    have hSlot := parity_original_Q_smooth_positive_skip_slot_budget434
      r E scales delta p hScales hWeight j hjFalse
    have hSuffix := hTail j hjFalse
    unfold parityOriginalQAllocationResidual434 at hSlot
    change Real.log E - (∑ i : Fin n, f i) ≤ B
    linarith

/-- Parity(4.5) LOWER bound as a theorem about the actual positive smooth
allocation branch and its exact selected e-product, with precisely the
remaining Q-prime tail geometry made explicit. It uses the original B590
weight, total Q capacity and suffix source supply; it does NOT assume the
inequality e >= E*exp(-B) being proved. -/
theorem parity_smooth_Q_allocation_e_lower_of_tail434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (r : ℕ) (E B : ℝ)
    (scales : Fin n → ℝ) (delta : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i})
    (hE : 0 < E) (hB : 0 ≤ B)
    (hScales : ∀ i, 0 < scales i)
    (hP : ∀ i, 0 < (p i).val)
    (hWeight : parityOriginalQAllocationBranchWeight434 r E scales delta
      (fun i => (p i).val) ≠ 0)
    (hTotal : Real.log E ≤ ∑ i : Fin n, Real.log ((p i).val : ℝ))
    (hTail : ∀ j : Fin n, delta j = false →
      Real.log ((p j).val : ℝ) + scales j ≤ B +
        ∑ i ∈ (Finset.univ.filter (fun i : Fin n => j < i)),
          Real.log ((p i).val : ℝ)) :
    E*Real.exp (-B) ≤ (paritySourceOrderedAllocatedE434 delta p : ℝ) := by
  have hSelected := parity_original_Q_allocation_log_selected_e434 delta p hP
  rw [Finset.sum_filter] at hSelected
  have hResidual := parity_smooth_Q_allocation_terminal_residual_le_of_tail434
    r E B scales delta (fun i => (p i).val) hScales hWeight hB hTotal hTail
  rw [←hSelected] at hResidual
  have hPos : 0 < (paritySourceOrderedAllocatedE434 delta p : ℝ) := by
    unfold paritySourceOrderedAllocatedE434
    push_cast
    apply Finset.prod_pos
    intro i hi
    by_cases hs : delta i = true
    · simpa [hs] using (show (0 : ℝ) < (p i).val from Nat.cast_pos.mpr (hP i))
    · simp [hs]
  calc
    E*Real.exp (-B) = Real.exp (Real.log E-B) := by
      rw [Real.exp_sub,Real.exp_log hE,Real.exp_neg]
      ring
    _ ≤ Real.exp (Real.log (paritySourceOrderedAllocatedE434 delta p : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = (paritySourceOrderedAllocatedE434 delta p : ℝ) := Real.exp_log hPos
end Green64Analytic.Parity

end

end

/-! ## ActualQTerminalScale -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 30000

/-- Real source dyadic exact halving at r0=20, including depth d=0.
The original Q_j scale is NOT replaced by a proxy logarithmic scale. -/
theorem parity_original_Q_scale_double_next434 (L : ℝ) (d : ℕ) :
    sourceOriginalPGroupScale 20 L d =
      2*sourceOriginalPGroupScale 20 L (d+1) := by
  unfold sourceOriginalPGroupScale
  rw [pow_succ]
  field_simp
  <;> ring

/-- ACTUAL original moving Q-depth maximality, rather than arbitrary
admissibility, forces terminal Q scale strictly below 40 log L.
This is the missing quantitative input needed for Parity(4.5) with Cs>88.
The threshold is uniform in the original unbounded moving Q-depth d. -/
theorem parity_eventually_actual_last_Q_scale_log_cap434 :
    ∀ᶠ L : ℝ in atTop,
      sourceOriginalPGroupScale 20 L
        (sourceOriginalLiteralDepth 20 L) < 40*Real.log L := by
  filter_upwards [source_original_literal_depth_properties_eventually 20 (by norm_num)]
    with L hDepth
  let d := sourceOriginalLiteralDepth 20 L
  have hNot : ¬sourceOriginalDepthAdmissible 20 (d+1) L := by
    intro hadd
    have hle := hDepth.2 (d+1) hadd
    omega
  have hS : sourceOriginalPGroupScale 20 L (d+1) < 20*Real.log L := by
    have hn : ¬ (20*Real.log L ≤
      sourceOriginalQActualExponent 20 (d+1)*L) := by
      simpa only [sourceOriginalDepthAdmissible,sourceOriginalQActualExponent,
        sourceOriginalQ0Scale] using hNot
    have hs := source_original_Q_actual_scale_eq_P_scale 20 (d+1) L (by norm_num)
    rw [hs] at hn
    exact lt_of_not_ge hn
  have hDouble := parity_original_Q_scale_double_next434 L d
  rw [hDouble]
  linarith
end Green64Analytic.Parity

end

end

/-! ## ActualQTerminalPrimeCost -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

/-- Actual literal moving-last Q band, every original prime p, pays
`log p + s_last < 88 log L`, from the pinned source Q upper endpoint
6/5*s_last and MAXIMAL original depth s_last<40logL. No assumed
terminal scale estimate, and no loss of any original last-band primes. -/
theorem parity_eventually_actual_last_Q_prime_skip_cost_log434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ p : ℕ,
        p ∈ sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L
          ⟨sourceOriginalLiteralDepth 20 L, by omega⟩ →
        Real.log (p : ℝ) +
          sourceOriginalPGroupScale 20 L (sourceOriginalLiteralDepth 20 L) <
            88*Real.log L := by
  filter_upwards [parity_eventually_actual_last_Q_scale_log_cap434] with L hTerm
  intro p hp
  let d := sourceOriginalLiteralDepth 20 L
  let j : Fin (d+1) := ⟨d,by omega⟩
  have hPrime : Nat.Prime p := source_original_Q_actual_prime 20 d L j p hp
  have hRange := (source_original_Q_actual_prime_range 20 d L
    (by norm_num) j p hp).2
  have hLog : Real.log (p:ℝ) ≤
      (6/5:ℝ)*sourceOriginalPGroupScale 20 L d := by
    exact (Real.log_le_iff_le_exp (by exact_mod_cast hPrime.pos)).mpr hRange
  linarith
end Green64Analytic.Parity

end

end

/-! ## ActualQSortedOrder -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 30000

/-- Source scales strictly decrease in actual increasing Q-band index. -/
theorem parity_actual_Q_scale_strict_antitone434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (a b : Fin (d+1)) (hab : a < b) :
    sourceActualSortedScales 20 d L b < sourceActualSortedScales 20 d L a := by
  change sourceOriginalPGroupScale 20 L b.val <
    sourceOriginalPGroupScale 20 L a.val
  have hSep := source_original_P_actual_scale_dyadic_separation 20 a.val b.val L
    (by norm_num) hL (by exact_mod_cast hab)
  have hp := source_original_positive_dyadic_scale 20 b.val L (by norm_num) hL
  linarith

/-- ACTUAL sourceQ list mergeSort comparator agrees with lexicographic
INCREASING band then mark index. Thus source actual Q labels are truly
ordered by increasing band, not merely a model-imposed assumption. -/
theorem parity_actual_Q_sorted_comparator_lex434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (a b : Fin (d+1) × Fin 20) :
    (decide (sourceActualSortedScales 20 d L b.1 <
      sourceActualSortedScales 20 d L a.1 ∨
      sourceActualSortedScales 20 d L b.1 =
        sourceActualSortedScales 20 d L a.1 ∧ a.2 ≤ b.2) = true) ↔
      a.1 < b.1 ∨ (a.1=b.1 ∧ a.2 ≤ b.2) := by
  simp only [decide_eq_true_eq]
  rcases lt_trichotomy a.1 b.1 with hLess | hEq | hGreater
  · have hs := parity_actual_Q_scale_strict_antitone434 d L hL a.1 b.1 hLess
    simp [hLess,hs,ne_of_lt hs]
  · have hs : sourceActualSortedScales 20 d L b.1 =
      sourceActualSortedScales 20 d L a.1 := congrArg _ hEq.symm
    simp [hEq,hs]
  · have hs := parity_actual_Q_scale_strict_antitone434 d L hL b.1 a.1 hGreater
    have hNotScale : ¬ (sourceActualSortedScales 20 d L b.1 <
      sourceActualSortedScales 20 d L a.1) := not_lt_of_ge hs.le
    have hNotBand : a.1 ≠ b.1 := ne_of_gt hGreater
    have hNotEqScale : sourceActualSortedScales 20 d L b.1 ≠
      sourceActualSortedScales 20 d L a.1 := ne_of_gt hs
    have hNotLess : ¬ a.1 < b.1 := not_lt_of_ge hGreater.le
    simp [hNotScale,hNotEqScale,hNotBand,hNotLess]

/-- Source `sourceOrderedLabels` is genuinely pairwise sorted in the
original 20-slot (moving d+1)-band system; no unproved order hypothesis. -/
theorem parity_actual_Q_ordered_labels_pairwise434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20) :
    List.Pairwise (fun a b : Fin (d+1) × Fin 20 =>
      a.1 < b.1 ∨ (a.1=b.1 ∧ a.2 ≤ b.2))
      (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot) := by
  let s := sourceActualSortedScales 20 d L
  let cmp : Fin (d+1) × Fin 20 → Fin (d+1) × Fin 20 → Bool :=
    fun a b => decide (s b.1 < s a.1 ∨ s b.1 = s a.1 ∧ a.2 ≤ b.2)
  have hCmp (a b : Fin (d+1) × Fin 20) :
      cmp a b = true ↔ a.1 < b.1 ∨ (a.1=b.1 ∧ a.2 ≤ b.2) :=
    parity_actual_Q_sorted_comparator_lex434 d L hL a b
  have hTrans : ∀ (a b c : Fin (d+1) × Fin 20),
      cmp a b = true → cmp b c = true → cmp a c = true := by
    intro a b c hab hbc
    apply (hCmp a c).2
    rcases (hCmp a b).1 hab with hab | ⟨hab,hmarkAB⟩
    · rcases (hCmp b c).1 hbc with hbc | ⟨hbc,hmarkBC⟩
      · exact Or.inl (lt_trans hab hbc)
      · exact Or.inl (by simpa [← hbc] using hab)
    · rcases (hCmp b c).1 hbc with hbc | ⟨hbc,hmarkBC⟩
      · exact Or.inl (by simpa [hab] using hbc)
      · exact Or.inr ⟨hab.trans hbc, by simpa using hmarkAB.trans hmarkBC⟩
  have hTotal : ∀ (a b : Fin (d+1) × Fin 20),
      (cmp a b || cmp b a) = true := by
    intro a b
    rw [Bool.or_eq_true]
    rcases lt_trichotomy a.1 b.1 with hab | heq | hba
    · exact Or.inl ((hCmp a b).2 (Or.inl hab))
    · rcases le_total a.2 b.2 with hmark | hmark
      · exact Or.inl ((hCmp a b).2 (Or.inr ⟨heq,hmark⟩))
      · exact Or.inr ((hCmp b a).2 (Or.inr ⟨heq.symm,hmark⟩))
    · exact Or.inr ((hCmp b a).2 (Or.inl hba))
  have hSorted := List.pairwise_mergeSort hTrans hTotal
    ((Finset.univ.erase (band,slot)).toList)
  change List.Pairwise (fun a b : Fin (d+1) × Fin 20 =>
      a.1 < b.1 ∨ (a.1=b.1 ∧ a.2 ≤ b.2))
      ((Finset.univ.erase (band,slot)).toList.mergeSort cmp)
  apply hSorted.imp
  intro a b hab
  exact (hCmp a b).1 hab

/-- The exact original sourceSortedLabelEquiv (not merely an abstract
sorted list) has nondecreasing natural Q-band labels as Fin index grows. -/
theorem parity_actual_Q_ordered_band_nondecreasing434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (i j : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length) (hij : i < j) :
    ((sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
      band slot i).val.1) ≤
      ((sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
      band slot j).val.1) := by
  have hPair := parity_actual_Q_ordered_labels_pairwise434 d L hL band slot
  have hGet := (List.pairwise_iff_get.mp hPair) i j hij
  rcases hGet with hlt | ⟨heq,hidx⟩
  · change ((sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).get i).1 ≤
      ((sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).get j).1
    exact le_of_lt hlt
  · change ((sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).get i).1 ≤
      ((sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).get j).1
    exact le_of_eq heq
end Green64Analytic.Parity

end

end

/-! ## ActualQNextBandSlots -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 32000

/-- Source sorted-position of an original Q-band mark, with only the
actual reserved mark omitted. Using the 19 marks `m != slot` avoids any
special-case assumption on the reserved BAND. -/
noncomputable def parity_actual_Q_unreserved_other_mark_index434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (laterBand : Fin (d+1)) (m : {m : Fin 20 // m ≠ slot}) :
    Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length :=
  (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L) band slot).symm
    ⟨(laterBand,m.val), by
      intro hEq
      exact m.property (congrArg Prod.snd hEq)⟩

/-- The actual position found by the inverse original source label
equivalence has precisely the requested band and original mark. -/
theorem parity_actual_Q_unreserved_other_mark_index_band434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (laterBand : Fin (d+1)) (m : {m : Fin 20 // m ≠ slot}) :
    (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L) band slot
      (parity_actual_Q_unreserved_other_mark_index434 d L band slot laterBand m)).val =
      (laterBand,m.val) := by
  unfold parity_actual_Q_unreserved_other_mark_index434
  simp

/-- All 19 other original marks remain distinct Q-positions even when
they share the same genuine source Q_j prime band. -/
theorem parity_actual_Q_unreserved_other_mark_index_injective434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (laterBand : Fin (d+1)) :
    Function.Injective
      (parity_actual_Q_unreserved_other_mark_index434 d L band slot laterBand) := by
  intro m m' hEq
  unfold parity_actual_Q_unreserved_other_mark_index434 at hEq
  have hSubtype :=
    (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L) band slot).symm.injective
      hEq
  have hm : m.val = m'.val :=
    congrArg (fun x : {v : Fin (d+1) × Fin 20 // v ≠ (band,slot)} => x.val.2)
      hSubtype
  exact Subtype.ext hm

/-- On the actual source SORTED Q labels, all nineteen other marks of
any later band lie STRICTLY after a given earlier-band Q-slot position. -/
theorem parity_actual_Q_unreserved_other_mark_after434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (j : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length)
    (laterBand : Fin (d+1))
    (hLaterBand : (sourceSortedLabelEquiv 20
      (sourceActualSortedScales 20 d L) band slot j).val.1 < laterBand)
    (m : {m : Fin 20 // m ≠ slot}) :
    j < parity_actual_Q_unreserved_other_mark_index434 d L band slot laterBand m := by
  let k := parity_actual_Q_unreserved_other_mark_index434 d L band slot laterBand m
  have hkBand : (sourceSortedLabelEquiv 20
      (sourceActualSortedScales 20 d L) band slot k).val.1 = laterBand := by
    exact congrArg Prod.fst
      (parity_actual_Q_unreserved_other_mark_index_band434 d L band slot laterBand m)
  by_contra hNot
  have hle : k ≤ j := le_of_not_gt hNot
  have hlt : k < j := by
    by_contra hNo
    have heq : k=j := le_antisymm hle (le_of_not_gt hNo)
    rw [heq] at hkBand
    exact (ne_of_lt hLaterBand) hkBand
  have hMon := parity_actual_Q_ordered_band_nondecreasing434 d L hL band slot k j hlt
  rw [hkBand] at hMon
  exact (not_le_of_gt hLaterBand) hMon

/-- 19 source-labelled later-band Q-slots exist (all 20 marked ordinary
primes except the one reserved marker), with no missing repeated label. -/
def parity_actual_Q_unreserved_other_mark_indices434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (laterBand : Fin (d+1)) :
    Finset (Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length) :=
  Finset.univ.image
    (parity_actual_Q_unreserved_other_mark_index434 d L band slot laterBand)

theorem parity_actual_Q_unreserved_other_mark_indices_card434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (laterBand : Fin (d+1)) :
    (parity_actual_Q_unreserved_other_mark_indices434 d L band slot laterBand).card = 19 := by
  unfold parity_actual_Q_unreserved_other_mark_indices434
  rw [Finset.card_image_iff.mpr (by
    intro a ha b hb
    exact fun h => (parity_actual_Q_unreserved_other_mark_index_injective434
      d L band slot laterBand) h)]
  simp
end Green64Analytic.Parity

end

end

/-! ## ActualQNextBandLogMass -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 32000

/-- The LITERAL nineteen unreserved prime marks of a strictly later
original Q band already force logarithmic tail mass >=19*s_later.
The original Q bands are closed, so no endpoint prime is lost; every
`p_i` comes from sourceActualSortedQ via the native sorted labels. -/
theorem parity_actual_Q_next_band_19_log_mass434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (j : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length)
    (laterBand : Fin (d+1))
    (hLaterBand : (sourceSortedLabelEquiv 20
      (sourceActualSortedScales 20 d L) band slot j).val.1 < laterBand)
    (p : (i : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length) → {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i}) :
    19*sourceOriginalPGroupScale 20 L laterBand.val ≤
      ∑ i ∈ (Finset.univ.filter (fun i : Fin
        (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length =>
        j < i)), Real.log ((p i).val : ℝ) := by
  let J := parity_actual_Q_unreserved_other_mark_indices434 d L band slot laterBand
  let suffix := (Finset.univ.filter (fun i : Fin
      (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length => j < i))
  have hSubset : J ⊆ suffix := by
    intro i hi
    obtain ⟨m,hm,heq⟩ := Finset.mem_image.mp hi
    have hAfter := parity_actual_Q_unreserved_other_mark_after434
      d L hL band slot j laterBand hLaterBand m
    rw [heq] at hAfter
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,hAfter⟩
  have hSingle : ∀ i ∈ J,
      sourceOriginalPGroupScale 20 L laterBand.val ≤ Real.log ((p i).val : ℝ) := by
    intro i hi
    obtain ⟨m,hm,heq⟩ := Finset.mem_image.mp hi
    have hBand0 := parity_actual_Q_unreserved_other_mark_index_band434
      d L band slot laterBand m
    rw [heq] at hBand0
    have hBand : (sourceSortedLabelEquiv 20
        (sourceActualSortedScales 20 d L) band slot i).val.1 = laterBand :=
      congrArg Prod.fst hBand0
    have hQ : (p i).val ∈ sourceOriginalQActualBands 20 d L laterBand := by
      have hp := (p i).property
      change (p i).val ∈ sourceOriginalQActualBands 20 d L
        (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
          band slot i).val.1 at hp
      rw [hBand] at hp
      exact hp
    have hPrime := source_original_Q_actual_prime 20 d L laterBand (p i).val hQ
    have hRange := (source_original_Q_actual_prime_range 20 d L
      (by norm_num) laterBand (p i).val hQ).1
    exact (Real.le_log_iff_exp_le (by exact_mod_cast hPrime.pos)).mpr hRange
  have hLog : ∀ i ∈ suffix, 0 ≤ Real.log ((p i).val : ℝ) := by
    intro i hi
    let k := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
      band slot i).val.1
    have hPrime : Nat.Prime (p i).val := source_original_Q_actual_prime 20 d L
      k (p i).val (p i).property
    have htwo : (2 : ℝ) ≤ ((p i).val : ℝ) := by exact_mod_cast hPrime.two_le
    exact Real.log_nonneg (by linarith)
  have hSumJ : 19*sourceOriginalPGroupScale 20 L laterBand.val ≤
      ∑ i ∈ J, Real.log ((p i).val : ℝ) := by
    have hs : ∑ _i ∈ J, sourceOriginalPGroupScale 20 L laterBand.val ≤
        ∑ i ∈ J, Real.log ((p i).val : ℝ) :=
      Finset.sum_le_sum hSingle
    have hCard : J.card = 19 :=
      parity_actual_Q_unreserved_other_mark_indices_card434 d L band slot laterBand
    simpa [Finset.sum_const,hCard,nsmul_eq_mul] using hs
  exact hSumJ.trans (Finset.sum_le_sum_of_subset_of_nonneg hSubset
    (by intro i hi hNot; exact hLog i hi))
end Green64Analytic.Parity

end

end

/-! ## ActualQEarlyTailBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 33000

/-- The previously missing NONTERMINAL original Q-slot tail inequality:
for ANY actual ordered Q position with band<d, the nineteen unreserved
marks in the IMMEDIATELY NEXT Q band alone contribute at least
19*s_{j+1}=(19/2)*s_j, strictly exceeding log p_j+s_j ≤(11/5)*s_j.
No source tail-capacity assumption is made: the actual sorted labels,
true Q closed prime endpoint ranges, r0=20, and literal reserved marker
are all used. This is the rigorous earlier-band half of Parity(4.4)-(4.5). -/
theorem parity_actual_Q_early_band_tail_covers_slot434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (p : (i : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length) → {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i})
    (j : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length)
    (hEarlier : (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
      band slot j).val.1.val < d) :
    Real.log ((p j).val : ℝ) + sourceActualSortedFrequencyScales 20 d L band slot j ≤
      ∑ i ∈ (Finset.univ.filter (fun i : Fin
        (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length =>
        j < i)), Real.log ((p i).val : ℝ) := by
  let b := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
      band slot j).val.1
  let nextB : Fin (d+1) := ⟨b.val+1,by omega⟩
  have hNext : b < nextB := by
    change b.val < b.val+1
    omega
  have hMass := parity_actual_Q_next_band_19_log_mass434 d L hL band slot j
    nextB hNext p
  have hQ : (p j).val ∈ sourceOriginalQActualBands 20 d L b := by
    exact (p j).property
  have hPrime := source_original_Q_actual_prime 20 d L b (p j).val hQ
  have hUpper := (source_original_Q_actual_prime_range 20 d L
    (by norm_num) b (p j).val hQ).2
  have hLog : Real.log ((p j).val : ℝ) ≤
      (6/5:ℝ)*sourceOriginalPGroupScale 20 L b.val :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hPrime.pos)).mpr hUpper
  have hDouble : sourceOriginalPGroupScale 20 L b.val =
      2*sourceOriginalPGroupScale 20 L nextB.val := by
    convert parity_original_Q_scale_double_next434 L b.val using 1
  have hPosScale : 0 < sourceOriginalPGroupScale 20 L nextB.val :=
    source_original_positive_dyadic_scale 20 nextB.val L (by norm_num) hL
  change Real.log ((p j).val : ℝ) + sourceOriginalPGroupScale 20 L b.val ≤
    ∑ i ∈ (Finset.univ.filter (fun i : Fin
      (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length =>
      j < i)), Real.log ((p i).val : ℝ)
  linarith
end Green64Analytic.Parity

end

end

/-! ## ActualQAllTailCapacity -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 33000

/-- The FULL PARITY (4.4) tail-capacity condition is now genuinely proved
for EVERY original dynamically sorted Q slot, from the actual source
Q prime bands. Earlier bands use the literal nineteen later Q marks;
last band uses the actual largest admissible Q depth s_last<40logL.
The coefficient 88 is the exact r20, c2=6/5 value 40*(1+6/5).
No hypothetical Q-tail condition is assumed. -/
theorem parity_eventually_actual_all_Q_slot_tail_capacity434 :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (p : (i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length) →
          {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
            L band slot i})
        (j : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length),
      Real.log ((p j).val : ℝ) +
        sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L)
          L band slot j ≤ 88*Real.log L +
        ∑ i ∈ (Finset.univ.filter (fun i : Fin
          (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length => j < i)),
          Real.log ((p i).val : ℝ) := by
  filter_upwards [parity_eventually_actual_last_Q_prime_skip_cost_log434,
    eventually_ge_atTop (2:ℝ)] with L hLast hL
  refine ⟨hL,?_⟩
  intro band slot p j
  let d := sourceOriginalLiteralDepth 20 L
  let b := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
    band slot j).val.1
  have hLp : 0 < L := by linarith
  have hLog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  by_cases hEarlier : b.val < d
  · have hEarly := parity_actual_Q_early_band_tail_covers_slot434
      d L hLp band slot p j hEarlier
    linarith
  · have hb : b.val = d := by have hbLe := b.isLt; omega
    have hBEq : b = (⟨d, by omega⟩ : Fin (d+1)) := Fin.ext hb
    have hpLast : (p j).val ∈ sourceOriginalQActualBands 20 d L
        (⟨d,by omega⟩ : Fin (d+1)) := by
      have hp := (p j).property
      change (p j).val ∈ sourceOriginalQActualBands 20 d L b at hp
      rw [hBEq] at hp
      exact hp
    have hLastCost := hLast (p j).val hpLast
    have hSuffixNonneg : 0 ≤
        ∑ i ∈ (Finset.univ.filter (fun i : Fin
          (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
            band slot).length => j < i)),
          Real.log ((p i).val : ℝ) := by
      apply Finset.sum_nonneg
      intro i hi
      let q := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
        band slot i).val.1
      have hPrime : Nat.Prime (p i).val := source_original_Q_actual_prime 20 d L q
        (p i).val (p i).property
      have hTwo : (2:ℝ) ≤ ((p i).val : ℝ) := by exact_mod_cast hPrime.two_le
      exact Real.log_nonneg (by linarith)
    change Real.log ((p j).val : ℝ) + sourceOriginalPGroupScale 20 L b.val ≤
      88*Real.log L + _
    rw [hb]
    linarith
end Green64Analytic.Parity

end

end

/-! ## ActualSmoothAllocatedELower -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000
set_option maxRecDepth 32000

/-- Literal Parity (4.5) LOWER e support proved for ALL actual moving Q
bands, ordered slots, actual B590 smooth branch weights and all mark
assignments, assuming ONLY the PHYSICAL original retained Q-product mass
`E<=product(all nonreserved source Q slots)`. Unlike previous reductions,
no Q-tail or depth-range inequality is assumed: both were proved from
actual source geometry. The remaining total-Q-product bound must be
linked to the retained u=ev and P/reserved prime-size source gates. -/
theorem parity_eventually_actual_smooth_e_lower_of_full_Q_mass434 :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      ∀ (E : ℝ), 1 ≤ E →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (p : (i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length) →
          {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
            L band slot i}),
      E ≤ ((∏ i, (p i).val : ℕ) : ℝ) →
      parityOriginalQAllocationBranchWeight434 20 E
        (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
          band slot) delta (fun i => (p i).val) ≠ 0 →
      E*L^((-88:ℝ)) ≤ (paritySourceOrderedAllocatedE434 delta p : ℝ) := by
  filter_upwards [parity_eventually_actual_all_Q_slot_tail_capacity434]
    with L hTail
  refine ⟨hTail.1,?_⟩
  intro E hE band slot delta p hFull hWeight
  let d := sourceOriginalLiteralDepth 20 L
  have hLPos : 0 < L := by linarith [hTail.1]
  have hEPos : 0 < E := by linarith
  have hScale := parity_actual_sorted_Q_allocation_scales_positive434
    d L hLPos band slot
  have hpPos : ∀ i, 0 < (p i).val := by
    intro i
    let q := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
      band slot i).val.1
    exact (source_original_Q_actual_prime 20 d L q (p i).val (p i).property).pos
  have hTotalLog : Real.log E ≤
      ∑ i, Real.log ((p i).val : ℝ) := by
    have hProdLog : Real.log ((∏ i, (p i).val : ℕ) : ℝ) =
        ∑ i, Real.log ((p i).val : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod]
      intro i hi
      exact_mod_cast (Nat.ne_of_gt (hpPos i))
    rw [← hProdLog]
    exact Real.log_le_log hEPos hFull
  have hTailBudget : ∀ j, delta j = false →
      Real.log ((p j).val : ℝ) +
        sourceActualSortedFrequencyScales 20 d L band slot j ≤
      88*Real.log L +
        ∑ i ∈ (Finset.univ.filter (fun i : Fin
          (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length =>
          j < i)), Real.log ((p i).val : ℝ) := by
    intro j hj
    exact hTail.2 band slot p j
  have hLower := parity_smooth_Q_allocation_e_lower_of_tail434 20 E
    (88*Real.log L)
    (sourceActualSortedFrequencyScales 20 d L band slot)
    delta p hEPos (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
    hScale hpPos hWeight hTotalLog hTailBudget
  have hPow : L^((-88:ℝ)) = Real.exp (-(88*Real.log L)) := by
    rw [Real.rpow_def_of_pos hLPos]
    congr 1
    ring
  rw [hPow]
  exact hLower
end Green64Analytic.Parity

end

end

/-! ## ActualSmoothAllocatedERange -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 30000

/-- Both Parity(4.5) bounds PROVED for every physical-mass-supported positive
smooth source allocation branch in actual r20 moving-depth Q bands:
E*L^-88 <= e <= E. Also derives odd e, coprime R=2, E(e)=1 and
W1(e*v)=W1(v). No range or tail-budget hypothesis remains: ONLY the
literal retained total Q-product capacity E<=product(nonreserved Q)
must be established from the original physical u and small group/reserved
factor before the historical a_e can be identified. -/
theorem parity_eventually_actual_smooth_e_full_range_of_Q_mass434 :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      ∀ E : ℝ, 1 ≤ E →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (p : (i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length) →
          {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
            L band slot i}),
      E ≤ ((∏ i, (p i).val : ℕ) : ℝ) →
      parityOriginalQAllocationBranchWeight434 20 E
        (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
          band slot) delta (fun i => (p i).val) ≠ 0 →
      let e := paritySourceOrderedAllocatedE434 delta p
      E*L^((-88:ℝ)) ≤ (e:ℝ) ∧ (e:ℝ) ≤ E ∧ Odd e ∧
      IsUnit (e : ZMod 2) ∧
      sourceOriginalPParityExponent
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) e = 0 ∧
      ∀ v : ℕ, v ≠ 0 →
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) (e*v) =
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v := by
  filter_upwards [parity_eventually_actual_smooth_e_lower_of_full_Q_mass434,
    parity_eventually_actual_Q_allocated_e_odd_unit434] with L hLow hOdd
  refine ⟨hLow.1,?_⟩
  intro E hE band slot delta p hFull hWeight
  dsimp only
  have hLPos : 0 < L := by linarith [hLow.1]
  have heLow := hLow.2 E hE band slot delta p hFull hWeight
  have heUpper := parity_actual_sorted_Q_smooth_e_upper434
    L E hLPos hE band slot delta p hWeight
  have heOdd := (hOdd.2 band slot delta p).1
  have heUnit := (hOdd.2 band slot delta p).2.2.1
  have hP0 := parity_actual_Q_allocated_e_P_parity_zero434
    L hLPos band slot delta p
  refine ⟨heLow,heUpper,heOdd,heUnit,hP0,?_⟩
  intro v hv
  exact (parity_actual_Q_allocated_e_P_weight_parity_invariant434
    L hLPos band slot delta p v hv).1
end Green64Analytic.Parity

end

end

/-! ## ActualPhysicalQMass -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 30000

/-- Original SOURCE r=20 Q band prime upper bound with NO band proxy:
all actual reserved prime labels (even the first Q band) satisfy
q <= exp((3/110)*L). The constant comes from Q0Scale=1/44 and
6/5 closed Q endpoint, without losing endpoints. -/
theorem parity_actual_original_reserved_Q_prime_exp_cap434
    (d : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (band : Fin (d+1)) (q : ℕ)
    (hq : q ∈ sourceOriginalQActualBands 20 d L band) :
    (q:ℝ) ≤ Real.exp ((3/110:ℝ)*L) := by
  have hExp := source_original_Q_actual_exponent_le_Q0 20 band.val
    (by norm_num)
  have hScale := mul_le_mul_of_nonneg_right hExp hL
  rw [source_original_Q_actual_scale_eq_P_scale 20 band.val L (by norm_num)] at hScale
  have hQ0 : sourceOriginalQ0Scale 20*L = L/44 := by
    norm_num [sourceOriginalQ0Scale]
    ring
  rw [hQ0] at hScale
  have hQrange := (source_original_Q_actual_prime_range 20 d L
    (by norm_num) band q hq).2
  calc
    (q:ℝ) ≤ Real.exp ((6/5:ℝ)*sourceOriginalPGroupScale 20 L band.val) := hQrange
    _ ≤ Real.exp ((3/110:ℝ)*L) := Real.exp_le_exp.mpr (by linarith)

/-- The literal B537 physical P-part support at H=floor(exp(L/44))
forces v<=exp(L/44), with all source P prime-power multiplicities. -/
theorem parity_actual_original_physical_Ppart_exp_cap434
    (L : ℝ) (v : ℕ)
    (hv : v ∈ sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊) :
    (v:ℝ) ≤ Real.exp (L/44) := by
  have hvBound := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).2
  have hvCast : (v:ℝ) ≤ (⌊Real.exp (L/44)⌋₊:ℝ) := by
    exact_mod_cast hvBound
  exact hvCast.trans (Nat.floor_le (Real.exp_nonneg _))

/-- SOURCE physical u = reserved-Q-prime * ALL nonreserved sorted Q
prime slots * genuine physical P part. The pinned B537 P gate and the
ACTUAL closed Q endpoints show, from u>=exp(L), that the full ordinary
Q product is >= exp((19/20)L). NO assumption on the Q-product itself.
This proves the physical source mass input needed by Parity (4.5) within
its stated original u-scale and all r20 Q bands. -/
theorem parity_actual_original_physical_full_Qmass_lower434
    (d : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (band : Fin (d+1)) (slot : Fin 20)
    (q : {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band})
    (p : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length) →
      {z : ℕ // z ∈ sourceActualSortedQ 20 d L band slot i})
    (v : ℕ)
    (hv : v ∈ sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
    (hPhysical : Real.exp L ≤
      ((q.val * (∏ i, (p i).val) * v : ℕ) : ℝ)) :
    Real.exp ((19/20:ℝ)*L) ≤ ((∏ i, (p i).val : ℕ) : ℝ) := by
  let Q := ∏ i, (p i).val
  have hqBound := parity_actual_original_reserved_Q_prime_exp_cap434 d L hL
    band q.val q.property
  have hvBound := parity_actual_original_physical_Ppart_exp_cap434 L v hv
  have hSmall : ((q.val:ℝ)*(v:ℝ)) ≤ Real.exp (L/20) := by
    calc
      (q.val:ℝ)*(v:ℝ) ≤ Real.exp ((3/110:ℝ)*L)*Real.exp (L/44) := by
        gcongr
      _ = Real.exp (L/20) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hPhysicalCast : Real.exp L ≤ ((q.val:ℝ)*(Q:ℝ))*(v:ℝ) := by
    simpa only [Q,Nat.cast_mul] using hPhysical
  have hPositive : 0 ≤ (Q:ℝ) := Nat.cast_nonneg Q
  have hCompare : Real.exp L ≤ (Q:ℝ)*Real.exp (L/20) := by
    calc
      Real.exp L ≤ (Q:ℝ)*((q.val:ℝ)*(v:ℝ)) := by
        calc
          _ ≤ (q.val:ℝ)*(Q:ℝ)*(v:ℝ) := hPhysicalCast
          _ = (Q:ℝ)*((q.val:ℝ)*(v:ℝ)) := by ring
      _ ≤ (Q:ℝ)*Real.exp (L/20) :=
        mul_le_mul_of_nonneg_left hSmall hPositive
  have hExpId : Real.exp L = Real.exp ((19/20:ℝ)*L) * Real.exp (L/20) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hExpId] at hCompare
  exact (mul_le_mul_iff_of_pos_right (Real.exp_pos _)).mp hCompare
end Green64Analytic.Parity

end

end

/-! ## ActualPhysicalSmoothERange -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- Source physical u>=exp(L), actual P cap exp(L/44) and reserved Q
prime cap exp((3/110)L) imply full Q mass >=exp((19/20)L).
Consequently, for 1<=E<=exp((19/20)L), every positive original B590
smooth allocation branch has the FULL Parity (4.5) range
    E*L^-88 <= e <= E
and the true P-parity, ZMod2 unit and W1 invariance. No explicit
Q-mass hypothesis is passed to this theorem. The physical u factor
is the literal reserved Q prime * original nonreserved Q labels *
original P-supported v, with ALL multiplicities.
The remaining physical range restriction E<=exp((19/20)L) is honest;
Parity's arbitrary-b_* (4.2) may need a parameter-dependent P cap. -/
theorem parity_eventually_actual_physical_smooth_e_range434 :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      ∀ E : ℝ, 1 ≤ E → E ≤ Real.exp ((19/20:ℝ)*L) →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (q : {q : ℕ // q ∈ sourceOriginalQActualBands 20
          (sourceOriginalLiteralDepth 20 L) L band})
        (p : (i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length) →
          {z : ℕ // z ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
            L band slot i})
        (v : ℕ),
      v ∈ sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊ →
      Real.exp L ≤ ((q.val*(∏ i, (p i).val)*v : ℕ) : ℝ) →
      ∀ delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool,
      parityOriginalQAllocationBranchWeight434 20 E
        (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
          band slot) delta (fun i => (p i).val) ≠ 0 →
      let e := paritySourceOrderedAllocatedE434 delta p
      E*L^((-88:ℝ)) ≤ (e:ℝ) ∧ (e:ℝ) ≤ E ∧ Odd e ∧
      IsUnit (e : ZMod 2) ∧
      sourceOriginalPParityExponent
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) e = 0 ∧
      ∀ v2 : ℕ, v2 ≠ 0 →
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) (e*v2) =
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v2 := by
  filter_upwards [parity_eventually_actual_smooth_e_full_range_of_Q_mass434]
    with L hRange
  refine ⟨hRange.1,?_⟩
  intro E hE hEcap band slot q p v hv hu delta hWeight
  have hL : 0 ≤ L := by linarith [hRange.1]
  have hPhysicalMass := parity_actual_original_physical_full_Qmass_lower434
    (sourceOriginalLiteralDepth 20 L) L hL band slot q p v hv hu
  have hQMass : E ≤ ((∏ i, (p i).val : ℕ) : ℝ) :=
    hEcap.trans hPhysicalMass
  exact hRange.2 E hE band slot delta p hQMass hWeight
end Green64Analytic.Parity

end

end

/-! ## ActualOriginalAFullQWitness -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 32000

/-- A NONZERO LITERAL ORIGINAL sourceOriginalA coefficient has a FULL
native Q-slot prime witness, including every band and its twenty labels.
This extracts sourceOriginalOrdinaryCoefficient support, rather than
assuming the source factorisation and prime count. -/
theorem parity_original_A_nonzero_full_Q_slots_witness434
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (u : ℕ) (hA : sourceOriginalA r Q P u ≠ 0) :
    ∃ f : (b : B) → Fin r → {q : ℕ // q ∈ Q b},
      (∏ b : B, ∏ i : Fin r, (f b i).val) =
        sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u := by
  have hc : sourceOriginalOrdinaryCoefficient r Q
      (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u) ≠ 0 := by
    intro h
    apply hA
    simp only [sourceOriginalA,sourceOriginalA0,h,mul_zero,zero_mul]
  by_contra hNo
  exact hc (by simp only [sourceOriginalOrdinaryCoefficient,if_neg hNo])

/-- The original `sourceSortedLabelEquiv`, without a surrogating tuple,
reindexes a FULL original Q_j labelled assignment into all nonreserved
sourceActualSortedQ positions after taking out the reserved (band,slot). -/
def parityActualSourceRemainingFullQTuple434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    (i : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length) →
      {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i} :=
  fun i => f ((sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
      band slot i).val.1)
    ((sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
      band slot i).val.2)

/-- The literal full ORIGINAL marked Q-prime product is reserved prime
times precisely the 20(d+1)-1 SOURCE sorted remaining primes. The
identification uses the actual native sourceSortedLabelEquiv, so no
factorial or repeated prime-power information can be dropped. -/
theorem parity_actual_source_fullQ_split_reserved_sorted_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      (f band slot).val *
        (∏ i, (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) := by
  let g : Fin (d+1) × Fin 20 → ℕ := fun z => (f z.1 z.2).val
  have hFull : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      ∏ z : Fin (d+1) × Fin 20, g z :=
    (Fintype.prod_prod_type g).symm
  have hSplit := source_original_Q_product_split_one (band,slot) g
  have hRest :
      (∏ i, (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) =
      ∏ z : {z : Fin (d+1) × Fin 20 // z ≠ (band,slot)}, g z.val := by
    simpa only [parityActualSourceRemainingFullQTuple434,g] using
      (Equiv.prod_comp
        (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L) band slot)
        (fun z : {z : Fin (d+1) × Fin 20 // z ≠ (band,slot)} => g z.val))
  calc
    _ = ∏ z : Fin (d+1) × Fin 20, g z := hFull
    _ = g (band,slot) *
        ∏ z : {z : Fin (d+1) × Fin 20 // z ≠ (band,slot)}, g z.val := hSplit
    _ = (f band slot).val *
        (∏ i, (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) := by
      rw [hRest]

/-- The NONZERO ORIGINAL sourceOriginalA, with no independent Q tuple
hypothesis, really factors its physical integer u as the original
reserved labelled Q prime * ALL sorted remaining Q marks * literal
`sourceOriginalPPrimePart`, preserving prime multiplicities. -/
theorem parity_actual_original_A_nonzero_physical_QP_factorization434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (hA : sourceOriginalA 20
      (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20) :
    ∃ f : (j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j},
      (f band slot).val *
          (∏ i, (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) *
          sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u = u := by
  have hu : u ≠ 0 := by
    intro hz
    apply hA
    simpa only [hz] using (b640_original_A_zero434 20
      (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L))
  obtain ⟨f,hf⟩ := parity_original_A_nonzero_full_Q_slots_witness434
    20 (sourceOriginalQActualBands 20 d L)
    (sourceOriginalPAllActualBands 20 L) u hA
  refine ⟨f,?_⟩
  have hFull := parity_actual_source_fullQ_split_reserved_sorted_exact434
    d L band slot f
  calc
    _ = (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) *
        sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u := by
      rw [hFull]
    _ = sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u *
        sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u := by
      rw [hf]
    _ = u := source_original_ordinary_times_P_part _ u hu
end Green64Analytic.Parity

end

end

/-! ## ActualOriginalAPhysicalMass -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14500000
set_option maxRecDepth 32000

/-- EVERY full original Q-prime tuple that contributes to a real
`sourceOriginalOrdinaryCoefficient` can be split at ANY original reserved
slot. Under its true source physical u>=exp L and PPart<=exp(L/44)
gates the unreserved sorted Q product has mass >=exp(19L/20).
In contrast to earlier bridges, the physical product identity itself
is DERIVED from the literal full source Q-product and the native
`source_original_ordinary_times_P_part` theorem. -/
theorem parity_actual_original_full_Q_tuple_source_physical_mass434
    (d : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (u : ℕ) (hu : u ≠ 0)
    (hLarge : Real.exp L ≤ (u : ℝ))
    (hPcap : sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
      sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (hf : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (band : Fin (d+1)) (slot : Fin 20) :
    Real.exp ((19/20:ℝ)*L) ≤
      ((∏ i, (parityActualSourceRemainingFullQTuple434 d L band slot f i).val : ℕ) : ℝ) := by
  have hSplit := parity_actual_source_fullQ_split_reserved_sorted_exact434
    d L band slot f
  have hU : (f band slot).val *
      (∏ i, (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) *
      sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u = u := by
    calc
      _ = (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) *
          sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u := by
        rw [hSplit]
      _ = sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u *
          sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u := by
        rw [hf]
      _ = u := source_original_ordinary_times_P_part _ u hu
  have hLargeR : Real.exp L ≤
      (((f band slot).val *
          (∏ i, (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) *
          sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u : ℕ) : ℝ) := by
    calc
      _ ≤ (u:ℝ) := hLarge
      _ = _ := by rw [hU]
  exact parity_actual_original_physical_full_Qmass_lower434
    d L hL band slot (f band slot)
    (parityActualSourceRemainingFullQTuple434 d L band slot f)
    (sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    hPcap hLargeR

/-- A NONZERO literal original sourceOriginalA (not a proxy physical
cofactor) supplies at least one FULL original Q-prime assignment; on
the true B537 physical P carrier and u>=exp L, the source sorted
nonreserved Q product has at least exp(19L/20) mass. The witness
requires no invented Q-mass assumption or independent factorization. -/
theorem parity_actual_original_A_nonzero_physical_Q_mass_witness434
    (d : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (u : ℕ)
    (hA : sourceOriginalA 20
      (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u ≠ 0)
    (hLarge : Real.exp L ≤ (u:ℝ))
    (hPcap : sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
      sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
    (band : Fin (d+1)) (slot : Fin 20) :
    ∃ f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j},
      Real.exp ((19/20:ℝ)*L) ≤
        ((∏ i, (parityActualSourceRemainingFullQTuple434 d L band slot f i).val : ℕ) : ℝ) := by
  have hu : u ≠ 0 := by
    intro hz
    exact hA (by simpa only [hz] using (b640_original_A_zero434 20
      (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L)))
  obtain ⟨f,hf⟩ := parity_original_A_nonzero_full_Q_slots_witness434
    20 (sourceOriginalQActualBands 20 d L)
    (sourceOriginalPAllActualBands 20 L) u hA
  exact ⟨f,parity_actual_original_full_Q_tuple_source_physical_mass434
    d L hL u hu hLarge hPcap f hf band slot⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalPositiveResidual -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Genuine SOURCE Parity §4.2 Eq(4.4), LOWER side, without postulating
anything about the residual R_i. On every actual nonzero B590 f0/f1
branch whose prime slots are >=1 and E>=1, no prefix can consume more
than the total selected Q logarithmic mass, already bounded by log E
through the genuine positive f1 gate support. -/
theorem parity_original_Q_positive_branch_residual_nonneg434
    {n : ℕ} (r : ℕ) (E : ℝ)
    (scales : Fin n → ℝ) (delta : Fin n → Bool) (p : Fin n → ℕ)
    (hE : 1 ≤ E) (hScales : ∀ i, 0 < scales i)
    (hP : ∀ i, 1 ≤ p i)
    (hWeight : parityOriginalQAllocationBranchWeight434 r E scales delta p ≠ 0)
    (i : Fin n) :
    0 ≤ parityOriginalQAllocationResidual434 E delta p i := by
  have hBudget := parity_original_Q_smooth_positive_branch_log_budget434
    r E scales delta p hE hScales hWeight
  have hFull : (∑ j : Fin n,
      if delta j then Real.log (p j : ℝ) else 0) ≤ Real.log E := by
    simpa [Finset.sum_filter] using hBudget
  have hSubset : (Finset.univ.filter (fun j : Fin n => j < i)) ⊆
      (Finset.univ : Finset (Fin n)) := Finset.filter_subset _ _
  have hPart :
      (∑ j ∈ (Finset.univ.filter (fun j : Fin n => j < i)),
        if delta j then Real.log (p j : ℝ) else 0) ≤
      (∑ j : Fin n, if delta j then Real.log (p j : ℝ) else 0) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
    intro j hj hjnot
    split_ifs
    · exact Real.log_nonneg (by exact_mod_cast hP j)
    · exact le_refl _
  unfold parityOriginalQAllocationResidual434
  linarith


/-- The lower half of Parity Eq(4.4) is proved on the ACTUAL full r=20
labelled source Q tuple, after the true sourceSortedLabelEquiv removes
its reserved Q prime. This removes arbitrary-positive-prime and scale
assumptions from the generic residual theorem. Only original 1<=E and
the branch's actual B590 nonzero weight remain. -/
theorem parity_actual_original_fullQ_positive_branch_residual_nonneg434
    (d : ℕ) (L E : ℝ) (hL : 0 < L) (hE : 1 ≤ E)
    (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (hWeight : parityOriginalQAllocationBranchWeight434 20 E
      (sourceActualSortedFrequencyScales 20 d L band slot)
      delta (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) ≠ 0)
    (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length) :
    0 ≤ parityOriginalQAllocationResidual434 E delta
      (fun z => (parityActualSourceRemainingFullQTuple434 d L band slot f z).val) i := by
  have hS := parity_actual_sorted_Q_allocation_scales_positive434
    d L hL band slot
  have hp : ∀ z : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      1 ≤ (parityActualSourceRemainingFullQTuple434 d L band slot f z).val := by
    intro z
    let j := (sourceSortedLabelEquiv 20
      (sourceActualSortedScales 20 d L) band slot z).val.1
    have hprime := source_original_Q_actual_prime 20 d L j
      (parityActualSourceRemainingFullQTuple434 d L band slot f z).val
      (parityActualSourceRemainingFullQTuple434 d L band slot f z).property
    exact hprime.one_lt.le
  exact parity_original_Q_positive_branch_residual_nonneg434 20 E
    (sourceActualSortedFrequencyScales 20 d L band slot)
    delta (fun z => (parityActualSourceRemainingFullQTuple434 d L band slot f z).val)
    hE hS hp hWeight i
end Green64Analytic.Parity

end

end

/-! ## OriginalEq44UpperRecurrence -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Original Parity B590 sequential residual, with all selected prime
logarithms subtracted in the original slot order. -/
def parityOriginalEq44PrefixResidual434
    (E : ℝ) (δ : ℕ → Bool) (logp : ℕ → ℝ) (i : ℕ) : ℝ :=
  Real.log E - ∑ j ∈ Finset.range i, if δ j then logp j else 0

/-- Remaining original Q prime logarithmic mass, without dropping any
repeated or previously skipped labelled slot. -/
def parityOriginalEq44Remaining434
    (logp : ℕ → ℝ) (n i : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, logp j) -
    (∑ j ∈ Finset.range i, logp j)

/-- The exact elementary Parity (4.4) step. A selected f1 branch removes
its prime logarithm from BOTH residual and remaining Q mass. A skipped
f0 branch leaves the residual fixed and is controlled by the genuine
source skip support R_i < log p_i + s_i and Q suffix capacity. -/
theorem parity_original_eq44_upper_all_prefixes_of_skip_supply434
    (E B : ℝ) (n : ℕ) (δ : ℕ → Bool)
    (logp scale : ℕ → ℝ) (hB : 0 ≤ B)
    (hTotal : Real.log E ≤ ∑ k ∈ Finset.range n, logp k)
    (hSkip : ∀ j < n, δ j = false →
      parityOriginalEq44PrefixResidual434 E δ logp j < logp j + scale j)
    (hSupply : ∀ j < n, logp j + scale j ≤
      parityOriginalEq44Remaining434 logp n (j+1) + B)
    (i : ℕ) (hi : i ≤ n) :
    parityOriginalEq44PrefixResidual434 E δ logp i ≤
      parityOriginalEq44Remaining434 logp n i + B := by
  induction i with
  | zero =>
      simp only [parityOriginalEq44PrefixResidual434,
        parityOriginalEq44Remaining434, Finset.range_zero, Finset.sum_empty, sub_zero]
      linarith
  | succ j ih =>
      have hj : j < n := by omega
      have hprev := ih (by omega)
      have hRes : parityOriginalEq44PrefixResidual434 E δ logp (j+1) =
          parityOriginalEq44PrefixResidual434 E δ logp j -
            (if δ j then logp j else 0) := by
        simp [parityOriginalEq44PrefixResidual434,Finset.sum_range_succ]
        ring
      have hTail : parityOriginalEq44Remaining434 logp n (j+1) =
          parityOriginalEq44Remaining434 logp n j - logp j := by
        simp [parityOriginalEq44Remaining434, Finset.sum_range_succ]
        ring
      cases hδ : δ j with
      | true =>
          simp only [hδ, ↓reduceIte] at hRes
          rw [hRes,hTail]
          linarith
      | false =>
          simp only [hδ, Bool.false_eq_true, ↓reduceIte, sub_zero] at hRes
          rw [hRes]
          exact (hSkip j hj hδ).le.trans (hSupply j hj)
end Green64Analytic.Parity

end

end

/-! ## OriginalB590PrefixReach -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Native Parity f0 skip support requires only the one actual local B590
gate, not the product over any future slot. This is essential to avoid
wrongly deriving source mass normalization from nonzero *full* branches. -/
theorem parity_original_B590_one_nonzero_f0_skip_budget434
    (r : ℕ) (R logp s : ℝ) (hs : 0 < s)
    (hGate : sourceBufferedGateReal r false ((R-logp)/s) ≠ 0) :
    R < logp + s := by
  have hGamma : Real.smoothTransition ((R-logp)/s) ≠ 1 := by
    intro hOne
    apply hGate
    simp [sourceBufferedGateReal,hOne]
  have hArg : (R-logp)/s < 1 := by
    by_contra h
    exact hGamma (Real.smoothTransition.one_of_one_le (le_of_not_gt h))
  have hNum := (div_lt_one hs).mp hArg
  linarith

/-- Original genuine B590 f0/f1 weighted prefix (not a complete
branch). Each slot uses the actual history-dependent residual R_j. -/
def parityOriginalEq44PrefixGateWeight434
    (r : ℕ) (E : ℝ) (delta : ℕ → Bool)
    (logp scale : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.range i,
    sourceBufferedGateReal r (delta j)
      ((parityOriginalEq44PrefixResidual434 E delta logp j-logp j)/scale j)

/-- Every gate in a NONZERO original B590 prefix has nonzero weight:
this does not depend on whether the prefix admits a later completion. -/
theorem parity_original_B590_nonzero_prefix_gate434
    (r : ℕ) (E : ℝ) (delta : ℕ → Bool)
    (logp scale : ℕ → ℝ) (i j : ℕ)
    (hj : j < i)
    (hPrefix : parityOriginalEq44PrefixGateWeight434 r E delta logp scale i ≠ 0) :
    sourceBufferedGateReal r (delta j)
      ((parityOriginalEq44PrefixResidual434 E delta logp j-logp j)/scale j) ≠ 0 := by
  exact (Finset.prod_ne_zero_iff.mp hPrefix) j (Finset.mem_range.mpr hj)

/-- SOURCE Parity(4.4) upper residual for an individual prefix, under
only the f0 skip gates PRECEDING that prefix. No nonzero COMPLETED
allocation is presumed; this is the missing reachability-safe form. -/
theorem parity_original_eq44_upper_of_local_skip_prefix434
    (E B : ℝ) (n : ℕ) (delta : ℕ → Bool)
    (logp scale : ℕ → ℝ) (hB : 0 ≤ B)
    (hTotal : Real.log E ≤ ∑ k ∈ Finset.range n, logp k)
    (i : ℕ) (hi : i ≤ n)
    (hSkip : ∀ j < i, delta j = false →
      parityOriginalEq44PrefixResidual434 E delta logp j < logp j + scale j)
    (hSupply : ∀ j < i, logp j + scale j ≤
      parityOriginalEq44Remaining434 logp n (j+1) + B) :
    parityOriginalEq44PrefixResidual434 E delta logp i ≤
      parityOriginalEq44Remaining434 logp n i + B := by
  induction i with
  | zero =>
      simp only [parityOriginalEq44PrefixResidual434,
        parityOriginalEq44Remaining434, Finset.range_zero, Finset.sum_empty, sub_zero]
      linarith
  | succ j ih =>
      have hj : j < n := by omega
      have hprev := ih (by omega)
        (by intro k hk hdelta; exact hSkip k (by omega) hdelta)
        (by intro k hk; exact hSupply k (by omega))
      have hRes : parityOriginalEq44PrefixResidual434 E delta logp (j+1) =
          parityOriginalEq44PrefixResidual434 E delta logp j -
            (if delta j then logp j else 0) := by
        simp [parityOriginalEq44PrefixResidual434,Finset.sum_range_succ]
        ring
      have hTail : parityOriginalEq44Remaining434 logp n (j+1) =
          parityOriginalEq44Remaining434 logp n j - logp j := by
        simp [parityOriginalEq44Remaining434,Finset.sum_range_succ]
        ring
      cases hδ : delta j with
      | true =>
          simp only [hδ, ↓reduceIte] at hRes
          rw [hRes,hTail]
          linarith
      | false =>
          simp only [hδ, Bool.false_eq_true, ↓reduceIte, sub_zero] at hRes
          rw [hRes]
          exact (hSkip j (by omega) hδ).le.trans (hSupply j (by omega))

/-- Important strengthened source form: if an original adaptive B590
prefix is nonzero, then all its f0 gates enforce Parity(4.4) upper bound,
using only full original Q capacity and physical suffix supply. No
later positive completion is required. -/
theorem parity_original_eq44_upper_of_nonzero_B590_prefix434
    (r : ℕ) (E B : ℝ) (n : ℕ) (delta : ℕ → Bool)
    (logp scale : ℕ → ℝ) (hB : 0 ≤ B)
    (hScale : ∀ j < n, 0 < scale j)
    (hTotal : Real.log E ≤ ∑ k ∈ Finset.range n, logp k)
    (hSupply : ∀ j < n, logp j + scale j ≤
      parityOriginalEq44Remaining434 logp n (j+1) + B)
    (i : ℕ) (hi : i ≤ n)
    (hPrefix : parityOriginalEq44PrefixGateWeight434 r E delta logp scale i ≠ 0) :
    parityOriginalEq44PrefixResidual434 E delta logp i ≤
      parityOriginalEq44Remaining434 logp n i + B := by
  apply parity_original_eq44_upper_of_local_skip_prefix434 E B n delta logp scale
    hB hTotal i hi
  · intro j hj hδ
    have hGate := parity_original_B590_nonzero_prefix_gate434
      r E delta logp scale i j hj hPrefix
    rw [hδ] at hGate
    exact parity_original_B590_one_nonzero_f0_skip_budget434
      r _ _ _ (hScale j (lt_of_lt_of_le hj hi)) hGate
  · intro j hj
    exact hSupply j (lt_of_lt_of_le hj hi)
end Green64Analytic.Parity

end

end

/-! ## OriginalFinPrefixReindex -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact conversion of the sequential natural Q prime slots into
the native Fin n source B590 prefix order. -/
theorem parity_original_Q_fin_prefix_eq_nat_range434
    {n : ℕ} (m : ℕ) (hm : m ≤ n) (f : Fin n → ℝ) :
    (∑ k ∈ Finset.range m,
      if hk : k < n then f ⟨k,hk⟩ else 0) =
    ∑ i ∈ ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m)), f i := by
  classical
  apply Finset.sum_bij (fun k hk => (⟨k,lt_of_lt_of_le (Finset.mem_range.mp hk) hm⟩ : Fin n))
  · intro k hk
    simp [Finset.mem_filter, Finset.mem_range, (Finset.mem_range.mp hk)]
  · intro k hk l hl hEq
    exact congrArg Fin.val hEq
  · intro i hi
    refine ⟨i.val, Finset.mem_range.mpr (Finset.mem_filter.mp hi).2, ?_⟩
    exact Fin.ext rfl
  · intro k hk
    simp [dif_pos (lt_of_lt_of_le (Finset.mem_range.mp hk) hm)]

/-- Prefix-filter normalization for genuine source Q allocation
residuals, with all original labelled slots preserved. -/
theorem parity_original_Q_fin_prefix_eq_nat_values434
    {n : ℕ} (m : ℕ) (hm : m ≤ n) (f : Fin n → ℝ) :
    (∑ k ∈ Finset.range m,
      if hk : k < n then f ⟨k,hk⟩ else 0) =
    (∑ i ∈ (Finset.univ.filter (fun i : Fin n => i.val < m)), f i) :=
  parity_original_Q_fin_prefix_eq_nat_range434 m hm f


/-- Exact original Q-ordered suffix, identifying true Fin labels later
than i with the remaining natural-indexed logarithmic prime mass. -/
theorem parity_original_Q_fin_suffix_eq_nat_remaining434
    {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    parityOriginalEq44Remaining434
      (fun k => if hk : k < n then f ⟨k,hk⟩ else 0)
      n (i.val+1) =
      ∑ j ∈ ((Finset.univ : Finset (Fin n)).filter (fun j => i < j)), f j := by
  classical
  unfold parityOriginalEq44Remaining434
  rw [Finset.sum_range_sub_sum_range (Nat.succ_le_of_lt i.isLt)]
  apply Finset.sum_bij
      (fun k hk => (⟨k,(Finset.mem_range.mp (Finset.mem_filter.mp hk).1)⟩ : Fin n))
  · intro k hk
    have h := (Finset.mem_filter.mp hk).2
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact_mod_cast h
  · intro k hk l hl heq
    exact congrArg Fin.val heq
  · intro j hj
    have h : i.val+1 ≤ j.val := by
      exact Nat.succ_le_of_lt (Finset.mem_filter.mp hj).2
    refine ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt,h⟩,?_⟩
    exact Fin.ext rfl
  · intro k hk
    simp [dif_pos (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)]
end Green64Analytic.Parity

end

end

/-! ## OriginalFinUpperResidual -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Parity(4.4) upper residual invariant on the EXACT original ordered
Fin n labelled Q slots. The physical hypotheses are only total
remaining Q capacity and genuine per-slot suffix supply; *both* are
proved independently for actual source Q geometries on retained tuples.
The skip step follows from native B590 f0 support, not from a guessed
upper residual assumption. -/
theorem parity_original_Q_all_positive_branch_upper_residual434
    {n : ℕ} (E B : ℝ) (s : Fin n → ℝ)
    (δ : Fin n → Bool) (p : Fin n → ℕ)
    (hB : 0 ≤ B)
    (hScales : ∀ i, 0 < s i)
    (hWeight : parityOriginalQAllocationBranchWeight434 20 E s δ p ≠ 0)
    (hTotal : Real.log E ≤ ∑ i : Fin n, Real.log (p i : ℝ))
    (hTail : ∀ i : Fin n,
      Real.log (p i : ℝ) + s i ≤
        (∑ j ∈ (Finset.univ.filter (fun j : Fin n => i < j)),
          Real.log (p j : ℝ)) + B)
    (i : Fin n) :
    parityOriginalQAllocationResidual434 E δ p i ≤
      (∑ j ∈ (Finset.univ.filter (fun j : Fin n => i ≤ j)),
        Real.log (p j : ℝ)) + B := by
  classical
  let dN : ℕ → Bool := fun k => if hk : k < n then δ ⟨k,hk⟩ else false
  let pN : ℕ → ℝ := fun k => if hk : k < n then Real.log (p ⟨k,hk⟩ : ℝ) else 0
  let sN : ℕ → ℝ := fun k => if hk : k < n then s ⟨k,hk⟩ else 0
  have hAll : Real.log E ≤ ∑ k ∈ Finset.range n, pN k := by
    change Real.log E ≤ ∑ k ∈ Finset.range n,
      if hk : k < n then Real.log (p ⟨k,hk⟩ : ℝ) else 0
    calc
      Real.log E ≤ ∑ z : Fin n, Real.log (p z : ℝ) := hTotal
      _ = _ := Finset.sum_fin_eq_sum_range (fun z : Fin n => Real.log (p z : ℝ))
  have hSkip : ∀ j < n, dN j = false →
      parityOriginalEq44PrefixResidual434 E dN pN j < pN j + sN j := by
    intro j hj hdj
    let q : Fin n := ⟨j,hj⟩
    have hδ : δ q = false := by simpa [dN,q,hj] using hdj
    have hS := parity_original_Q_smooth_positive_skip_slot_budget434
      20 E s δ p hScales hWeight q hδ
    have hPrefix : parityOriginalEq44PrefixResidual434 E dN pN j =
        parityOriginalQAllocationResidual434 E δ p q := by
      unfold parityOriginalEq44PrefixResidual434 parityOriginalQAllocationResidual434
      congr 1
      calc
        (∑ k ∈ Finset.range j, if dN k then pN k else 0) =
          (∑ k ∈ Finset.range j,
            if hk : k < n then
              (if δ ⟨k,hk⟩ then Real.log (p ⟨k,hk⟩ : ℝ) else 0)
            else 0) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hlt : k < n := lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.le_of_lt hj)
              simp [dN,pN,hlt]
        _ = _ := parity_original_Q_fin_prefix_eq_nat_range434 j (Nat.le_of_lt hj)
          (fun z : Fin n => if δ z then Real.log (p z : ℝ) else 0)
    rw [hPrefix]
    simpa [pN,sN,q,hj] using hS
  have hSupply : ∀ j < n, pN j + sN j ≤
      parityOriginalEq44Remaining434 pN n (j+1) + B := by
    intro j hj
    let q : Fin n := ⟨j,hj⟩
    have hsuffix := parity_original_Q_fin_suffix_eq_nat_remaining434
      q (fun z => Real.log (p z : ℝ))
    have hT := hTail q
    change parityOriginalEq44Remaining434 pN n (j+1) = _ at hsuffix
    rw [hsuffix]
    simpa [pN,sN,q,hj, add_assoc, add_comm, add_left_comm] using hT
  have hResult := parity_original_eq44_upper_all_prefixes_of_skip_supply434
    E B n dN pN sN hB hAll hSkip hSupply i.val i.isLt.le
  have hPrefix : parityOriginalEq44PrefixResidual434 E dN pN i.val =
      parityOriginalQAllocationResidual434 E δ p i := by
    unfold parityOriginalEq44PrefixResidual434 parityOriginalQAllocationResidual434
    congr 1
    calc
      (∑ k ∈ Finset.range i.val, if dN k then pN k else 0) =
        (∑ k ∈ Finset.range i.val,
          if hk : k < n then
            (if δ ⟨k,hk⟩ then Real.log (p ⟨k,hk⟩ : ℝ) else 0)
          else 0) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hlt : k < n := lt_of_lt_of_le (Finset.mem_range.mp hk) i.isLt.le
            simp [dN,pN,hlt]
      _ = _ := parity_original_Q_fin_prefix_eq_nat_range434 i.val i.isLt.le
        (fun z : Fin n => if δ z then Real.log (p z : ℝ) else 0)
  have hRemaining : parityOriginalEq44Remaining434 pN n i.val =
      ∑ j ∈ (Finset.univ.filter (fun j : Fin n => i ≤ j)),
        Real.log (p j : ℝ) := by
    unfold parityOriginalEq44Remaining434
    rw [Finset.sum_range_sub_sum_range i.isLt.le]
    apply Finset.sum_bij
      (fun k hk => (⟨k,(Finset.mem_range.mp (Finset.mem_filter.mp hk).1)⟩ : Fin n))
    · intro k hk
      have h := (Finset.mem_filter.mp hk).2
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact_mod_cast h
    · intro k hk l hl heq
      exact congrArg Fin.val heq
    · intro j hj
      have h : i.val ≤ j.val := by exact_mod_cast (Finset.mem_filter.mp hj).2
      refine ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt,h⟩,?_⟩
      exact Fin.ext rfl
    · intro k hk
      simp [pN, dif_pos (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)]
  rw [hPrefix,hRemaining] at hResult
  exact hResult
end Green64Analytic.Parity

end

end

/-! ## OriginalActualEq44SuffixCapacity -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 34000

/-- Original Parity(4.4) actual Q-suffix supply with the EXACT endpoint
constant (c2+1)*s_last=(11/5)*s_last, not the coarser 88 log L:
all earlier bands have 19 next-band prime marks, while the final band
requires only the immediate original Q_j prime interval and positivity
of its suffix. Valid for EVERY d and each reserved Q label. -/
theorem parity_original_actual_Q_suffix_capacity_eq44_434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (p : (i : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length) → {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i})
    (i : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length) :
    Real.log ((p i).val : ℝ) + sourceActualSortedFrequencyScales 20 d L band slot i ≤
      (∑ j ∈ (Finset.univ.filter (fun j : Fin
        (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length => i < j)),
        Real.log ((p j).val : ℝ)) +
      (11/5:ℝ)*sourceOriginalPGroupScale 20 L d := by
  let b := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
    band slot i).val.1
  have hBd : b.val ≤ d := by have h:=b.isLt; omega
  by_cases hEarly : b.val < d
  · have hEarlyMass := parity_actual_Q_early_band_tail_covers_slot434
      d L hL band slot p i hEarly
    have hLastPos := source_original_positive_dyadic_scale 20 d L (by norm_num) hL
    linarith
  · have hb : b.val = d := by omega
    have hQ : (p i).val ∈ sourceOriginalQActualBands 20 d L b := (p i).property
    have hPrime := source_original_Q_actual_prime 20 d L b (p i).val hQ
    have hUp := (source_original_Q_actual_prime_range 20 d L
      (by norm_num) b (p i).val hQ).2
    have hLog : Real.log ((p i).val : ℝ) ≤
        (6/5:ℝ)*sourceOriginalPGroupScale 20 L d := by
      have h := (Real.log_le_iff_le_exp (by exact_mod_cast hPrime.pos)).mpr hUp
      rw [hb] at h
      exact h
    have hTailPos : 0 ≤
      ∑ j ∈ (Finset.univ.filter (fun j : Fin
        (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length => i < j)),
        Real.log ((p j).val : ℝ) := by
      apply Finset.sum_nonneg
      intro j hj
      let c := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
        band slot j).val.1
      have hp := source_original_Q_actual_prime 20 d L c (p j).val (p j).property
      exact Real.log_nonneg (by exact_mod_cast hp.one_le)
    change Real.log ((p i).val : ℝ) + sourceOriginalPGroupScale 20 L b.val ≤ _
    rw [hb]
    linarith
end Green64Analytic.Parity

end

end

/-! ## OriginalSingleGateBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- An individual nonzero TRUE original B590 f1 gate cannot select
more prime logarithmic mass than the current residual: the precise
zero-support of native `Real.smoothTransition` enforces R > log p.
This is deliberately local, not conditioned on a complete branch. -/
theorem parity_original_B590_one_nonzero_f1_selected_budget434
    (r : ℕ) (R logp s : ℝ) (hs : 0 < s)
    (hGate : sourceBufferedGateReal r true ((R-logp)/s) ≠ 0) :
    logp < R := by
  have hGamma : Real.smoothTransition ((R-logp)/s) ≠ 0 := by
    intro hZero
    apply hGate
    simp [sourceBufferedGateReal,hZero]
  have hArg : 0 < (R-logp)/s := by
    by_contra h
    exact hGamma (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
  have hNum := (div_pos_iff_of_pos_right hs).mp hArg
  linarith
end Green64Analytic.Parity

end

end

/-! ## ActualOriginalASmoothRange -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 32000

/-- A genuine nonzero ORIGINAL `sourceOriginalA` coefficient at physical
u (rather than a synthetic Q tuple) furnishes its actual complete Q
assignment, exact retained Q/P factorisation and, for EVERY positive
B590 smooth allocation branch, the FULL original Parity (4.5) e range.
All r=20 original moving Q bands and sorted marks are preserved.
No additional Q-mass assumption or odd-e assumption is made.

The explicit physical gates are `exp L<=u`, original Ppart in the exact
B537 cutoff `floor(exp(L/44))`, and E<=exp(19L/20); general arbitrary
Parity b_* and the historical a_e phase decomposition remain to bridge. -/
theorem parity_eventually_original_A_actual_smooth_e_range434 :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      ∀ E : ℝ, 1 ≤ E → E ≤ Real.exp ((19/20:ℝ)*L) →
      ∀ u : ℕ,
      sourceOriginalA 20
        (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
        (sourceOriginalPAllActualBands 20 L) u ≠ 0 →
      Real.exp L ≤ (u:ℝ) →
      sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
        sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊ →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20),
      ∃ f : (j : Fin (sourceOriginalLiteralDepth 20 L+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20
          (sourceOriginalLiteralDepth 20 L) L j},
        (∏ j, ∏ i, (f j i).val) =
          sourceOriginalOrdinaryPart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∧
        ∀ (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool),
        let p := parityActualSourceRemainingFullQTuple434
          (sourceOriginalLiteralDepth 20 L) L band slot f
        parityOriginalQAllocationBranchWeight434 20 E
          (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
            band slot) δ (fun i => (p i).val) ≠ 0 →
        let e := paritySourceOrderedAllocatedE434 δ p
        E*L^((-88:ℝ)) ≤ (e:ℝ) ∧ (e:ℝ) ≤ E ∧ Odd e ∧
        IsUnit (e : ZMod 2) ∧
        sourceOriginalPParityExponent
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) e = 0 ∧
        ∀ v : ℕ, v ≠ 0 →
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) (e*v) =
            sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v := by
  filter_upwards [parity_eventually_actual_smooth_e_full_range_of_Q_mass434]
    with L hRange
  refine ⟨hRange.1,?_⟩
  intro E hE hEcap u hA hLarge hPcap band slot
  have hu : u ≠ 0 := by
    intro hZero
    apply hA
    simpa only [hZero] using (b640_original_A_zero434 20
      (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
      (sourceOriginalPAllActualBands 20 L))
  obtain ⟨f,hf⟩ := parity_original_A_nonzero_full_Q_slots_witness434
    20 (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
    (sourceOriginalPAllActualBands 20 L) u hA
  have hQLower := parity_actual_original_full_Q_tuple_source_physical_mass434
    (sourceOriginalLiteralDepth 20 L) L (by linarith [hRange.1])
    u hu hLarge hPcap f hf band slot
  let p := parityActualSourceRemainingFullQTuple434
    (sourceOriginalLiteralDepth 20 L) L band slot f
  have hEFull : E ≤ ((∏ i, (p i).val : ℕ) : ℝ) := hEcap.trans hQLower
  refine ⟨f,hf,?_⟩
  intro δ
  dsimp only
  intro hWeight
  exact hRange.2 E hE band slot δ p hEFull hWeight
end Green64Analytic.Parity

end

end

/-! ## ActualSmoothEFibreRange -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 34000

/-- The ACTUAL B590-smoothed complex a_e-like SOURCE FIBRE vanishes
BELOW the original Parity(4.5) range whenever the additional original
Fourier/physical amplitude is supported on retained ordinary Q mass.
No positivity of complex phase, and no conditional Q-tail input: the
entire 19-next-band source geometry was proved independently. The sole
remaining physically grounded obligation is exactly phase-support
`E <= product(unreserved Q)`, NOT a substitute bound on e itself. -/
theorem parity_eventually_actual_smooth_e_fibre_below_range_zero434 :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      ∀ (E : ℝ), 1 ≤ E →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (phase :
          (Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → Bool) →
          ((i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length) →
            {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
              L band slot i}) → ℂ),
      (∀ delta p, phase delta p ≠ 0 →
        E ≤ ((∏ i, (p i).val : ℕ) : ℝ)) →
      ∀ e : ℕ, (e:ℝ) < E*L^((-88:ℝ)) →
        parityActualSortedQSmoothEFibre434 L E band slot phase e=0 := by
  filter_upwards [parity_eventually_actual_smooth_e_full_range_of_Q_mass434]
    with L hRange
  refine ⟨hRange.1,?_⟩
  intro E hE band slot phase hMassSupport e heBelow
  unfold parityActualSortedQSmoothEFibre434
    paritySourceOrderedAllocatedEFibre434 sourceEndpointFibre
  apply Finset.sum_eq_zero
  intro x hx
  have hMatch : paritySourceOrderedAllocatedE434 x.1 x.2=e :=
    (Finset.mem_filter.mp hx).2
  let gate := parityOriginalQAllocationBranchWeight434 20 E
    (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
      band slot) x.1 (fun i => (x.2 i).val)
  by_cases hGate : gate=0
  · simp [gate] at hGate ⊢
    simp [hGate]
  by_cases hPhase : phase x.1 x.2=0
  · simp [hPhase]
  have hFull := hMassSupport x.1 x.2 hPhase
  have hLower := (hRange.2 E hE band slot x.1 x.2 hFull hGate).1
  rw [hMatch] at hLower
  exact False.elim ((not_le_of_gt heBelow) hLower)
end Green64Analytic.Parity

end

end

/-! ## ActualFourierSmoothEFibre -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 34000

/-- LITERAL SOURCE original B509 Fourier/factorial QSkip phase, evaluated
on the full original ordered Q assignment, restricted to δ=false
primes by `OrderedQSkip`. The exact same `sourceActualSortedFactorial`
and `orderedSkipPhase` appear in `sourceNativePrimeCore.residual`.
An extra factor keeps all subsequent original branch/physical weights;
no surrogate Fourier character or dropped factorial is introduced. -/
def parityActualSourceFourierSmoothPhase434
    (L : ℝ)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → ℝ)
    (extra :
      (Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) →
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) → ℂ)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → Bool)
    (p : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) : ℂ :=
  sourceActualSortedFactorial 20 (sourceOriginalLiteralDepth 20 L) *
    orderedSkipPhase (δ := δ)
      (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
        band slot) ξ (fun i => p i.val) * extra δ p

/-- The actual Q-allocation e-indexed coefficient WITH the exact native
original Fourier/factorial QSkip phase and the genuine B590 smooth gate.
The unspecified extra physical factor is explicit rather than silently
identified with historical Parity a_e (4.7). -/
def parityActualSourceFourierSmoothEFibre434
    (L E : ℝ)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → ℝ)
    (extra :
      (Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) →
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) → ℂ)
    (e : ℕ) : ℂ :=
  parityActualSortedQSmoothEFibre434 L E band slot
    (parityActualSourceFourierSmoothPhase434 L band slot ξ extra) e

/-- The exact source-skip Fourier weighted finite Q allocation is
reindexed by e without altering the native factorial or character. -/
theorem parity_actual_source_fourier_smooth_e_fibre_reindex434
    (L E : ℝ)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → ℝ)
    (extra :
      (Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) →
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) → ℂ) :
    (∑ x :
      ((Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) ×
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i})),
      (parityOriginalQAllocationBranchWeight434 20 E
        (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
          band slot) x.1 (fun i => (x.2 i).val) : ℂ) *
      parityActualSourceFourierSmoothPhase434 L band slot ξ extra x.1 x.2) =
    ∑ e ∈ paritySourceOrderedAllocatedESupport434
      (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot),
      parityActualSourceFourierSmoothEFibre434 L E band slot ξ extra e := by
  exact parity_actual_sorted_Q_smooth_e_fibre_reindex434 L E band slot
    (parityActualSourceFourierSmoothPhase434 L band slot ξ extra)

/-- The source-original B509 Fourier/factorial e-fibre vanishes above
Parity(4.5) cap for every phase and every retained physical weight. -/
theorem parity_actual_source_fourier_smooth_e_above_cap_zero434
    (L E : ℝ) (hL : 0 < L) (hE : 1 ≤ E)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → ℝ)
    (extra :
      (Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) →
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) → ℂ)
    (e : ℕ) (he : E < (e:ℝ)) :
    parityActualSourceFourierSmoothEFibre434 L E band slot ξ extra e=0 :=
  parity_actual_sorted_Q_smooth_e_fibre_above_cap_zero434 L E hL hE band slot
    (parityActualSourceFourierSmoothPhase434 L band slot ξ extra) e he

/-- Every literal B509 Fourier/factorial smoothly allocated-e coefficient
BELOW E*L^-88 is zero when the additional PHYSICAL retained amplitude
is supported on the original full-Q-product mass E<=prod Q.
The Fourier phase, normalizer and smooth branch gate are literal source
objects; no positivity of an oscillatory amplitude is assumed. -/
theorem parity_eventually_actual_source_fourier_smooth_e_below_cap_zero434 :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      ∀ (E : ℝ), 1 ≤ E →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (extra :
          (Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → Bool) →
          ((i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length) →
            {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
              L band slot i}) → ℂ),
      (∀ δ p, extra δ p ≠ 0 → E ≤ ((∏ i, (p i).val : ℕ) : ℝ)) →
      ∀ e : ℕ, (e:ℝ) < E*L^((-88:ℝ)) →
        parityActualSourceFourierSmoothEFibre434 L E band slot ξ extra e=0 := by
  filter_upwards [parity_eventually_actual_smooth_e_fibre_below_range_zero434]
    with L hBelow
  refine ⟨hBelow.1,?_⟩
  intro E hE band slot ξ extra hExtraMass e he
  have hPhaseMass : ∀ δ p,
      parityActualSourceFourierSmoothPhase434 L band slot ξ extra δ p ≠ 0 →
      E ≤ ((∏ i, (p i).val : ℕ) : ℝ) := by
    intro δ p hPhase
    apply hExtraMass δ p
    intro hZero
    apply hPhase
    simp [parityActualSourceFourierSmoothPhase434,hZero]
  exact hBelow.2 E hE band slot
    (parityActualSourceFourierSmoothPhase434 L band slot ξ extra)
    hPhaseMass e he
end Green64Analytic.Parity

end

end

/-! ## OriginalFullFourierPhaseSplit -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 32000

/-- Exact ORIGINAL B509 Q-slot Fourier phase for ALL labelled original
Q primes, without dropping the primes allocated to e. It has the
SOURCE `Real.fourierChar` convention (frequency 2π) and exact
`sourceSlotFrequency`, not a fabricated formal character. -/
def paritySourceFullSlotFourierPhase434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i}) : ℂ :=
  ∏ i : Fin n, ((Real.fourierChar
    (Real.log ((p i).val : ℝ) * sourceSlotFrequency s ξ δ i) : Circle) : ℂ)

/-- ORIGINAL source Fourier phase carried by Q primes allocated into e.
This exact phase is the algebraic `a_e`-side input BEFORE the rest of
the Parity Fourier transform and Mellin allocation are integrated. -/
def paritySourceAllocatedSlotFourierPhase434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i}) : ℂ :=
  ∏ i ∈ (Finset.univ.filter (fun i : Fin n => δ i = true)),
    ((Real.fourierChar
      (Real.log ((p i).val : ℝ) * sourceSlotFrequency s ξ δ i) : Circle) : ℂ)

/-- Every original B509 Q-slot Fourier factor splits EXACTLY between
selected e primes and the native source `orderedSkipPhase` for the
complementary Q primes. This is a real full-source identity, including
all repeated Q primes; it is not a Fourier asymptotic or an assumed
external Parity correlation theorem. -/
theorem parity_source_full_slot_fourier_phase_split434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i}) :
    paritySourceFullSlotFourierPhase434 s ξ δ p =
      paritySourceAllocatedSlotFourierPhase434 s ξ δ p *
        orderedSkipPhase (δ := δ) s ξ
          (fun i : {i : Fin n // ¬δ i = true} => p i.val) := by
  classical
  let f : Fin n → ℂ := fun i =>
    ((Real.fourierChar
      (Real.log ((p i).val : ℝ) * sourceSlotFrequency s ξ δ i) : Circle) : ℂ)
  have hSkipped :
      orderedSkipPhase (δ := δ) s ξ
        (fun i : {i : Fin n // ¬δ i = true} => p i.val) =
      ∏ i ∈ (Finset.univ.filter (fun i : Fin n => ¬δ i = true)), f i := by
    unfold orderedSkipPhase
    exact (Finset.prod_subtype
      (s := Finset.univ.filter (fun i : Fin n => ¬δ i = true))
      (p := fun i : Fin n => ¬δ i = true)
      (by intro i; simp)
      f).symm
  unfold paritySourceFullSlotFourierPhase434
    paritySourceAllocatedSlotFourierPhase434
  change (∏ i : Fin n, f i) =
    (∏ i ∈ (Finset.univ.filter (fun i : Fin n => δ i = true)), f i) *
      orderedSkipPhase (δ := δ) s ξ
        (fun i : {i : Fin n // ¬δ i = true} => p i.val)
  rw [hSkipped]
  exact (Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset (Fin n)) (fun i : Fin n => δ i = true) f).symm

/-- Source factorial normalization in `sourceNativePrimeCore.residual`
is EXACTLY the full ORIGINAL all-Q Fourier phase with the selected-e
Fourier phase kept outside. We do not replace `sourceActualSortedFactorial`
with a guessed 20! weight. This is the one missing factor that needs to
be carried into the historical `a_e` identification after Fourier
separation. -/
theorem parity_source_full_slot_fourier_factorial_split434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (r d : ℕ) (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i}) :
    sourceActualSortedFactorial r d *
      paritySourceFullSlotFourierPhase434 s ξ δ p =
      paritySourceAllocatedSlotFourierPhase434 s ξ δ p *
        (sourceActualSortedFactorial r d *
          orderedSkipPhase (δ := δ) s ξ
            (fun i : {i : Fin n // ¬δ i = true} => p i.val)) := by
  rw [parity_source_full_slot_fourier_phase_split434]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalFullFourierEFibre -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 33000

/-- The COMPLETE original Q-Fourier factor at the native B509
`sourceSlotFrequency` for ALL primes, including selected e primes,
with the actual B590 smoothed source gate and unchanged complex
physical/endpoint weights. Unlike the partial skipped source residual,
this phase has no selected Fourier factor missing. -/
def parityActualSourceFullFourierSmoothedBranch434
    (L E : ℝ)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → ℝ)
    (extra :
      (Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) →
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) → ℂ)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → Bool)
    (p : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) : ℂ :=
  (parityOriginalQAllocationBranchWeight434 20 E
    (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
      band slot) δ (fun i => (p i).val) : ℂ) *
    (sourceActualSortedFactorial 20 (sourceOriginalLiteralDepth 20 L) *
      paritySourceFullSlotFourierPhase434
        (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
          band slot) ξ δ p) * extra δ p

/-- Exactly the source selected-e Fourier factors needed to restore
FULL original Q-Fourier phase from the B509 native skipped-Q residual.
The remaining physical amplitude is copied unchanged. -/
def parityActualSourceSelectedFourierExtra434
    (L : ℝ)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → ℝ)
    (extra :
      (Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) →
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) → ℂ)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → Bool)
    (p : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) : ℂ :=
  paritySourceAllocatedSlotFourierPhase434
    (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
      band slot) ξ δ p * extra δ p

/-- Pointwise exact equality of the literal FULL B509 Fourier phase
with the candidate B590/B509 skipped-phase Q carrier after restoring
ONLY the actual selected-slot Fourier factors. This equality holds
for every δ and prime assignment, with no positivity of extra. -/
theorem parity_actual_original_full_fourier_branch_eq_source_split434
    (L E : ℝ)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → ℝ)
    (extra :
      (Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) →
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) → ℂ)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → Bool)
    (p : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) :
    parityActualSourceFullFourierSmoothedBranch434 L E band slot ξ extra δ p =
      (parityOriginalQAllocationBranchWeight434 20 E
        (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
          band slot) δ (fun i => (p i).val) : ℂ) *
      parityActualSourceFourierSmoothPhase434 L band slot ξ
        (parityActualSourceSelectedFourierExtra434 L band slot ξ extra) δ p := by
  unfold parityActualSourceFullFourierSmoothedBranch434
    parityActualSourceFourierSmoothPhase434
    parityActualSourceSelectedFourierExtra434
  rw [parity_source_full_slot_fourier_factorial_split434]
  ring

/-- Genuine COMPLETE B509 Q-Fourier and B590 allocation sum, with ALL
labelled source Q primes, is exactly its finite e-coefficient regrouping
using the already native `sourceEndpointFibre` and the restored
selected-slot phase. This is the physical Fourier algebra interface
needed for Parity (4.7), not yet the full original a_e equality involving
the reserved prime/P group Fourier integrals. -/
theorem parity_actual_original_full_fourier_smoothed_e_reindex434
    (L E : ℝ)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → ℝ)
    (extra :
      (Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) →
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) → ℂ) :
    (∑ x :
      ((Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) ×
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i})),
      parityActualSourceFullFourierSmoothedBranch434 L E band slot ξ extra x.1 x.2) =
    ∑ e ∈ paritySourceOrderedAllocatedESupport434
      (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot),
      parityActualSourceFourierSmoothEFibre434 L E band slot ξ
        (parityActualSourceSelectedFourierExtra434 L band slot ξ extra) e := by
  have hReindex := parity_actual_source_fourier_smooth_e_fibre_reindex434 L E
    band slot ξ (parityActualSourceSelectedFourierExtra434 L band slot ξ extra)
  rw [←hReindex]
  apply Finset.sum_congr rfl
  intro x hx
  exact parity_actual_original_full_fourier_branch_eq_source_split434
    L E band slot ξ extra x.1 x.2
end Green64Analytic.Parity

end

end

/-! ## OriginalFourierLogIdentity -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 34000

/-- Exact finite Fubini interchange behind Parity §4.2:
`sum_{i} b_i sum_{j < i} a_j = sum_{j} a_j sum_{i>j} b_i`.
The original selected-slot condition is kept in a_j and does not
assume distinct primes or nonzero frequencies. -/
theorem parity_original_fourier_ordered_double_sum_swap434
    {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i : Fin n, b i *
      (∑ j : Fin n, if j < i then a j else 0)) =
    ∑ j : Fin n, a j *
      (∑ i : Fin n, if j < i then b i else 0) := by
  calc
    (∑ i : Fin n, b i *
      (∑ j : Fin n, if j < i then a j else 0)) =
      ∑ i : Fin n, ∑ j : Fin n,
        (if j < i then b i*a j else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring
    _ = ∑ j : Fin n, ∑ i : Fin n,
        (if j < i then a j*b i else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> ring
    _ = ∑ j : Fin n, a j *
      (∑ i : Fin n, if j < i then b i else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> ring

/-- EXACT Parity §4.2 source Fourier exponent identity, before applying
the multiplicative Fourier character:
`sum_i (xi_i/s_i)*(R_i-log p_i)
 = log E * sum_i xi_i/s_i + sum_j log p_j * sigma_j`,
with R_i the ORIGINAL positive-weight allocation residual and
`sigma_j=sourceSlotFrequency s xi delta j` the literal B509 source
frequency. This is mathematical finite Fubini, not an approximate
Fourier tail; the source character convention has 2π in the exponent. -/
theorem parity_original_fourier_log_exponent_eq_source_slot_freq434
    {n : ℕ} (E : ℝ)
    (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (p : Fin n → ℕ) :
    (∑ i : Fin n, (ξ i / s i) *
      (parityOriginalQAllocationResidual434 E δ p i - Real.log (p i : ℝ))) =
    Real.log E * (∑ i : Fin n, ξ i / s i) +
      ∑ j : Fin n, Real.log (p j : ℝ) * sourceSlotFrequency s ξ δ j := by
  let a : Fin n → ℝ := fun j => if δ j then Real.log (p j : ℝ) else 0
  let b : Fin n → ℝ := fun i => ξ i / s i
  have hResidual (i : Fin n) :
      parityOriginalQAllocationResidual434 E δ p i =
      Real.log E - (∑ j : Fin n, if j < i then a j else 0) := by
    simp [parityOriginalQAllocationResidual434,a,Finset.sum_filter]
  have hFreq (j : Fin n) :
      Real.log (p j : ℝ) * sourceSlotFrequency s ξ δ j =
      -Real.log (p j : ℝ)*b j -
        a j * (∑ i : Fin n, if j < i then b i else 0) := by
    cases hδ : δ j with
    | false =>
      simp [sourceSlotFrequency,a,b,hδ]
      ring
    | true =>
      simp [sourceSlotFrequency,a,b,hδ]
      ring
  calc
    (∑ i : Fin n, (ξ i / s i) *
      (parityOriginalQAllocationResidual434 E δ p i - Real.log (p i : ℝ))) =
      ∑ i : Fin n, b i *
        (Real.log E - (∑ j : Fin n, if j < i then a j else 0) -
          Real.log (p i : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hResidual]
    _ = Real.log E * (∑ i : Fin n, b i) -
        (∑ j : Fin n, a j *
          (∑ i : Fin n, if j < i then b i else 0)) -
        (∑ i : Fin n, Real.log (p i : ℝ)*b i) := by
        rw [←parity_original_fourier_ordered_double_sum_swap434 a b]
        simp only [mul_sub,Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul]
        have hComm : (∑ x : Fin n, b x * Real.log (p x : ℝ)) =
            ∑ x : Fin n, Real.log (p x : ℝ) * b x := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        rw [hComm]
        ring
    _ = Real.log E * (∑ i : Fin n, ξ i / s i) +
      ∑ j : Fin n, Real.log (p j : ℝ) * sourceSlotFrequency s ξ δ j := by
        have hFreqTotal :
            (∑ j : Fin n, Real.log (p j : ℝ) * sourceSlotFrequency s ξ δ j) =
              -(∑ j : Fin n, Real.log (p j : ℝ) * b j) -
              (∑ j : Fin n, a j * (∑ i : Fin n, if j < i then b i else 0)) := by
          rw [Finset.sum_congr rfl (fun j hj => hFreq j)]
          rw [Finset.sum_sub_distrib]
          congr 1
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        change Real.log E * (∑ i : Fin n, b i) -
            (∑ j : Fin n, a j * (∑ i : Fin n, if j < i then b i else 0)) -
            (∑ i : Fin n, Real.log (p i : ℝ)*b i) =
            Real.log E * (∑ i : Fin n, b i) +
              (∑ j : Fin n, Real.log (p j : ℝ) * sourceSlotFrequency s ξ δ j)
        rw [hFreqTotal]
        ring
end Green64Analytic.Parity

end

end

/-! ## OriginalFourierCharacterIdentity -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

/-- Multiplicative property of the ACTUAL source's `Real.fourierChar`
in the `Circle → ℂ` embedding, preserving its 2π normalisation.
No hypothetical replacement with the historical exp(iξt) convention. -/
theorem parity_source_fourierChar_finset_sum_to_complex_prod434
    {ι : Type} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) :
    ((Real.fourierChar (∑ i ∈ S, f i) : Circle) : ℂ) =
      ∏ i ∈ S, ((Real.fourierChar (f i) : Circle) : ℂ) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty,Finset.prod_empty,
      AddChar.map_zero_eq_one, Circle.coe_one]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,
      AddChar.map_add_eq_mul,Circle.coe_mul,ih]

/-- The source Fourier exponential of the *actual Parity smooth allocation*
product of gate characters is EXACTLY the original global prefactor
`log E sum_i ξ_i/s_i` times the FULL labelled source B509 slot phase
`sourceSlotFrequency(s,ξ,δ)`. This is Parity manuscript §4.2 line
634-640, with the source Fourier character's precise 2π convention.
The selected e-prime phases are INCLUDED, not silently discarded. -/
theorem parity_original_smooth_gate_fourier_character_exact434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (E : ℝ) (s ξ : Fin n → ℝ)
    (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i}) :
    ((Real.fourierChar
      (∑ i : Fin n, (ξ i / s i) *
        (parityOriginalQAllocationResidual434 E δ
          (fun j => (p j).val) i - Real.log ((p i).val : ℝ))) : Circle) : ℂ) =
    ((Real.fourierChar
      (Real.log E * (∑ i : Fin n, ξ i / s i)) : Circle) : ℂ) *
      paritySourceFullSlotFourierPhase434 s ξ δ p := by
  have hLog := parity_original_fourier_log_exponent_eq_source_slot_freq434
    E s ξ δ (fun j => (p j).val)
  rw [hLog,AddChar.map_add_eq_mul,Circle.coe_mul]
  unfold paritySourceFullSlotFourierPhase434
  rw [parity_source_fourierChar_finset_sum_to_complex_prod434
    (Finset.univ : Finset (Fin n))
    (fun i => Real.log ((p i).val : ℝ) * sourceSlotFrequency s ξ δ i)]

/-- Parity §4.2 source gate Fourier character decomposes EXACTLY into
its unchanged global phase, e-selected Fourier factors and the B509
original unselected-slot Fourier factor `orderedSkipPhase`.
This is the strict SOURCE Fourier algebra of eq(4.7), still before
proving historical a_e separability, Fourier tail or TypeII. -/
theorem parity_original_smooth_gate_fourier_character_split434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (E : ℝ) (s ξ : Fin n → ℝ)
    (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i}) :
    ((Real.fourierChar
      (∑ i : Fin n, (ξ i / s i) *
        (parityOriginalQAllocationResidual434 E δ
          (fun j => (p j).val) i - Real.log ((p i).val : ℝ))) : Circle) : ℂ) =
    ((Real.fourierChar
      (Real.log E * (∑ i : Fin n, ξ i / s i)) : Circle) : ℂ) *
      paritySourceAllocatedSlotFourierPhase434 s ξ δ p *
      orderedSkipPhase (δ := δ) s ξ
        (fun i : {i : Fin n // ¬δ i = true} => p i.val) := by
  rw [parity_original_smooth_gate_fourier_character_exact434,
    parity_source_full_slot_fourier_phase_split434]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalFourierNormalization -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

/-- EXACT Fourier-unit conversion between Lean's B509 character
`Real.fourierChar(z)=exp(2π i z)` and Parity's original manuscript
§4.2 convention `exp(i t)`: divide the REAL character argument by
`2π`. This conversion is proved, not silently assumed in a_e phases. -/
theorem parity_original_fourier_2pi_normalization_exact434 (t : ℝ) :
    ((Real.fourierChar (t/(2*Real.pi)) : Circle) : ℂ) =
      Complex.exp ((t:ℂ)*Complex.I) := by
  change ((Circle.exp (2*Real.pi*(t/(2*Real.pi))) : Circle) : ℂ) = _
  have h : 2*Real.pi*(t/(2*Real.pi)) = t := by
    field_simp [Real.pi_ne_zero]
  rw [h]
  exact Circle.coe_exp t

/-- Source B509 `Real.fourierChar` at frequency `ξ/(2π)` is exactly
the historical Parity (4.7) character `exp(i ξ t)` at arbitrary real
a and t, including negative frequencies and all Q prime logs. -/
theorem parity_original_fourier_character_convention_bridge434
    (xi t : ℝ) :
    ((Real.fourierChar ((xi*t)/(2*Real.pi)) : Circle) : ℂ) =
      Complex.exp (Complex.I*((xi*t:ℝ):ℂ)) := by
  rw [parity_original_fourier_2pi_normalization_exact434]
  congr 1
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalBufferedGateFourierInversion -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff RealInnerProductSpace
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The GENUINE ORIGINAL B590 f0 and f1, not a proxy bump or an
independent artificial Fourier gate, satisfy literal real Fourier
inversion with Mathlib convention `exp(2πi ξ t)` and Lebesgue measure.
The source defines `sourceBufferedGate r d` as a Schwartz map from its
actual C∞ compact ζ_r γ_r products; no assumed smoothness or decay.
Parity's manuscript `exp(i ξ t) dξ/(2π)` is obtained by ξ↦ξ/(2π).
This theorem is pointwise, before simultaneous N-slot integration or
any frequency tail bounds in original Eq.(4.6). -/
theorem parity_original_source_B590_single_gate_fourier_inversion434
    (r : ℕ) (δ : Bool) (t : ℝ) :
    ((sourceBufferedGateReal r δ t : ℝ) : ℂ) =
      ∫ ξ : ℝ,
        Complex.exp (((2*Real.pi*ξ*t : ℝ):ℂ)*Complex.I) *
          (𝓕 (sourceBufferedGate r δ) : 𝓢(ℝ,ℂ)) ξ := by
  let f := sourceBufferedGate r δ
  have hInv : (𝓕⁻ (𝓕 f : 𝓢(ℝ,ℂ))) t = f t := by
    rw [FourierTransform.fourierInv_fourier_eq]
  calc
    _ = f t := rfl
    _ = (𝓕⁻ (𝓕 f : 𝓢(ℝ,ℂ))) t := hInv.symm
    _ = _ := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [Real.inner_apply]
      simp only [smul_eq_mul]
      congr 1
      push_cast
      ring
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierL1 -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The REAL original B590 f0/f1 Fourier transform is integrable.
The source's actual r=20, ζ, γ and Schwartz Fourier convention are
unchanged, and no approximate compactly supported Fourier proxy is
inserted. This is the individual true L1 input to Parity (4.6). -/
theorem parity_original_B590_gate_fourier_norm_integrable434
    (δ : Bool) :
    Integrable (fun ξ : ℝ =>
      ‖(𝓕 (sourceBufferedGate 20 δ) : 𝓢(ℝ,ℂ)) ξ‖) := by
  exact (𝓕 (sourceBufferedGate 20 δ) : 𝓢(ℝ,ℂ)).integrable.norm

/-- A FIXED original r0=20 B590 Fourier L1 mass constant, independent
of the source splitting precision K0, L and requested Type II accuracy.
The constant is defined using the actual two native f0/f1 Schwartz
Fourier transforms and the original real Lebesgue measure. -/
def parityOriginalB590FixedFourierL1Mass434 : ℝ :=
  max 1 (max
    (∫ ξ : ℝ, ‖(𝓕 (sourceBufferedGate 20 false) : 𝓢(ℝ,ℂ)) ξ‖)
    (∫ ξ : ℝ, ‖(𝓕 (sourceBufferedGate 20 true) : 𝓢(ℝ,ℂ)) ξ‖))

/-- Uniform fixed-source Fourier mass for BOTH original B590 gates,
without inserting K0 into any Schwartz regularity constant. -/
theorem parity_original_B590_gate_fourier_norm_le_fixed_mass434
    (δ : Bool) :
    (∫ ξ : ℝ, ‖(𝓕 (sourceBufferedGate 20 δ) : 𝓢(ℝ,ℂ)) ξ‖) ≤
      parityOriginalB590FixedFourierL1Mass434 := by
  unfold parityOriginalB590FixedFourierL1Mass434
  cases δ
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- The true original fixed B590 Fourier L1 constant can always be
chosen at least one, as in manuscript (4.6). -/
theorem parity_original_B590_fixed_fourier_L1_mass_ge_one434 :
    1 ≤ parityOriginalB590FixedFourierL1Mass434 := by
  exact le_max_left _ _
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierTotalVariation -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13500000

/-- Genuine original r0=20 B590 Fourier L1 product variation of one
history-dependent Boolean branch, with its actual f0/f1 choice at
each ordered Q slot. The branch's Fourier integral variation factors
because the individual Schwartz transforms are fixed and integrable.
No fictitious independence of the ORIGINAL physical delta weights is
claimed: this bound is about Fourier integration measure only. -/
def parityOriginalB590FourierBranchVariation434
    {N : ℕ} (δ : Fin N → Bool) : ℝ :=
  ∏ i : Fin N,
    (∫ ξ : ℝ, ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ‖)

/-- For every original Q-slot branch, the product of the ACTUAL
individual B590 Fourier L1 integrals is bounded by the fixed
constant CF^N, independent of the splitting precision K0. -/
theorem parity_original_B590_fourier_branch_variation_le434
    {N : ℕ} (δ : Fin N → Bool) :
    parityOriginalB590FourierBranchVariation434 δ ≤
      parityOriginalB590FixedFourierL1Mass434^N := by
  unfold parityOriginalB590FourierBranchVariation434
  calc
    _ ≤ ∏ _i : Fin N, parityOriginalB590FixedFourierL1Mass434 := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact integral_nonneg (fun ξ => norm_nonneg _)
      · intro i hi
        exact parity_original_B590_gate_fourier_norm_le_fixed_mass434 (δ i)
    _ = _ := by simp

/-- Parity original §4.2 total Fourier variation bound for ALL 2^N
f0/f1 allocation branches:

`sum_delta product_i ‖Fourier f_delta_i‖_L1 ≤ (2CF)^N`.

The actual fixed source Schwartz functions and their true L1 masses
are used, with no K0/frequency-tail dependence. This is precisely the
finite variational part of manuscript (4.6), NOT the polynomial-in-L
estimate or per-frequency truncation error, which remain separate. -/
theorem parity_original_B590_fourier_total_variation_le434 (N : ℕ) :
    (∑ δ : Fin N → Bool, parityOriginalB590FourierBranchVariation434 δ) ≤
      (2*parityOriginalB590FixedFourierL1Mass434)^N := by
  let CF : ℝ := parityOriginalB590FixedFourierL1Mass434
  have hAll :
      (∑ δ : Fin N → Bool, parityOriginalB590FourierBranchVariation434 δ) ≤
        ((Fintype.card (Fin N → Bool):ℝ)*CF^N) := by
    calc
      _ ≤ ∑ _δ : Fin N → Bool, CF^N := by
        apply Finset.sum_le_sum
        intro δ hδ
        exact parity_original_B590_fourier_branch_variation_le434 δ
      _ = _ := by simp
  calc
    _ ≤ ((Fintype.card (Fin N → Bool):ℝ)*CF^N) := hAll
    _ = (2*CF)^N := by
      simp [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, mul_pow]
end Green64Analytic.Parity

end

end

