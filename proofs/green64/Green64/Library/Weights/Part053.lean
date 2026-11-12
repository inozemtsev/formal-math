module

public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Weights.Part051
public import Green64.Library.Weights.Part046
public import Green64.Library.Weights.Part014
public import Green64.Library.Weights.Part052
public import Green64.Library.Correlation.Part040
public import Green64.Library.Correlation.Part038
public import Green64.Library.Weights.Part015
public import Green64.Library.Correlation.Part039
public import Green64.Library.Weights.Part017
public import Green64.Library.Correlation.Part034
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Weights.ActualDyadicResidual

@[expose] public section

/-!
# Weights / Part053

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalTrueOutputCellTwoDyadCover -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- TRUE original source03 product OUTPUT log cell lies in
exactly one of TWO deterministic C6 integer windows,
[M0,2M0) and [2M0,4M0), M0=ceil(exp(jh)).
Strict half-open endpoint convention is preserved. -/
theorem source_original_true_output_cell_two_matched_dyads434
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (j : ℤ) (n : ℕ) (hn : 0 < n)
    (hidx : sourceOriginalLiteralLogCellIndex434 h n=j) :
    let M0 := Nat.ceil (Real.exp ((j:ℝ)*h))
    n ∈ Finset.Ico M0 (2*M0) ∨
    n ∈ Finset.Ico (2*M0) (4*M0) := by
  classical
  let M0 := Nat.ceil (Real.exp ((j:ℝ)*h))
  have hCell : sourceOriginalLiteralLogCell434 h j n :=
    (source_original_literal_log_cell_iff_index434 h hh n j).mpr hidx.symm
  obtain ⟨M,hMpos,hChoice,hScale,hLo,hHi⟩ :=
    source_original_actual_log_cell_two_integer_dyads434
      h hh1 j n hn hCell
  rcases hChoice with h | h
  · left
    rw [h] at hLo hHi
    exact Finset.mem_Ico.mpr ⟨hLo,hHi⟩
  · right
    rw [h] at hLo hHi
    exact Finset.mem_Ico.mpr (by constructor <;> omega)

/-- Product of any truly sampled nonempty/empty prime-label
state in a genuine SOURCE03 prime-atom support is positive.
The result remains true if selected prime groups repeat numeric
prime values at distinct physical slots. -/
theorem source_original_true_atom_output_product_pos434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ)
    (hPrime : ∀ i p, p ∈ S i → p.Prime)
    (n : ℕ)
    (hn : n ∈ sourceOriginalPhysicalProductAtomSupport434 S) :
    0 < n := by
  classical
  change n ∈ (Finset.univ :
    Finset (SourceOriginalGramPrimeTuple434 S)).image
      (sourceOriginalGramPrimeProduct434 S) at hn
  obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hn
  have hp : 0 < sourceOriginalGramPrimeProduct434 S v :=
    source_original_gram_physical_prime_product_pos434 S hPrime v
  simpa only [heq] using hp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFinitePositiveCellFourOutputWindows -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- TRUE original SOURCE03-compatible RAW selected output GLOBAL jA/jB
finite positive-atom sum is exactly FOUR matched output dyad windows.
Arbitrary finite positive output atom supports are retained;
no invented uniform measure or prime independence.
All masks follow from true half-open logarithmic cell geometry.
The coupled complex Fourier/Mellin phase is an ARBITRARY function
of nA*nB; no analytic spectral bound assumed here. -/
theorem source_original_finite_positive_cell_four_output_windows434
    (TA TB : Finset ℕ)
    (hPosA : ∀ n∈TA, 0 < n)
    (hPosB : ∀ n∈TB, 0 < n)
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hhA1 : hA ≤ 1) (hhB1 : hB ≤ 1)
    (jA jB : ℤ) (aCoeff bCoeff : ℕ → ℂ)
    (phase : ℕ → ℂ) :
    let M0 := Nat.ceil (Real.exp ((jA:ℝ)*hA))
    let N0 := Nat.ceil (Real.exp ((jB:ℝ)*hB))
    let aCell : ℕ → ℂ := fun n =>
      if sourceOriginalLiteralLogCellIndex434 hA n=jA
      then aCoeff n else 0
    let bCell : ℕ → ℂ := fun n =>
      if sourceOriginalLiteralLogCellIndex434 hB n=jB
      then bCoeff n else 0
    (∑ n∈TA,∑ mm∈TB, aCell n*bCell mm*phase (n*mm)) =
    (∑ n∈TA,∑ mm∈TB,
      (if n∈Finset.Ico M0 (2*M0) then aCell n else 0) *
      (if mm∈Finset.Ico N0 (2*N0) then bCell mm else 0) *
        phase (n*mm)) +
    (∑ n∈TA,∑ mm∈TB,
      (if n∈Finset.Ico M0 (2*M0) then aCell n else 0) *
      (if mm∈Finset.Ico (2*N0) (4*N0) then bCell mm else 0) *
        phase (n*mm)) +
    (∑ n∈TA,∑ mm∈TB,
      (if n∈Finset.Ico (2*M0) (4*M0) then aCell n else 0) *
      (if mm∈Finset.Ico N0 (2*N0) then bCell mm else 0) *
        phase (n*mm)) +
    (∑ n∈TA,∑ mm∈TB,
      (if n∈Finset.Ico (2*M0) (4*M0) then aCell n else 0) *
      (if mm∈Finset.Ico (2*N0) (4*N0) then bCell mm else 0) *
        phase (n*mm)) := by
  classical
  let M0 := Nat.ceil (Real.exp ((jA:ℝ)*hA))
  let N0 := Nat.ceil (Real.exp ((jB:ℝ)*hB))
  let aCell : ℕ → ℂ := fun n =>
    if sourceOriginalLiteralLogCellIndex434 hA n=jA
    then aCoeff n else 0
  let bCell : ℕ → ℂ := fun n =>
    if sourceOriginalLiteralLogCellIndex434 hB n=jB
    then bCoeff n else 0
  have hAcover (n : ℕ) (hn : n∈TA) (hNonzero : aCell n ≠ 0) :
      n∈Finset.Ico M0 (2*M0) ∨
      n∈Finset.Ico (2*M0) (4*M0) := by
    have hIdx : sourceOriginalLiteralLogCellIndex434 hA n=jA := by
      by_contra hOff
      exact hNonzero (by simp [aCell,hOff])
    have hp := hPosA n hn
    exact source_original_true_output_cell_two_matched_dyads434
      hA hhA hhA1 jA n hp hIdx
  have hBcover (n : ℕ) (hn : n∈TB) (hNonzero : bCell n ≠ 0) :
      n∈Finset.Ico N0 (2*N0) ∨
      n∈Finset.Ico (2*N0) (4*N0) := by
    have hIdx : sourceOriginalLiteralLogCellIndex434 hB n=jB := by
      by_contra hOff
      exact hNonzero (by simp [bCell,hOff])
    have hp := hPosB n hn
    exact source_original_true_output_cell_two_matched_dyads434
      hB hhB hhB1 jB n hp hIdx
  have hAdisjoint (n : ℕ) (hn : n∈TA) :
      ¬(n∈Finset.Ico M0 (2*M0) ∧
        n∈Finset.Ico (2*M0) (4*M0)) := by
    rintro ⟨h0,h1⟩
    have h0' := (Finset.mem_Ico.mp h0).2
    have h1' := (Finset.mem_Ico.mp h1).1
    omega
  have hBdisjoint (n : ℕ) (hn : n∈TB) :
      ¬(n∈Finset.Ico N0 (2*N0) ∧
        n∈Finset.Ico (2*N0) (4*N0)) := by
    rintro ⟨h0,h1⟩
    have h0' := (Finset.mem_Ico.mp h0).2
    have h1' := (Finset.mem_Ico.mp h1).1
    omega
  have hExpansion :=
    source_original_finite_four_output_window_expansion434
      TA TB aCell bCell (fun n mm => phase (n*mm))
      (fun n => n∈Finset.Ico M0 (2*M0))
      (fun n => n∈Finset.Ico (2*M0) (4*M0))
      (fun n => n∈Finset.Ico N0 (2*N0))
      (fun n => n∈Finset.Ico (2*N0) (4*N0))
      hAcover hBcover hAdisjoint hBdisjoint
  simpa only [M0, N0, aCell, bCell] using hExpansion
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueOwnGlobalRetainedGates -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Original SOURCE03 retained C192 source-B/target-A gates
hold for ANY full physical prime-mark state whose actual
GLOBAL indices match a selected ACTIVE cell pair.
The TRUE source and target prime products are automatically
positive, and their exponential upper cutoffs come from
their own original log-cell widths rather than log(2) dyads.
No additional bound on the full-state endpoint tests. -/
theorem source_original_true_own_global_retained_gates434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (hPrime : ∀ g, ∀ p ∈ P g, p.Prime)
    (V : G → ℝ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (jB jA : ℤ)
    (hjB : jB ∈ sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
    (hjA : jA ∈ sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
    (s v : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν))
    (hs : sourceOriginalLiteralLogCellIndex434 hB
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val)) = jB)
    (hv : sourceOriginalLiteralLogCellIndex434 hA
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val)) = jA) :
    let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (fun g i => (s g i).val)
    let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (fun g i => (v g i).val)
    (∃ j ∈ sourceOriginalProbeActiveCellsB434 m P V ν hB xi,
      sourceOriginalLiteralLogCell434 hB j XB) ∧
    (XB:ℝ) ≤ 2*Real.exp (((jB:ℝ)+1)*hB) ∧
    (∃ j ∈ sourceOriginalProbeActiveCellsA434 m P V ν hA xi,
      sourceOriginalLiteralLogCell434 hA j XA) ∧
    (XA:ℝ) ≤ 2*Real.exp (((jA:ℝ)+1)*hA) := by
  classical
  let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
    (fun g i => (s g i).val)
  let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
    (fun g i => (v g i).val)
  have hBp : 0 < XB := by
    unfold XB sourceOriginalProbeFreeSourceX434
    apply Finset.prod_pos
    intro z hz
    exact (hPrime z.val.1
      (s z.val.1 (sourceOriginalProbeFreeIndex434 J ell m
        hmJ ν z.val.1 z.val.2 (Or.inr z.property))).val
      (s z.val.1 (sourceOriginalProbeFreeIndex434 J ell m
        hmJ ν z.val.1 z.val.2 (Or.inr z.property))).property).pos
  have hAp : 0 < XA := by
    unfold XA sourceOriginalProbeFreeTargetX434
    apply Finset.prod_pos
    intro z hz
    exact (hPrime z.val.1
      (v z.val.1 (sourceOriginalProbeFreeIndex434 J ell m
        hmJ ν z.val.1 z.val.2 (Or.inl z.property))).val
      (v z.val.1 (sourceOriginalProbeFreeIndex434 J ell m
        hmJ ν z.val.1 z.val.2 (Or.inl z.property))).property).pos
  have hCB : sourceOriginalLiteralLogCell434 hB jB XB :=
    (source_original_literal_log_cell_iff_index434
      hB hhB XB jB).mpr hs.symm
  have hCA : sourceOriginalLiteralLogCell434 hA jA XA :=
    (source_original_literal_log_cell_iff_index434
      hA hhA XA jA).mpr hv.symm
  have hUB : (XB:ℝ) ≤
      2*Real.exp (((jB:ℝ)+1)*hB) := by
    have hh := source_original_true_global_cell_index_upper434
      hB hhB jB XB hBp hs
    have he := Real.exp_pos (((jB:ℝ)+1)*hB)
    linarith
  have hUA : (XA:ℝ) ≤
      2*Real.exp (((jA:ℝ)+1)*hA) := by
    have hh := source_original_true_global_cell_index_upper434
      hA hhA jA XA hAp hv
    have he := Real.exp_pos (((jA:ℝ)+1)*hA)
    linarith
  exact ⟨⟨jB,hjB,hCB⟩,hUB,⟨jA,hjA,hCA⟩,hUA⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueOwnIndividualRetainedGates -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- In the true SOURCE03 source-B free-mark law, belonging to
the specific ACTIVE original GLOBAL cell jB implies the C192
retained source gate at its OWN exponential upper cutoff.
No target-state nonemptiness or artificial product measure. -/
theorem source_original_true_own_retained_source_gate434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hPrime : ∀ z : ν.2, ∀ p ∈ P z.val.1, p.Prime)
    (hB xi : ℝ) (hhB : 0 < hB)
    (jB : ℤ)
    (hjB : jB ∈ sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
    (Vscale : ℝ)
    (hScale : Vscale = Real.exp (((jB:ℝ)+1)*hB))
    (s : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν))
    (hs : sourceOriginalLiteralLogCellIndex434 hB
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val)) = jB) :
    (∃ j ∈ sourceOriginalProbeActiveCellsB434 m P V ν hB xi,
      sourceOriginalLiteralLogCell434 hB j
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val))) ∧
    (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (fun g i => (s g i).val):ℝ) ≤ 2*Vscale := by
  classical
  let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
    (fun g i => (s g i).val)
  have hp : 0 < XB := by
    unfold XB sourceOriginalProbeFreeSourceX434
    apply Finset.prod_pos
    intro z hz
    exact (hPrime z
      (s z.val.1 (sourceOriginalProbeFreeIndex434 J ell m
        hmJ ν z.val.1 z.val.2 (Or.inr z.property))).val
      (s z.val.1 (sourceOriginalProbeFreeIndex434 J ell m
        hmJ ν z.val.1 z.val.2 (Or.inr z.property))).property).pos
  have hCell : sourceOriginalLiteralLogCell434 hB jB XB :=
    (source_original_literal_log_cell_iff_index434
      hB hhB XB jB).mpr hs.symm
  have hBound : (XB:ℝ) ≤ 2*Vscale := by
    rw [hScale]
    have hh := source_original_true_global_cell_index_upper434
      hB hhB jB XB hp hs
    have he := Real.exp_pos (((jB:ℝ)+1)*hB)
    linarith
  exact ⟨⟨jB,hjB,hCell⟩,hBound⟩

/-- The independent true SOURCE03 target-A analogue,
with all target free marks and the exact active GLOBAL cell. -/
theorem source_original_true_own_retained_target_gate434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hPrime : ∀ z : ν.1, ∀ p ∈ P z.val.1, p.Prime)
    (hA xi : ℝ) (hhA : 0 < hA)
    (jA : ℤ)
    (hjA : jA ∈ sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
    (Uscale : ℝ)
    (hScale : Uscale = Real.exp (((jA:ℝ)+1)*hA))
    (v : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν))
    (hv : sourceOriginalLiteralLogCellIndex434 hA
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val)) = jA) :
    (∃ j ∈ sourceOriginalProbeActiveCellsA434 m P V ν hA xi,
      sourceOriginalLiteralLogCell434 hA j
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val))) ∧
    (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (fun g i => (v g i).val):ℝ) ≤ 2*Uscale := by
  classical
  let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
    (fun g i => (v g i).val)
  have hp : 0 < XA := by
    unfold XA sourceOriginalProbeFreeTargetX434
    apply Finset.prod_pos
    intro z hz
    exact (hPrime z
      (v z.val.1 (sourceOriginalProbeFreeIndex434 J ell m
        hmJ ν z.val.1 z.val.2 (Or.inl z.property))).val
      (v z.val.1 (sourceOriginalProbeFreeIndex434 J ell m
        hmJ ν z.val.1 z.val.2 (Or.inl z.property))).property).pos
  have hCell : sourceOriginalLiteralLogCell434 hA jA XA :=
    (source_original_literal_log_cell_iff_index434
      hA hhA XA jA).mpr hv.symm
  have hBound : (XA:ℝ) ≤ 2*Uscale := by
    rw [hScale]
    have hh := source_original_true_global_cell_index_upper434
      hA hhA jA XA hp hv
    have he := Real.exp_pos (((jA:ℝ)+1)*hA)
    linarith
  exact ⟨⟨jA,hjA,hCell⟩,hBound⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueRawFourOutputWindowFubini -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- TRUE original SOURCE03 RAW selected output GLOBAL jA/jB
prime-atom sum is exactly FOUR matched output dyad windows.
The two independently labelled actual prime groups and every
physical atom are retained, with no invented uniform measure.
All masks follow from true half-open logarithmic cell geometry.
The coupled complex Fourier/Mellin phase is an ARBITRARY function
of nA*nB; no analytic spectral bound assumed here. -/
theorem source_original_true_RAW_four_selected_output_windows434
    {ιA ιB : Type}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (SB : ιB → Finset ℕ)
    (hPrimeA : ∀ i p, p∈SA i → p.Prime)
    (hPrimeB : ∀ i p, p∈SB i → p.Prime)
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hhA1 : hA ≤ 1) (hhB1 : hB ≤ 1)
    (jA jB : ℤ) (aCoeff bCoeff : ℕ → ℂ)
    (phase : ℕ → ℂ) :
    let TA := sourceOriginalPhysicalProductAtomSupport434 SA
    let TB := sourceOriginalPhysicalProductAtomSupport434 SB
    let M0 := Nat.ceil (Real.exp ((jA:ℝ)*hA))
    let N0 := Nat.ceil (Real.exp ((jB:ℝ)*hB))
    let aCell : ℕ → ℂ := fun n =>
      if sourceOriginalLiteralLogCellIndex434 hA n=jA
      then aCoeff n else 0
    let bCell : ℕ → ℂ := fun n =>
      if sourceOriginalLiteralLogCellIndex434 hB n=jB
      then bCoeff n else 0
    (∑ n∈TA,∑ mm∈TB, aCell n*bCell mm*phase (n*mm)) =
    (∑ n∈TA,∑ mm∈TB,
      (if n∈Finset.Ico M0 (2*M0) then aCell n else 0) *
      (if mm∈Finset.Ico N0 (2*N0) then bCell mm else 0) *
        phase (n*mm)) +
    (∑ n∈TA,∑ mm∈TB,
      (if n∈Finset.Ico M0 (2*M0) then aCell n else 0) *
      (if mm∈Finset.Ico (2*N0) (4*N0) then bCell mm else 0) *
        phase (n*mm)) +
    (∑ n∈TA,∑ mm∈TB,
      (if n∈Finset.Ico (2*M0) (4*M0) then aCell n else 0) *
      (if mm∈Finset.Ico N0 (2*N0) then bCell mm else 0) *
        phase (n*mm)) +
    (∑ n∈TA,∑ mm∈TB,
      (if n∈Finset.Ico (2*M0) (4*M0) then aCell n else 0) *
      (if mm∈Finset.Ico (2*N0) (4*N0) then bCell mm else 0) *
        phase (n*mm)) := by
  classical
  have hPosA (n : ℕ)
      (hn : n ∈ sourceOriginalPhysicalProductAtomSupport434 SA) :
      0 < n :=
    source_original_true_atom_output_product_pos434 SA hPrimeA n hn
  have hPosB (n : ℕ)
      (hn : n ∈ sourceOriginalPhysicalProductAtomSupport434 SB) :
      0 < n :=
    source_original_true_atom_output_product_pos434 SB hPrimeB n hn
  have hExpansion :=
    source_original_finite_positive_cell_four_output_windows434
      (sourceOriginalPhysicalProductAtomSupport434 SA)
      (sourceOriginalPhysicalProductAtomSupport434 SB)
      hPosA hPosB hA hB hhA hhB hhA1 hhB1
      jA jB aCoeff bCoeff phase
  simpa only using hExpansion
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTwoGlobalSlowPhase -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- For a pair of true original GLOBAL character block products
the logarithmic separation is bounded by the SUM hA+hB of
the independent original log-cell widths, with no factor equal
to the number of BIG prime labels. -/
theorem source_original_two_global_log_distance434
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (jA jB : ℤ) (DA XA DB XB : ℕ)
    (hDAp : 0 < DA) (hXAp : 0 < XA)
    (hDBp : 0 < DB) (hXBp : 0 < XB)
    (hDA : sourceOriginalLiteralLogCell434 hA jA DA)
    (hXA : sourceOriginalLiteralLogCell434 hA jA XA)
    (hDB : sourceOriginalLiteralLogCell434 hB jB DB)
    (hXB : sourceOriginalLiteralLogCell434 hB jB XB) :
    |Real.log ((DA*DB:ℕ):ℝ) -
      Real.log ((XA*XB:ℕ):ℝ)| ≤ hA+hB := by
  have hdA : (0:ℝ) < DA := by exact_mod_cast hDAp
  have hxA : (0:ℝ) < XA := by exact_mod_cast hXAp
  have hdB : (0:ℝ) < DB := by exact_mod_cast hDBp
  have hxB : (0:ℝ) < XB := by exact_mod_cast hXBp
  have hLogDA :
      Real.log ((DA*DB:ℕ):ℝ) =
        Real.log (DA:ℝ)+Real.log (DB:ℝ) := by
    rw [Nat.cast_mul]
    exact Real.log_mul hdA.ne' hdB.ne'
  have hLogXA :
      Real.log ((XA*XB:ℕ):ℝ) =
        Real.log (XA:ℝ)+Real.log (XB:ℝ) := by
    rw [Nat.cast_mul]
    exact Real.log_mul hxA.ne' hxB.ne'
  have hCellA :=
    source_original_same_global_log_cell_distance434
      hA hhA jA DA XA hDA hXA
  have hCellB :=
    source_original_same_global_log_cell_distance434
      hB hhB jB DB XB hDB hXB
  calc
    _ = |(Real.log (DA:ℝ)-Real.log (XA:ℝ)) +
         (Real.log (DB:ℝ)-Real.log (XB:ℝ))| := by
           rw [hLogDA,hLogXA]
           ring
    _ ≤ |Real.log (DA:ℝ)-Real.log (XA:ℝ)| +
        |Real.log (DB:ℝ)-Real.log (XB:ℝ)| := abs_add_le _ _
    _ ≤ hA+hB := add_le_add hCellA hCellB
/-- TRUE source03 two-GLOBAL additive/Mellin slow multiplier:
when every source/target product pair occupies the SAME respective
physical logarithmic cell and the combined products are bounded by
R, the total phase discrepancy is <=
(|zeta|+2*pi*|beta|*R)*(hA+hB).
This is the exact geometric major-arc perturbation estimate
that is later summed with the true primitive-frame kernel. -/
theorem source_original_two_global_slow_phase_perturbation434
    (ζ beta hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (jA jB : ℤ) (DA XA DB XB : ℕ) (R : ℝ)
    (hDAp : 0 < DA) (hXAp : 0 < XA)
    (hDBp : 0 < DB) (hXBp : 0 < XB)
    (hDAR : ((DA*DB:ℕ):ℝ) ≤ R)
    (hXAR : ((XA*XB:ℕ):ℝ) ≤ R)
    (hDA : sourceOriginalLiteralLogCell434 hA jA DA)
    (hXA : sourceOriginalLiteralLogCell434 hA jA XA)
    (hDB : sourceOriginalLiteralLogCell434 hB jB DB)
    (hXB : sourceOriginalLiteralLogCell434 hB jB XB) :
    ‖sourceOriginalSlowMellinAdditivePhase434 ζ beta (DA*DB) -
      sourceOriginalSlowMellinAdditivePhase434 ζ beta (XA*XB)‖ ≤
        (|ζ|+2*Real.pi*|beta| * R)*(hA+hB) := by
  let ld : ℝ :=
    Real.log ((DA*DB:ℕ):ℝ)-Real.log ((XA*XB:ℕ):ℝ)
  have hLog : |ld| ≤ hA+hB :=
    source_original_two_global_log_distance434
      hA hB hhA hhB jA jB DA XA DB XB
      hDAp hXAp hDBp hXBp hDA hXA hDB hXB
  have hd : 0 < DA*DB := Nat.mul_pos hDAp hDBp
  have hx : 0 < XA*XB := Nat.mul_pos hXAp hXBp
  have hDist :
      |((DA*DB:ℕ):ℝ)-((XA*XB:ℕ):ℝ)| ≤ R*|ld| :=
    source_original_prime_products_log_to_linear434
      (DA*DB) (XA*XB) R hd hx hDAR hXAR
  have hβ : 0 ≤ 2*Real.pi*|beta| := by positivity
  have hR : 0 ≤ R := by
    have hd0 : (0:ℝ) < (DA*DB:ℕ) := by exact_mod_cast hd
    linarith
  have hCoeff : 0 ≤ |ζ|+2*Real.pi*|beta| * R := by positivity
  calc
    _ ≤ |ζ| * |ld|+
      (2*Real.pi*|beta|)*
        |((DA*DB:ℕ):ℝ)-((XA*XB:ℕ):ℝ)| :=
      source_original_slow_mellin_additive_phase_oscillation434
        ζ beta (DA*DB) (XA*XB)
    _ ≤ |ζ| * |ld|+(2*Real.pi*|beta|)*(R*|ld|) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hDist hβ)
    _ = (|ζ|+2*Real.pi*|beta| * R)*|ld| := by ring
    _ ≤ (|ζ|+2*Real.pi*|beta| * R)*(hA+hB) :=
      mul_le_mul_of_nonneg_left hLog hCoeff
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalTwoGlobalTwistedSlow -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The ORIGINAL two-GLOBAL primitive character kernels on
true independently labelled harmonic prime tuples have
a quantitatively SMALL change when the irrational/Mellin
slow phase is moved from auxiliary D_A*D_B to target X_A*X_B.
A major arc with beta and zeta remains a COMPLETELY COUPLED
function of both BIG prime products: no separability shortcut.
The actual retained log cells imply log-distance ≤ hA+hB.
Crucially, the total harmonic L¹ kernel cost is only
|primitive family|², WITHOUT xi^-1, by C165–C168.
The explicit dyadic product cap R is the sole geometric
condition to be checked at original source03 local scales. -/
theorem source_original_actual_two_global_rational_twisted_slow434
    {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (hmuA : ∀ i p, p ∈ SA i → 0 ≤ muA i p)
    (hPrimeA : ∀ i p, p ∈ SA i → p.Prime)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hmuB : ∀ i p, p ∈ SB i → 0 ≤ muB i p)
    (hPrimeB : ∀ i p, p ∈ SB i → p.Prime)
    (Q : ℕ) (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (jA jB : ℤ) (xi : ℝ) (hxi : 0 < xi)
    (hMassA : xi ≤ sourceOriginalRealGramCellMass434 SA muA hA jA)
    (hMassB : xi ≤ sourceOriginalRealGramCellMass434 SB muB hB jB)
    (pA : SourceOriginalGramPrimeTuple434 SA)
    (pB : SourceOriginalGramPrimeTuple434 SB)
    (hCellA : sourceOriginalLiteralLogCell434 hA jA
      (sourceOriginalGramPrimeProduct434 SA pA))
    (hCellB : sourceOriginalLiteralLogCell434 hB jB
      (sourceOriginalGramPrimeProduct434 SB pB))
    (R : ℝ)
    (hUpper :
      ∀ qA : SourceOriginalGramPrimeTuple434 SA,
        ∀ qB : SourceOriginalGramPrimeTuple434 SB,
          sourceOriginalLiteralLogCell434 hA jA
            (sourceOriginalGramPrimeProduct434 SA qA) →
          sourceOriginalLiteralLogCell434 hB jB
            (sourceOriginalGramPrimeProduct434 SB qB) →
          (((sourceOriginalGramPrimeProduct434 SA qA *
             sourceOriginalGramPrimeProduct434 SB qB):ℕ):ℝ) ≤ R)
    (r : ℕ) (hr : 0 < r) (u : ℤ)
    (ζ beta : ℝ) :
    let slow := sourceOriginalSlowMellinAdditivePhase434 ζ beta
    let WA := sourceOriginalGramPrimeMass434 SA muA
    let WB := sourceOriginalGramPrimeMass434 SB muB
    let KA := sourceOriginalActualPrimitiveGlobalKernel434
      Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
    let KB := sourceOriginalActualPrimitiveGlobalKernel434
      Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
    let DA := sourceOriginalGramPrimeProduct434 SA
    let DB := sourceOriginalGramPrimeProduct434 SB
    let omega := (|ζ|+2*Real.pi*|beta| * R)*(hA+hB)
    ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                 SourceOriginalGramPrimeTuple434 SB,
      (((WA q.1*WB q.2:ℝ):ℂ)*
        (KA (DA q.1) (DA pA)*KB (DB q.2) (DB pB)))*
        (sourceOriginalPositiveRationalPhaseAtNat434 r hr u
          (DA q.1*DB q.2) *
          (slow (DA q.1*DB q.2)-slow (DA pA*DB pB))))‖ ≤
      ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2)*
        omega := by
  classical
  let XA := SourceOriginalGramPrimeTuple434 SA
  let XB := SourceOriginalGramPrimeTuple434 SB
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let wA : XA → ℝ := sourceOriginalGramPrimeMass434 SA muA
  let wB : XB → ℝ := sourceOriginalGramPrimeMass434 SB muB
  let DA : XA → ℕ := sourceOriginalGramPrimeProduct434 SA
  let DB : XB → ℕ := sourceOriginalGramPrimeProduct434 SB
  let KA : XA → XA → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
      (DA q) (DA p)
  let KB : XB → XB → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
      (DB q) (DB p)
  let gateA : XA → Prop := fun q =>
    sourceOriginalLiteralLogCell434 hA jA (DA q)
  let gateB : XB → Prop := fun q =>
    sourceOriginalLiteralLogCell434 hB jB (DB q)
  let phi : XA × XB → ℂ := fun q =>
    sourceOriginalSlowMellinAdditivePhase434 ζ beta (DA q.1*DB q.2)
  let H : XA × XB → ℂ := fun q =>
    sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      (DA q.1*DB q.2)
  let omega : ℝ := (|ζ|+2*Real.pi*|beta| * R)*(hA+hB)
  have hwA (q : XA) : 0 ≤ wA q :=
    source_original_physical_gram_prime_mass_nonneg434 SA muA hmuA q
  have hwB (q : XB) : 0 ≤ wB q :=
    source_original_physical_gram_prime_mass_nonneg434 SB muB hmuB q
  have hPosA (q : XA) : 0 < DA q := by
    dsimp [DA,sourceOriginalGramPrimeProduct434]
    apply Finset.prod_pos
    intro i hi
    exact (hPrimeA i (q i).val (q i).property).pos
  have hPosB (q : XB) : 0 < DB q := by
    dsimp [DB,sourceOriginalGramPrimeProduct434]
    apply Finset.prod_pos
    intro i hi
    exact (hPrimeB i (q i).val (q i).property).pos
  have hRpos : 0 ≤ R := by
    have hp : 0 < DA pA*DB pB :=
      Nat.mul_pos (hPosA pA) (hPosB pB)
    have hu := hUpper pA pB hCellA hCellB
    have hNat : (0:ℝ) < ((DA pA*DB pB:ℕ):ℝ) := by
      exact_mod_cast hp
    linarith
  have hCoeff : 0 ≤ |ζ|+2*Real.pi*|beta| * R := by
    positivity
  have hOmega : 0 ≤ omega :=
    mul_nonneg hCoeff (by linarith)
  have hKAsupport (q : XA) (hq : ¬gateA q) :
      KA q pA = 0 := by
    have hEntry := source_original_physical_primitive_cell_frame_kernel434
      SA muA hA jA Q q pA
    dsimp [KA,DA,gateA] at hq ⊢
    rw [hEntry]
    simp [hq]
  have hKBsupport (q : XB) (hq : ¬gateB q) :
      KB q pB = 0 := by
    have hEntry := source_original_physical_primitive_cell_frame_kernel434
      SB muB hB jB Q q pB
    dsimp [KB,DB,gateB] at hq ⊢
    rw [hEntry]
    simp [hq]
  have hSlow (qA : XA) (qB : XB)
      (hqa : gateA qA) (hqb : gateB qB) :
      ‖phi (qA,qB)-phi (pA,pB)‖ ≤ omega := by
    exact source_original_two_global_slow_phase_perturbation434
      ζ beta hA hB hhA hhB jA jB
      (DA qA) (DA pA) (DB qB) (DB pB) R
      (hPosA qA) (hPosA pA) (hPosB qB) (hPosB pB)
      (hUpper qA qB hqa hqb)
      (hUpper pA pB hCellA hCellB)
      hqa hCellA hqb hCellB
  have hH (q : XA × XB) : ‖H q‖ ≤ 1 := by
    exact le_of_eq (source_original_positive_rational_phase_norm_one434
      r hr u (DA q.1*DB q.2))
  have hL1 :
    (∑ q : XA × XB,
      (wA q.1*wB q.2)*‖KA q.1 pA*KB q.2 pB‖) ≤
      ((Fintype.card Fam:ℝ)^2) := by
    simpa only [XA,XB,Fam,wA,wB,KA,KB,DA,DB] using
      (source_original_actual_two_global_primitive_L1_434
        SA muA hmuA SB muB hmuB Q hA hB jA jB
        xi hxi hMassA hMassB pA pB hCellA hCellB)
  have hMain :=
    source_original_finite_twisted_two_global_slow_kernel434
      wA wB hwA hwB KA KB gateA gateB pA pB
      hKAsupport hKBsupport phi H omega
      ((Fintype.card Fam:ℝ)^2) hOmega hH hSlow hL1
  change
    ‖(∑ q : XA × XB,
      (((wA q.1*wB q.2:ℝ):ℂ)*
        (KA q.1 pA*KB q.2 pB))*
        (H q*(phi q-phi (pA,pB))))‖ ≤
      ((Fintype.card Fam:ℝ)^2)*omega
  exact hMain
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalFullMajorSlowComparison -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 30000000

/-- Full ACTUAL original two-GLOBAL major-arc phase comparison:
the independent physical primitive character frames reproduce
exp(2*pi*i*(u/r+beta)*D_A*D_B) * (D_A*D_B)^(i*zeta)
to error rational_SW_error + |primitive_family|^2 * slow_oscillation.
All small-rational Fourier, the TRUE character cell law, and
the rational-twisted Mellin perturbation are kernel-checked.
No division by the retained cell probability in the slow-phase
error; arbitrary real zeta,beta are allowed under a genuine
matched-cell product-scale cap R. This is the true MAJOR-ARC
block, not yet minor arcs or the full source03 signed residual. -/
theorem source_original_two_global_full_major_phase_comparison_unconditional434
    (Cq Cxi : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
      (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
      (hmuA : ∀ k, ∑ p ∈ SA k, muA k p = 1)
      (hmuPosA : ∀ k p, p ∈ SA k → 0 ≤ muA k p)
      (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
      (hmuB : ∀ k, ∑ p ∈ SB k, muB k p = 1)
      (hmuPosB : ∀ k p, p ∈ SB k → 0 ≤ muB k p)
      (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
      (jA jB : ℤ) (Q : ℕ)
      (iA : ιA) (hBIGA : ∀ k p, p ∈ SA k → p.Prime ∧ Q^2 < p)
      (iB : ιB) (hBIGB : ∀ k p, p ∈ SB k → p.Prime ∧ Q^2 < p)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (VA VB : ℝ) (hVA : Vmin ≤ VA) (hVB : Vmin ≤ VB)
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (hWeightA : ∀ p, muA iA p = (1/(p:ℝ))/VA)
      (hWeightB : ∀ p, muB iB p = (1/(p:ℝ))/VB)
      (xi : ℝ) (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi)
      (hMassA : xi ≤ sourceOriginalRealGramCellMass434 SA muA hA jA)
      (hMassB : xi ≤ sourceOriginalRealGramCellMass434 SB muB hB jB)
      (pA : SourceOriginalGramPrimeTuple434 SA)
      (pB : SourceOriginalGramPrimeTuple434 SB)
      (hCellA : sourceOriginalLiteralLogCell434 hA jA
         (sourceOriginalGramPrimeProduct434 SA pA))
      (hCellB : sourceOriginalLiteralLogCell434 hB jB
         (sourceOriginalGramPrimeProduct434 SB pB))

      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ)
      (R : ℝ)
      (hUpper :
        ∀ qA : SourceOriginalGramPrimeTuple434 SA,
          ∀ qB : SourceOriginalGramPrimeTuple434 SB,
            sourceOriginalLiteralLogCell434 hA jA
              (sourceOriginalGramPrimeProduct434 SA qA) →
            sourceOriginalLiteralLogCell434 hB jB
              (sourceOriginalGramPrimeProduct434 SB qB) →
            (((sourceOriginalGramPrimeProduct434 SA qA *
               sourceOriginalGramPrimeProduct434 SB qB):ℕ):ℝ) ≤ R)
      (ζ beta : ℝ),
      let δ : ℝ := (K/Vmin)*L^(-B)
      let eps : ℝ := (δ+δ+δ*δ)*(r:ℝ)
      let omega : ℝ := (|ζ|+2*Real.pi*|beta| * R)*(hA+hB)
      let DA := sourceOriginalGramPrimeProduct434 SA
      let DB := sourceOriginalGramPrimeProduct434 SB
      let WA := sourceOriginalGramPrimeMass434 SA muA
      let WB := sourceOriginalGramPrimeMass434 SB muB
      let KA := sourceOriginalActualPrimitiveGlobalKernel434
         Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
      let KB := sourceOriginalActualPrimitiveGlobalKernel434
         Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
      let rat := sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      let slow := sourceOriginalSlowMellinAdditivePhase434 ζ beta
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                   SourceOriginalGramPrimeTuple434 SB,
         (((WA q.1*WB q.2:ℝ):ℂ) *
            (KA (DA q.1) (DA pA) *
             KB (DB q.2) (DB pB))) *
         (rat (DA q.1*DB q.2) * slow (DA q.1*DB q.2))) -
          rat (DA pA*DB pB)*slow (DA pA*DB pB)‖ ≤
        eps +
        ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2)*
          omega := by
  obtain ⟨K,Y,hK,hRatSource⟩ :=
    source_original_two_global_rational_phase_comparison_unconditional434
      Cq Cxi gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro ιA ιB instFA instDA instFB instDB
    SA muA hmuA hmuPosA SB muB hmuB hmuPosB
    hA hB hhA hhB jA jB Q iA hBIGA iB hBIGB
    L hL hLdyad hQ uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB
    Vmin hVmin VA VB hVA hVB hBandA hBandB
    hWeightA hWeightB xi hxi hXi hMassA hMassB
    pA pB hCellA hCellB r hr hrQ u
    R hUpper ζ beta
  dsimp
  let XA := SourceOriginalGramPrimeTuple434 SA
  let XB := SourceOriginalGramPrimeTuple434 SB
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let wA : XA → ℝ := sourceOriginalGramPrimeMass434 SA muA
  let wB : XB → ℝ := sourceOriginalGramPrimeMass434 SB muB
  let DA : XA → ℕ := sourceOriginalGramPrimeProduct434 SA
  let DB : XB → ℕ := sourceOriginalGramPrimeProduct434 SB
  let KA : XA → XA → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
      (DA q) (DA p)
  let KB : XB → XB → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
      (DB q) (DB p)
  let F : XA × XB → ℂ := fun q =>
    ((wA q.1*wB q.2:ℝ):ℂ)*
      (KA q.1 pA*KB q.2 pB)
  let rat : XA × XB → ℂ := fun q =>
    sourceOriginalPositiveRationalPhaseAtNat434
      r hr u (DA q.1*DB q.2)
  let slow : XA × XB → ℂ := fun q =>
    sourceOriginalSlowMellinAdditivePhase434
      ζ beta (DA q.1*DB q.2)
  let δ : ℝ := (K/Vmin)*L^(-B)
  let eps : ℝ := (δ+δ+δ*δ)*(r:ℝ)
  let omega : ℝ := (|ζ|+2*Real.pi*|beta| * R)*(hA+hB)
  have hRatRaw := hRatSource
    SA muA hmuA hmuPosA SB muB hmuB hmuPosB
    hA hB jA jB Q iA hBIGA iB hBIGB
    L hL hLdyad hQ uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB
    Vmin hVmin VA VB hVA hVB hBandA hBandB
    hWeightA hWeightB xi hxi hXi hMassA hMassB
    pA pB hCellA hCellB r hr hrQ u
  have hRat :
      ‖(∑ q : XA × XB, F q*rat q)-rat (pA,pB)‖ ≤ eps := by
    dsimp only at hRatRaw
    simpa only [F,rat,wA,wB,KA,KB,DA,DB,eps,δ,
      Complex.ofReal_mul,mul_assoc] using hRatRaw
  have hTwistRaw :=
    source_original_actual_two_global_rational_twisted_slow434
      SA muA hmuPosA (fun i p hp => (hBIGA i p hp).1)
      SB muB hmuPosB (fun i p hp => (hBIGB i p hp).1)
      Q hA hB hhA hhB jA jB
      xi hxi hMassA hMassB pA pB hCellA hCellB
      R hUpper r hr u ζ beta
  have hTwist :
      ‖(∑ q : XA × XB,
        F q*rat q*(slow q-slow (pA,pB)))‖ ≤
        ((Fintype.card Fam:ℝ)^2)*omega := by
    dsimp only at hTwistRaw
    simpa only [F,rat,slow,wA,wB,KA,KB,DA,DB,omega,Fam,
      Complex.ofReal_mul,mul_assoc] using hTwistRaw
  have hUnit : ‖slow (pA,pB)‖ = 1 := by
    have h : ‖Complex.exp (Complex.I *
      (((ζ * Real.log (((DA pA*DB pB:ℕ):ℝ))+
        2*Real.pi*beta*(((DA pA*DB pB:ℕ):ℝ))):ℝ):ℂ))‖ = 1 :=
        Complex.norm_exp_I_mul_ofReal _
    push_cast at h
    simpa only [slow,sourceOriginalSlowMellinAdditivePhase434,
      Nat.cast_mul,Complex.ofReal_mul, Complex.ofReal_natCast] using h
  have hMain :=
    source_original_finite_rational_slow_combine434
      F rat slow (pA,pB)
      eps ((Fintype.card Fam:ℝ)^2*omega)
      hUnit hRat hTwist
  change ‖(∑ q : XA × XB,
      F q*(rat q*slow q))-
        rat (pA,pB)*slow (pA,pB)‖ ≤
        eps+((Fintype.card Fam:ℝ)^2)*omega
  simpa only [mul_assoc] using hMain
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalFullMajorCellCap -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The ACTUAL independent-prime two GLOBAL character frames
reproduce the full rational, irrational-beta and Mellin phase
unconditionally, where the needed common source-product scale
R is DERIVED from the literal half-open product-log cells.
No separate upper-product hypothesis hUpper is retained.
All other genuine BIG band/harmonic normalizer and retention
hypotheses remain explicit: this is NOT a minor-arc estimate. -/
theorem source_original_two_global_full_major_phase_cell_cap_unconditional434
    (Cq Cxi : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
      (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
      (hmuA : ∀ k, ∑ p ∈ SA k, muA k p = 1)
      (hmuPosA : ∀ k p, p ∈ SA k → 0 ≤ muA k p)
      (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
      (hmuB : ∀ k, ∑ p ∈ SB k, muB k p = 1)
      (hmuPosB : ∀ k p, p ∈ SB k → 0 ≤ muB k p)
      (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
      (jA jB : ℤ) (Q : ℕ)
      (iA : ιA) (hBIGA : ∀ k p, p ∈ SA k → p.Prime ∧ Q^2 < p)
      (iB : ιB) (hBIGB : ∀ k p, p ∈ SB k → p.Prime ∧ Q^2 < p)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (VA VB : ℝ) (hVA : Vmin ≤ VA) (hVB : Vmin ≤ VB)
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (hWeightA : ∀ p, muA iA p = (1/(p:ℝ))/VA)
      (hWeightB : ∀ p, muB iB p = (1/(p:ℝ))/VB)
      (xi : ℝ) (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi)
      (hMassA : xi ≤ sourceOriginalRealGramCellMass434 SA muA hA jA)
      (hMassB : xi ≤ sourceOriginalRealGramCellMass434 SB muB hB jB)
      (pA : SourceOriginalGramPrimeTuple434 SA)
      (pB : SourceOriginalGramPrimeTuple434 SB)
      (hCellA : sourceOriginalLiteralLogCell434 hA jA
         (sourceOriginalGramPrimeProduct434 SA pA))
      (hCellB : sourceOriginalLiteralLogCell434 hB jB
         (sourceOriginalGramPrimeProduct434 SB pB))

      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ)
      (ζ beta : ℝ),
      let R : ℝ := Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB)
      let δ : ℝ := (K/Vmin)*L^(-B)
      let eps : ℝ := (δ+δ+δ*δ)*(r:ℝ)
      let omega : ℝ := (|ζ|+2*Real.pi*|beta| * R)*(hA+hB)
      let DA := sourceOriginalGramPrimeProduct434 SA
      let DB := sourceOriginalGramPrimeProduct434 SB
      let WA := sourceOriginalGramPrimeMass434 SA muA
      let WB := sourceOriginalGramPrimeMass434 SB muB
      let KA := sourceOriginalActualPrimitiveGlobalKernel434
         Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
      let KB := sourceOriginalActualPrimitiveGlobalKernel434
         Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
      let rat := sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      let slow := sourceOriginalSlowMellinAdditivePhase434 ζ beta
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                   SourceOriginalGramPrimeTuple434 SB,
         (((WA q.1*WB q.2:ℝ):ℂ) *
            (KA (DA q.1) (DA pA) *
             KB (DB q.2) (DB pB))) *
         (rat (DA q.1*DB q.2) * slow (DA q.1*DB q.2))) -
          rat (DA pA*DB pB)*slow (DA pA*DB pB)‖ ≤
        eps +
        ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2)*
          omega := by
  obtain ⟨K,Y,hK,hMain⟩ :=
    source_original_two_global_full_major_phase_comparison_unconditional434
      Cq Cxi gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro ιA ιB instFA instDA instFB instDB
    SA muA hmuA hmuPosA SB muB hmuB hmuPosB
    hA hB hhA hhB jA jB Q iA hBIGA iB hBIGB
    L hL hLdyad hQ uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB
    Vmin hVmin VA VB hVA hVB hBandA hBandB
    hWeightA hWeightB xi hxi hXi hMassA hMassB
    pA pB hCellA hCellB r hr hrQ u ζ beta
  let R : ℝ := Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB)
  have hUpper :
      ∀ qA : SourceOriginalGramPrimeTuple434 SA,
        ∀ qB : SourceOriginalGramPrimeTuple434 SB,
          sourceOriginalLiteralLogCell434 hA jA
            (sourceOriginalGramPrimeProduct434 SA qA) →
          sourceOriginalLiteralLogCell434 hB jB
            (sourceOriginalGramPrimeProduct434 SB qB) →
          (((sourceOriginalGramPrimeProduct434 SA qA *
             sourceOriginalGramPrimeProduct434 SB qB):ℕ):ℝ) ≤ R := by
    intro qA qB hca hcb
    exact source_original_physical_two_global_cell_product_cap434
      SA SB
      (fun i p hp => (hBIGA i p hp).1)
      (fun i p hp => (hBIGB i p hp).1)
      hA hB jA jB qA qB hca hcb
  have hResult := hMain
    SA muA hmuA hmuPosA SB muB hmuB hmuPosB
    hA hB hhA hhB jA jB Q iA hBIGA iB hBIGB
    L hL hLdyad hQ uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB
    Vmin hVmin VA VB hVA hVB hBandA hBandB
    hWeightA hWeightB xi hxi hXi hMassA hMassB
    pA pB hCellA hCellB r hr hrQ u R hUpper ζ beta
  exact hResult
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeFullMajorPhaseInstantiation -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- C168: SOURCE03 ORIGINAL nu-pattern full major-arc comparison
on the two TRUE independently-labelled harmonic prime-product
spaces, with both the rational additive phase and the small
real beta / Mellin ζ correction.
No external hUpper R assumption: R_jA,jB is DERIVED from the
literal GLOBAL cells in C165-167. Original group-by-group
prime-law normalization, retained-cell masses and BIG conductor
conditions are instantiated from existing kernel-checked results.
This is not yet signed raw-vs-comparison or any minor-arc theorem. -/
theorem source_original_probe_full_major_phase_instantiated434
    (Cq Cxi : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [DecidableEq G]
      (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ) (V : G → ℝ)
      (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
      (hVp : ∀ g, 0 < V g)
      (Q : ℕ)
      (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
           p.Prime ∧ Q^2 < p)
      (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
           p.Prime ∧ Q^2 < p)
      (hA hB xi : ℝ)
      (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
      (jA jB : ℤ)
      (hjA : jA ∈ sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (hjB : jB ∈ sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (hXi : xi⁻¹ ≤ L^Cxi)
      (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (hAllVmin : ∀ g, Vmin ≤ V g)
      (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
      (pA : SourceOriginalGramPrimeTuple434
          (fun z : ν.1 => P z.val.1))
      (pB : SourceOriginalGramPrimeTuple434
          (fun z : ν.2 => P z.val.1))
      (hCellA : sourceOriginalLiteralLogCell434 hA jA
          (sourceOriginalGramPrimeProduct434
            (fun z : ν.1 => P z.val.1) pA))
      (hCellB : sourceOriginalLiteralLogCell434 hB jB
          (sourceOriginalGramPrimeProduct434
            (fun z : ν.2 => P z.val.1) pB))
      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ)
      (ζ beta : ℝ),
      let SA : ν.1 → Finset ℕ := fun z => P z.val.1
      let SB : ν.2 → Finset ℕ := fun z => P z.val.1
      let muA : ν.1 → ℕ → ℝ := fun z =>
        sourcePrimeSharedAtom434 (V z.val.1)
      let muB : ν.2 → ℕ → ℝ := fun z =>
        sourcePrimeSharedAtom434 (V z.val.1)
      let eps : ℝ := (K/Vmin)*L^(-B)
      let R : ℝ := Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB)
      let omega : ℝ := (|ζ|+2*Real.pi*|beta| * R)*(hA+hB)
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                     SourceOriginalGramPrimeTuple434 SB,
        (((sourceOriginalGramPrimeMass434 SA muA q.1 *
            sourceOriginalGramPrimeMass434 SB muB q.2:ℝ):ℂ) *
        (sourceOriginalActualPrimitiveGlobalKernel434
           Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
           (sourceOriginalGramPrimeProduct434 SA q.1)
           (sourceOriginalGramPrimeProduct434 SA pA) *
         sourceOriginalActualPrimitiveGlobalKernel434
           Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
           (sourceOriginalGramPrimeProduct434 SB q.2)
           (sourceOriginalGramPrimeProduct434 SB pB)) *
        (sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalGramPrimeProduct434 SA q.1 *
            sourceOriginalGramPrimeProduct434 SB q.2) *
         sourceOriginalSlowMellinAdditivePhase434 ζ beta
           (sourceOriginalGramPrimeProduct434 SA q.1 *
            sourceOriginalGramPrimeProduct434 SB q.2)))) -
        (sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalGramPrimeProduct434 SA pA *
            sourceOriginalGramPrimeProduct434 SB pB) *
         sourceOriginalSlowMellinAdditivePhase434 ζ beta
           (sourceOriginalGramPrimeProduct434 SA pA *
            sourceOriginalGramPrimeProduct434 SB pB))‖ ≤
        (eps+eps+eps*eps)*(r:ℝ) +
          ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2)*omega := by
  obtain ⟨K,Y,hK,hEstimate⟩ :=
    source_original_two_global_full_major_phase_cell_cap_unconditional434
      Cq Cxi gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro G instDec m ν P V hV hVp Q hBIGA hBIGB
    hA hB xi hhA hhB hxi jA jB hjA hjB
    L hL hLdyad hQ hXi iA iB uA vA uB vB
    huA huB huvA huvB hvA hvB huLargeA huLargeB
    huBIGA huBIGB hYA hYB Vmin hVmin hAllVmin
    hBandA hBandB pA pB hCellA hCellB r hr hrQ u ζ beta
  dsimp
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let VA := V iA.val.1
  let VB := V iB.val.1
  obtain ⟨hmuA,hmuPosA,hprimeA,hWeightA⟩ :=
    source_original_probe_actual_coordinate_law434
      SA (fun z : ν.1 => V z.val.1)
      (fun z => hV z.val.1) (fun z => hVp z.val.1)
      Q hBIGA
  obtain ⟨hmuB,hmuPosB,hprimeB,hWeightB⟩ :=
    source_original_probe_actual_coordinate_law434
      SB (fun z : ν.2 => V z.val.1)
      (fun z => hV z.val.1) (fun z => hVp z.val.1)
      Q hBIGB
  have hmA : xi ≤ sourceOriginalRealGramCellMass434
      SA muA hA jA :=
    source_original_probe_A_retained_gram_mass434
      m ν P V hA xi hhA hxi jA hjA
  have hmB : xi ≤ sourceOriginalRealGramCellMass434
      SB muB hB jB :=
    source_original_probe_B_retained_gram_mass434
      m ν P V hB xi hhB hxi jB hjB
  have hVA : Vmin ≤ VA := hAllVmin iA.val.1
  have hVB : Vmin ≤ VB := hAllVmin iB.val.1
  have hFirst := hEstimate
    SA muA hmuA hmuPosA SB muB hmuB hmuPosB
    hA hB hhA hhB jA jB Q iA hprimeA iB hprimeB
    L hL hLdyad hQ
    uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    Vmin hVmin VA VB hVA hVB hBandA hBandB
    (hWeightA iA) (hWeightB iB)
    xi hxi hXi hmA hmB pA pB hCellA hCellB
    r hr hrQ u ζ beta
  simpa only [SA,SB,muA,muB,VA,VB] using hFirst
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeCanonicalSignedMajorSlow -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The TRUE signed canonical ν-pattern comparison, with ALL
active A/B global cells, obeys the unconditional major-rational
phase bound on the true harmonic labelled prime tuples.
Unlike C120, the SOURCE ORIGINAL pattern sign and full active
Knu are literally present under the auxiliary expectation.
The original prime-interval geometry stays explicit, and this
major-rational statement does not silently assert minor arcs. -/
theorem source_original_probe_full_active_signed_major_slow_unconditional434
    (Cq Cxi : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [DecidableEq G]
      (J ell m : ℕ) (hmJ : m ≤ J)
      (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ) (V : G → ℝ)
      (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (hMass : ∀ g, Vmin ≤ V g)
      (Q : ℕ)
      (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hA hB xi : ℝ)
      (hhA : 0 < hA) (hhB : 0 < hB)
      (hxi : 0 < xi)
      (jA jB : ℤ)
      (hjA : jA ∈ sourceOriginalProbeActiveCellsA434
        m P V ν hA xi)
      (hjB : jB ∈ sourceOriginalProbeActiveCellsB434
        m P V ν hB xi)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (hXi : xi⁻¹ ≤ L^Cxi)
      (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
      (target source : ∀ g,
        Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
      (ht : ∀ g i, target g i ∈ P g)
      (hs : ∀ g i, source g i ∈ P g)
      (hCellA : sourceOriginalLiteralLogCell434 hA jA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target))
      (hCellB : sourceOriginalLiteralLogCell434 hB jB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source))
      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ) (ζ beta : ℝ),
      let SA : ν.1 → Finset ℕ := fun z => P z.val.1
      let SB : ν.2 → Finset ℕ := fun z => P z.val.1
      let muA : ν.1 → ℕ → ℝ :=
        fun z => sourcePrimeSharedAtom434 (V z.val.1)
      let muB : ν.2 → ℕ → ℝ :=
        fun z => sourcePrimeSharedAtom434 (V z.val.1)
      let pA := sourceOriginalProbeTargetAIntoGram434
        J ell m hmJ ν P target ht
      let pB := sourceOriginalProbeSourceBIntoGram434
        J ell m hmJ ν P source hs
      let eps : ℝ := (K/Vmin)*L^(-B)
      let R : ℝ := Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB)
      let omega : ℝ := (|ζ|+2*Real.pi*|beta| * R)*(hA+hB)
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                     SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA muA q.1:ℂ) *
         (sourceOriginalGramPrimeMass434 SB muB q.2:ℂ)) *
        sourceOriginalActualPrimitiveComparisonKernel434 Q
          (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
          (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
          hA hB
          (sourceOriginalProbeCellA434 m P V ν hA)
          (sourceOriginalProbeCellB434 m P V ν hB)
          (sourceOriginalGramPrimeProduct434 SA q.1)
          (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target)
          (sourceOriginalGramPrimeProduct434 SB q.2)
          (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
          (ν.1.card+ν.2.card) *
        (sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalGramPrimeProduct434 SA q.1 *
            sourceOriginalGramPrimeProduct434 SB q.2) *
         sourceOriginalSlowMellinAdditivePhase434 ζ beta
           (sourceOriginalGramPrimeProduct434 SA q.1 *
            sourceOriginalGramPrimeProduct434 SB q.2))) -
        (-((-1:ℂ)^(ν.1.card+ν.2.card))) *
        (sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target *
            sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source) *
         sourceOriginalSlowMellinAdditivePhase434 ζ beta
           (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target *
            sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source))‖ ≤
        (eps+eps+eps*eps)*(r:ℝ) +
          ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2)*omega := by
  obtain ⟨K,Y,hK,hMajor⟩ :=
    source_original_probe_full_major_phase_instantiated434
      Cq Cxi gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro G _ J ell m hmJ ν P V hV Vmin hVmin hMass Q hBIGA hBIGB
    hA hB xi hhA hhB hxi jA jB hjA hjB L hL hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    target source ht hs hCellA hCellB r hr hrQ u ζ beta
  dsimp
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let ε : ℝ := (K/Vmin)*L^(-B)
  let R : ℝ := Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB)
  let ω : ℝ := (|ζ|+2*Real.pi*|beta| * R)*(hA+hB)
  let σ : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
  have hσ : ‖σ‖ = 1 := by simp [σ]
  have hVp (g : G) : 0 < V g := hVmin.trans_le (hMass g)
  let pA := sourceOriginalProbeTargetAIntoGram434
    J ell m hmJ ν P target ht
  let pB := sourceOriginalProbeSourceBIntoGram434
    J ell m hmJ ν P source hs
  have hCellAP : sourceOriginalLiteralLogCell434 hA jA
      (sourceOriginalGramPrimeProduct434 SA pA) := by
    simpa only [pA,SA,
      source_original_probe_target_A_gram_product434] using hCellA
  have hCellBP : sourceOriginalLiteralLogCell434 hB jB
      (sourceOriginalGramPrimeProduct434 SB pB) := by
    simpa only [pB,SB,
      source_original_probe_source_B_gram_product434] using hCellB
  have hMajorInst := hMajor
    m ν P V hV hVp Q hBIGA hBIGB
    hA hB xi hhA hhB hxi jA jB hjA hjB
    L hL hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    Vmin hVmin hMass hBandA hBandB pA pB
    hCellAP hCellBP r hr hrQ u ζ beta
  have hMA : sourceOriginalProbeCellA434 m P V ν hA =
      sourceOriginalRealGramCellMass434 SA muA hA := by
    funext j
    exact source_original_probe_A_cell_probability_gram434 m ν P V hA j
  have hMB : sourceOriginalProbeCellB434 m P V ν hB =
      sourceOriginalRealGramCellMass434 SB muB hB := by
    funext j
    exact source_original_probe_B_cell_probability_gram434 m ν P V hB j
  let weight : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB → ℂ := fun q =>
    ((sourceOriginalGramPrimeMass434 SA muA q.1:ℂ) *
     (sourceOriginalGramPrimeMass434 SB muB q.2:ℂ))
  let kA : SourceOriginalGramPrimeTuple434 SA → ℂ := fun q =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jA} hA (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalGramPrimeProduct434 SA q)
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target)
  let kB : SourceOriginalGramPrimeTuple434 SB → ℂ := fun q =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jB} hB (sourceOriginalProbeCellB434 m P V ν hB)
      (sourceOriginalGramPrimeProduct434 SB q)
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
  let Ksigned : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB → ℂ := fun q =>
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      hA hB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      (sourceOriginalGramPrimeProduct434 SA q.1)
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target)
      (sourceOriginalGramPrimeProduct434 SB q.2)
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
      (ν.1.card+ν.2.card)
  let phase : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB → ℂ := fun q =>
    sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      (sourceOriginalGramPrimeProduct434 SA q.1 *
       sourceOriginalGramPrimeProduct434 SB q.2) *
    sourceOriginalSlowMellinAdditivePhase434 ζ beta
      (sourceOriginalGramPrimeProduct434 SA q.1 *
       sourceOriginalGramPrimeProduct434 SB q.2)
  let phaseX : ℂ :=
    sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target *
       sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source) *
    sourceOriginalSlowMellinAdditivePhase434 ζ beta
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target *
       sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
  have hKernelCollapse (q :
      SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB) :
      Ksigned q = σ * kA q.1 * kB q.2 := by
    have hc := source_original_probe_full_active_signed_singleton434
      J ell m hmJ ν P V Q hA hB xi hhA hhB
      jA jB hjA hjB
      (sourceOriginalGramPrimeProduct434 SA q.1)
      (sourceOriginalGramPrimeProduct434 SB q.2)
      target source hCellA hCellB
    dsimp only [Ksigned]
    rw [hc]
    rfl
  have hFactor :
      (∑ q : SourceOriginalGramPrimeTuple434 SA ×
             SourceOriginalGramPrimeTuple434 SB,
        weight q * Ksigned q * phase q) =
      σ * (∑ q : SourceOriginalGramPrimeTuple434 SA ×
                 SourceOriginalGramPrimeTuple434 SB,
        weight q * (kA q.1 * kB q.2) * phase q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [hKernelCollapse q]
    ring
  have hErrorSign :
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
             SourceOriginalGramPrimeTuple434 SB,
        weight q * Ksigned q * phase q) - σ * phaseX‖ =
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
             SourceOriginalGramPrimeTuple434 SB,
        weight q * (kA q.1 * kB q.2) * phase q) - phaseX‖ := by
    rw [hFactor, ←mul_sub, norm_mul, hσ, one_mul]
  have hNorm :
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
             SourceOriginalGramPrimeTuple434 SB,
        weight q * (kA q.1 * kB q.2) * phase q) - phaseX‖ ≤
      (ε+ε+ε*ε)*(r:ℝ) +
        ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2)*ω := by
    dsimp only at hMajorInst
    rw [←hMA,←hMB] at hMajorInst
    rw [source_original_probe_target_A_gram_product434
      J ell m hmJ ν P target ht,
      source_original_probe_source_B_gram_product434
      J ell m hmJ ν P source hs] at hMajorInst
    simpa only [SA,SB,muA,muB,weight,kA,kB,phase,phaseX,ε,R,ω,
      Complex.ofReal_mul,mul_assoc,pA,pB] using hMajorInst
  change ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
            SourceOriginalGramPrimeTuple434 SB,
    weight q * Ksigned q * phase q) - σ * phaseX‖ ≤
      (ε+ε+ε*ε)*(r:ℝ) +
        ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2)*ω
  rw [hErrorSign]
  exact hNorm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeLocalDyadicMajor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- SOURCE03 canonical signed ν-pattern REAL major dyad
pointwise comparison: all active original GLOBAL cells,
real rational e(u/r), full Mellin and irrational beta,
unconditional source SW saving L^-B; under authentic
Dirichlet |beta|UV<=2S/r and X_A<=2U, X_B<=2V,
the LOCAL retained-cell product cap, not the coarse
exp(m L^d), gives the needed oscillator estimate uniformly
for all |zeta|<=L^C4.
This is one DYAD-PAIR and one physical endpoint pair;
it is not a proof of minor arcs or full RAW/Hoeffding. -/
theorem source_original_probe_active_local_dyad_log_power_unconditional434
    (Cq Cxi Cs C4 : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [DecidableEq G]
      (J ell m : ℕ) (hmJ : m ≤ J)
      (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ) (V : G → ℝ)
      (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (hMass : ∀ g, Vmin ≤ V g)
      (Q : ℕ)
      (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hA hB xi : ℝ)
      (hhA : 0 < hA) (hhB : 0 < hB)
      (hxi : 0 < xi)
      (jA jB : ℤ)
      (hjA : jA ∈ sourceOriginalProbeActiveCellsA434
        m P V ν hA xi)
      (hjB : jB ∈ sourceOriginalProbeActiveCellsB434
        m P V ν hB xi)
      (L : ℝ) (hL : 192 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (hXi : xi⁻¹ ≤ L^Cxi)
      (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
      (target source : ∀ g,
        Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
      (ht : ∀ g i, target g i ∈ P g)
      (hs : ∀ g i, source g i ∈ P g)
      (hCellA : sourceOriginalLiteralLogCell434 hA jA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target))
      (hCellB : sourceOriginalLiteralLogCell434 hB jB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source))
      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ) (ζ beta : ℝ)
      (U Vdyad S : ℝ)
      (hU : 0 ≤ U) (hVdyad : 0 ≤ Vdyad)
      (hDyadA : (sourceOriginalProbeFreeTargetX434
        J ell m hmJ ν target:ℝ) ≤ 2*U)
      (hDyadB : (sourceOriginalProbeFreeSourceX434
        J ell m hmJ ν source:ℝ) ≤ 2*Vdyad)
      (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
      (hDir : |beta| *(U*Vdyad) ≤ 2*S/(r:ℝ))
      (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
      (hDeltaLe : (K/Vmin)*L^(-(B+(Cq:ℝ))) ≤ 1)
      (hWidth : hA+hB ≤ L^(-(B+((4*Cq+C4:ℕ):ℝ))))
      (hWidth1 : hA+hB ≤ 1)
      (hZeta : |ζ| ≤ L^C4),
      let SA : ν.1 → Finset ℕ := fun z => P z.val.1
      let SB : ν.2 → Finset ℕ := fun z => P z.val.1
      let muA : ν.1 → ℕ → ℝ :=
        fun z => sourcePrimeSharedAtom434 (V z.val.1)
      let muB : ν.2 → ℕ → ℝ :=
        fun z => sourcePrimeSharedAtom434 (V z.val.1)
      let pA := sourceOriginalProbeTargetAIntoGram434
        J ell m hmJ ν P target ht
      let pB := sourceOriginalProbeSourceBIntoGram434
        J ell m hmJ ν P source hs
      let eps : ℝ := (K/Vmin)*L^(-B)
      let R : ℝ := Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB)
      let omega : ℝ := (|ζ|+2*Real.pi*|beta| * R)*(hA+hB)
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                     SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA muA q.1:ℂ) *
         (sourceOriginalGramPrimeMass434 SB muB q.2:ℂ)) *
        sourceOriginalActualPrimitiveComparisonKernel434 Q
          (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
          (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
          hA hB
          (sourceOriginalProbeCellA434 m P V ν hA)
          (sourceOriginalProbeCellB434 m P V ν hB)
          (sourceOriginalGramPrimeProduct434 SA q.1)
          (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target)
          (sourceOriginalGramPrimeProduct434 SB q.2)
          (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
          (ν.1.card+ν.2.card) *
        (sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalGramPrimeProduct434 SA q.1 *
            sourceOriginalGramPrimeProduct434 SB q.2) *
         sourceOriginalSlowMellinAdditivePhase434 ζ beta
           (sourceOriginalGramPrimeProduct434 SA q.1 *
            sourceOriginalGramPrimeProduct434 SB q.2))) -
        (-((-1:ℂ)^(ν.1.card+ν.2.card))) *
        (sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target *
            sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source) *
         sourceOriginalSlowMellinAdditivePhase434 ζ beta
           (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target *
            sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source))‖ ≤
        (3*(K/Vmin)+2)*L^(-B) := by
  let Bplus : ℝ := B+(Cq:ℝ)
  have hBplus : 0 < Bplus := by
    dsimp [Bplus]
    have hCn : (0:ℝ) ≤ Cq := Nat.cast_nonneg _
    linarith
  obtain ⟨K,Y,hK,hOrig⟩ :=
    source_original_probe_full_active_signed_major_slow_unconditional434
      Cq Cxi gamma d Bplus hgamma hd hBplus
  refine ⟨K,Y,hK,?_⟩
  intro G instD J ell m hmJ ν P V hV Vmin hVmin hMass
    Q hBIGA hBIGB hA hB xi hhA hhB hxi
    jA jB hjA hjB L hL hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB target source ht hs hCellA hCellB
    r hr hrQ u ζ beta U Vdyad S
    hU hVdyad hDyadA hDyadB hS hSscale hDir hC4
    hDeltaLe hWidth hWidth1 hZeta
  dsimp
  let XA := sourceOriginalProbeFreeTargetX434
    J ell m hmJ ν target
  let XB := sourceOriginalProbeFreeSourceX434
    J ell m hmJ ν source
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  have hXAp : 0 < XA := by
    have hp :=
      source_original_gram_physical_prime_product_pos434 SA
        (fun z p hp => (hBIGA z p hp).1)
        (sourceOriginalProbeTargetAIntoGram434
          J ell m hmJ ν P target ht)
    rw [source_original_probe_target_A_gram_product434
      J ell m hmJ ν P target ht] at hp
    exact hp
  have hXBp : 0 < XB := by
    have hp :=
      source_original_gram_physical_prime_product_pos434 SB
        (fun z p hp => (hBIGB z p hp).1)
        (sourceOriginalProbeSourceBIntoGram434
          J ell m hmJ ν P source hs)
    rw [source_original_probe_source_B_gram_product434
      J ell m hmJ ν P source hs] at hp
    exact hp
  let δ : ℝ := (K/Vmin)*L^(-Bplus)
  let Rcell : ℝ := Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB)
  let omega : ℝ := (|ζ|+2*Real.pi*|beta| *Rcell)*(hA+hB)
  have hBudget :=
    source_original_local_arc_full_log_power_budget434
      Q Cq Cs C4 r L B K Vmin ζ beta
      hA hB jA jB XA XB U Vdyad S
      hL hQ hrQ hr hK hVmin hDeltaLe
      hhA hhB hWidth hWidth1 hZeta
      hXAp hXBp hU hVdyad hDyadA hDyadB
      hCellA hCellB hS hSscale hDir hC4
  have hSaved :
      (δ+δ+δ*δ)*(r:ℝ) +
        ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2)*
          omega ≤ (3*(K/Vmin)+2)*L^(-B) := by
    simpa only [δ,Bplus,Rcell,omega] using hBudget
  have hLone : 1 ≤ L := by linarith
  have hRaw := hOrig J ell m hmJ ν P V hV
    Vmin hVmin hMass Q hBIGA hBIGB
    hA hB xi hhA hhB hxi jA jB hjA hjB
    L hLone hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB target source ht hs hCellA hCellB
    r hr hrQ u ζ beta
  change _ ≤ (δ+δ+δ*δ)*(r:ℝ) +
      ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2)*
        omega at hRaw
  exact hRaw.trans hSaved
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeSignedMajorSlowError -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- ACTUAL source03 nu-pattern signed residual ERROR for a full
major-arc phase: e((u/r+beta)*D_A*D_B) times
(D_A*D_B)^(i*zeta). The auxiliary prime labels, true harmonic
weights, complete canonical active two-global Knu, pattern
inclusion-exclusion sign -(-1)^(|A|+|B|), and the arbitrary
source/target physical FREE mark arrays are unchanged.
No analytic error bound or independent mark-H(p) assumption
is built into this exact DEFINITION. -/
noncomputable def sourceOriginalProbeSignedMajorSlowError434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (r : ℕ) (hr : 0 < r) (u : ℤ) (ζ beta : ℝ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) : ℂ :=
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target
  let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source
  let σ : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
  let phase : ℕ → ℂ := fun n =>
    sourceOriginalPositiveRationalPhaseAtNat434 r hr u n *
    sourceOriginalSlowMellinAdditivePhase434 ζ beta n
  (∑ ab : SourceOriginalGramPrimeTuple434 SA ×
           SourceOriginalGramPrimeTuple434 SB,
    ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
      (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      hA hB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      (sourceOriginalGramPrimeProduct434 SA ab.1) XA
      (sourceOriginalGramPrimeProduct434 SB ab.2) XB
      (ν.1.card+ν.2.card) *
    phase (sourceOriginalGramPrimeProduct434 SA ab.1 *
       sourceOriginalGramPrimeProduct434 SB ab.2)) -
  σ * phase (XA*XB)

end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePhysicalSignedMajorFourierError -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 28000000

/-- A LITERAL SOURCE03 raw-minus-primitive-comparison
Fourier error at actual frequency -k*theta and actual
Mellin twist ζ, for all genuine ν-dependent source/target
free prime marks. Original full active global cell gates,
primitive characters, prime-product weights, and the
inclusion-exclusion sign are identical to C196's original
rational/Mellin physical signed major kernel.
No beta, rational denominator, or approximation is
hidden in this definition. -/
noncomputable def sourceOriginalProbeSignedMajorFourierError434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (ζ theta : ℝ) (k : ℤ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) : ℂ :=
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target
  let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source
  let σ : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
  let phase : ℕ → ℂ := fun n =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
      Complex.exp (Complex.I *((ζ*Real.log (n:ℝ)):ℂ))
  (∑ ab : SourceOriginalGramPrimeTuple434 SA ×
           SourceOriginalGramPrimeTuple434 SB,
    ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
      (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      hA hB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      (sourceOriginalGramPrimeProduct434 SA ab.1) XA
      (sourceOriginalGramPrimeProduct434 SB ab.2) XB
      (ν.1.card+ν.2.card) *
    phase (sourceOriginalGramPrimeProduct434 SA ab.1 *
       sourceOriginalGramPrimeProduct434 SB ab.2)) -
  σ * phase (XA*XB)

/-- EXACT signed SOURCE03 physical major arithmetic/Fourier
identification. Provided the REAL original circle-arc lift
-k θ = u/r + β - Nshift, and r>0, this equates
the C196 checked original rational+Mellin error coefficient
to the ACTUAL physical raw-versus-primitive-Kν Fourier
error at -k θ. The integer shift vanishes by true
integer Fourier periodicity, and the rational phase is
the unchanged standard ZMod additive character.
This does NOT claim the entire source03 full correlation
operator has already been assembled across ν or marks. -/
theorem source_original_true_signed_major_fourier_error_eq434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (r : ℕ) (hr : 0 < r) (u : ℤ)
    (ζ beta theta : ℝ) (k Nshift : ℤ)
    (hLift : -(k:ℝ)*theta =
      (u:ℝ)/(r:ℝ)+beta-(Nshift:ℝ))
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    sourceOriginalProbeSignedMajorSlowError434
      J ell m hmJ ν P V Q hA hB xi
      r hr u ζ beta source target =
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν P V Q hA hB xi
      ζ theta k source target := by
  have hPhase (n : ℕ) :
      sourceOriginalPositiveRationalPhaseAtNat434 r hr u n *
        sourceOriginalSlowMellinAdditivePhase434 ζ beta n =
      Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
        Complex.exp (Complex.I *((ζ*Real.log (n:ℝ)):ℂ)) :=
    (source_original_true_integer_mellin_dirichlet_phase434
      theta beta ζ k u Nshift r n hr hLift).symm
  unfold sourceOriginalProbeSignedMajorSlowError434
    sourceOriginalProbeSignedMajorFourierError434
  dsimp only
  simp only [hPhase]

/-- The identification is NOT merely pointwise:
it holds under the exact joint physical source/target
bilinear law for all arbitrary complex own-side tests and
all label-sensitive source/target mark arrays.
In particular it can transport checked C196 signed
weighted-L² estimates to the true -kθ Fourier phase. -/
theorem source_original_true_signed_major_fourier_pairing_eq434
    {G X : Type} [DecidableEq G]
    [Fintype X]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (r : ℕ) (hr : 0 < r) (u : ℤ)
    (ζ beta theta : ℝ) (k Nshift : ℤ)
    (hLift : -(k:ℝ)*theta =
      (u:ℝ)/(r:ℝ)+beta-(Nshift:ℝ))
    (source target : X → ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (weight : X → ℝ) (sourceTest targetTest : X → ℂ) :
    (∑ ab : X × X,
      (((weight ab.1*weight ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2) *
      sourceOriginalProbeSignedMajorSlowError434
        J ell m hmJ ν P V Q hA hB xi
        r hr u ζ beta (source ab.1) (target ab.2)) =
    (∑ ab : X × X,
      (((weight ab.1*weight ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2) *
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν P V Q hA hB xi
        ζ theta k (source ab.1) (target ab.2)) := by
  classical
  apply Finset.sum_congr rfl
  intro ab hab
  rw [source_original_true_signed_major_fourier_error_eq434
    J ell m hmJ ν P V Q hA hB xi
    r hr u ζ beta theta k Nshift hLift
    (source ab.1) (target ab.2)]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeRetainedFourierPointwise -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- C191's GENUINE SOURCE03 signed original RAW-minus-canonical
Knu physical Fourier pointwise major comparison for one
retained GLOBAL jA/jB cell and one actual physical dyad.
This is not a synthetic generic approximation: true output
marked prime X_A/X_B, arbitrary other FREE prime labels,
real rational/Mellin/slow phase with exact -k theta and
the true physical source supports remain unchanged.
The rational C191 log saving and all Dirichlet, prime-band,
character and mesh budgets are explicit hypotheses.
No loss from discarded cells; it is a RETAINED major result
prior to two-ended weighted L2/global summation. -/
theorem source_original_probe_active_local_dyad_fourier_pointwise434
    (Cq Cxi Cs C4 : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [DecidableEq G]
      (J ell m : ℕ) (hmJ : m ≤ J)
      (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ) (V : G → ℝ)
      (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (hMass : ∀ g, Vmin ≤ V g)
      (Q : ℕ)
      (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hA hB xi : ℝ)
      (hhA : 0 < hA) (hhB : 0 < hB)
      (hxi : 0 < xi)
      (jA jB : ℤ)
      (hjA : jA ∈ sourceOriginalProbeActiveCellsA434
        m P V ν hA xi)
      (hjB : jB ∈ sourceOriginalProbeActiveCellsB434
        m P V ν hB xi)
      (L : ℝ) (hL : 192 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (hXi : xi⁻¹ ≤ L^Cxi)
      (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
      (target source : ∀ g,
        Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
      (ht : ∀ g i, target g i ∈ P g)
      (hs : ∀ g i, source g i ∈ P g)
      (hCellA : sourceOriginalLiteralLogCell434 hA jA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target))
      (hCellB : sourceOriginalLiteralLogCell434 hB jB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source))
      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ) (ζ beta : ℝ)
      (theta : ℝ) (k Nshift : ℤ)
      (hLift : -(k:ℝ)*theta =
        (u:ℝ)/(r:ℝ)+beta-(Nshift:ℝ))
      (U Vdyad S : ℝ)
      (hU : 0 ≤ U) (hVdyad : 0 ≤ Vdyad)
      (hDyadA : (sourceOriginalProbeFreeTargetX434
        J ell m hmJ ν target:ℝ) ≤ 2*U)
      (hDyadB : (sourceOriginalProbeFreeSourceX434
        J ell m hmJ ν source:ℝ) ≤ 2*Vdyad)
      (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
      (hDir : |beta| *(U*Vdyad) ≤ 2*S/(r:ℝ))
      (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
      (hDeltaLe : (K/Vmin)*L^(-(B+(Cq:ℝ))) ≤ 1)
      (hWidth : hA+hB ≤ L^(-(B+((4*Cq+C4:ℕ):ℝ))))
      (hWidth1 : hA+hB ≤ 1)
      (hZeta : |ζ| ≤ L^C4),
      ‖sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν P V Q hA hB xi ζ theta k source target‖ ≤
      (3*(K/Vmin)+2)*L^(-B) := by
  obtain ⟨K,Y,hK,hMain⟩ :=
    source_original_probe_active_local_dyad_log_power_unconditional434
      Cq Cxi Cs C4 gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro G instD J ell m hmJ ν P V hV Vmin hVmin hMass
    Q hBIGA hBIGB hA hB xi hhA hhB hxi
    jA jB hjA hjB L hL hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB target source ht hs hCellA hCellB
    r hr hrQ u ζ beta theta k Nshift hLift
    U Vdyad S hU hVdyad hDyadA hDyadB
    hS hSscale hDir hC4 hDeltaLe hWidth hWidth1 hZeta
  have hRational := hMain
    J ell m hmJ ν P V hV
    Vmin hVmin hMass Q hBIGA hBIGB
    hA hB xi hhA hhB hxi jA jB hjA hjB
    L hL hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB target source ht hs hCellA hCellB
    r hr hrQ u ζ beta U Vdyad S hU hVdyad
    hDyadA hDyadB hS hSscale hDir hC4
    hDeltaLe hWidth hWidth1 hZeta
  have hIdentity :=
    source_original_true_signed_major_fourier_error_eq434
      J ell m hmJ ν P V Q hA hB xi
      r hr u ζ beta theta k Nshift hLift source target
  change
    ‖sourceOriginalProbeSignedMajorSlowError434
      J ell m hmJ ν P V Q hA hB xi
      r hr u ζ beta source target‖ ≤
        (3*(K/Vmin)+2)*L^(-B) at hRational
  rw [hIdentity] at hRational
  exact hRational
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueGlobalPairRetainedFourierPointwise -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The genuine SOURCE03 retained signed major error for one
ACTUAL source-B/target-A prime-mark state pair, at the OWN
rational arc of the original GLOBAL cells jB,jA. Character
and active cell tests are not substituted. Using the real
prime-band/Dirichlet estimates and original beta+Mellin
phase, it proves a pointwise L^-B saving without requiring
a primitive-character witness as a fake source of geometry.
This is not yet the full weighted-L2 / all-pattern operator. -/
theorem source_original_true_global_pair_retained_fourier_pointwise434
    (Cq Cxi Cs C4 : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      (J ell m : ℕ) (hmJ : m ≤ J)
      (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ) (V : G → ℝ)
      (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (hMass : ∀ g, Vmin ≤ V g)
      (Q : ℕ)
      (jA jB : ℤ)
      (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hA hB xi : ℝ)
      (hhA : 0 < hA) (hhB : 0 < hB)
      (hxi : 0 < xi)
      (L : ℝ) (hL : 192 ≤ L)
      (hPrimeUpperA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
      (hPrimeUpperB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
        p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (hXi : xi⁻¹ ≤ L^Cxi)
      (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
      (ζ theta : ℝ) (k : ℤ) (D Carc : ℝ)
      (Uscale Vscale S : ℝ)
      (hUscale : 0 ≤ Uscale) (hVscale : 0 ≤ Vscale)
      (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
      (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Q)
      (hBudget :
        3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ))*
          |(k:ℝ)| *L^Carc ≤ 2*S)
      (hOwn : (theta:AddCircle (1:ℝ)) ∈
        sourceCircleRationalArcs434
          (k.natAbs*Nat.ceil (L^(D+1)))
          (L^Carc/(Real.exp ((jA:ℝ)*hA)*Real.exp ((jB:ℝ)*hB))))
      (hScaleA : Uscale =
        Real.exp (((jA:ℝ)+1)*hA))
      (hScaleB : Vscale =
        Real.exp (((jB:ℝ)+1)*hB))
      (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
      (hDeltaLe : (K/Vmin)*L^(-(B+(Cq:ℝ))) ≤ 1)
      (hWidth : hA+hB ≤ L^(-(B+((4*Cq+C4:ℕ):ℝ))))
      (hWidth1 : hA+hB ≤ 1)
      (hZeta : |ζ| ≤ L^C4)
      (hjA : jA ∈ sourceOriginalProbeActiveCellsA434
        m P V ν hA xi)
      (hjB : jB ∈ sourceOriginalProbeActiveCellsB434
        m P V ν hB xi)
      (s v : SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν))
      (hIdxB : sourceOriginalLiteralLogCellIndex434 hB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val)) = jB)
      (hIdxA : sourceOriginalLiteralLogCellIndex434 hA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val)) = jA), 
      ‖sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν P V Q hA hB xi ζ theta k
          (fun g i => (s g i).val)
          (fun g i => (v g i).val)‖ ≤
        (3*(K/Vmin)+2)*L^(-B) := by
  obtain ⟨K,Y,hK,hPoint⟩ :=
    source_original_probe_active_local_dyad_fourier_pointwise434
      Cq Cxi Cs C4 gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro G instF instD J ell m hmJ ν P V hV Vmin hVmin hMass
    Q jA jB hBIGA hBIGB hA hB xi hhA hhB hxi L hL
    hPrimeUpperA hPrimeUpperB hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB ζ theta k D Carc
    Uscale Vscale S hUscale hVscale hS hSscale
    hQchar hBudget hOwn hScaleA hScaleB
    hC4 hDeltaLe hWidth hWidth1 hZeta
    hjA hjB s v hIdxB hIdxA
  classical
  have hCap : Uscale*Vscale ≤
      3*(Real.exp ((jA:ℝ)*hA)*Real.exp ((jB:ℝ)*hB)) := by
    rw [hScaleA,hScaleB]
    exact source_original_true_global_pair_upper_C196_cap434
      hA hB jA jB hWidth1
  obtain ⟨beta,q',hq',u',Nshift,
      hqQ,hCop,hFrequency,hCellDir,hPhase⟩ :=
    source_original_true_global_pair_reduced_dyad_C196_dir434
      Q hA hB jA jB L D Carc k theta S 0
      (by linarith : 0 ≤ L) hQchar hBudget hOwn
  have hDir : |beta| * (Uscale*Vscale) ≤ 2*S/(q':ℝ) :=
    hCellDir Uscale Vscale hCap
  have hSource := source_original_true_own_retained_source_gate434
    J ell m hmJ ν P V
    (fun z p hp => (hBIGB z p hp).1)
    hB xi hhB jB hjB Vscale hScaleB s hIdxB
  have hTarget := source_original_true_own_retained_target_gate434
    J ell m hmJ ν P V
    (fun z p hp => (hBIGA z p hp).1)
    hA xi hhA jA hjA Uscale hScaleA v hIdxA
  have hCellA : sourceOriginalLiteralLogCell434 hA jA
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
       (fun g i => (v g i).val)) :=
    (source_original_literal_log_cell_iff_index434
      hA hhA _ jA).mpr hIdxA.symm
  have hCellB : sourceOriginalLiteralLogCell434 hB jB
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
       (fun g i => (s g i).val)) :=
    (source_original_literal_log_cell_iff_index434
      hB hhB _ jB).mpr hIdxB.symm
  exact hPoint J ell m hmJ ν P V hV
    Vmin hVmin hMass Q hBIGA hBIGB
    hA hB xi hhA hhB hxi jA jB hjA hjB
    L hL hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB
    (fun g i => (v g i).val) (fun g i => (s g i).val)
    (fun g i => (v g i).property) (fun g i => (s g i).property)
    hCellA hCellB
    q' hq' hqQ u' ζ beta theta k Nshift hFrequency
    Uscale Vscale S hUscale hVscale
    hTarget.2 hSource.2 hS hSscale hDir hC4
    hDeltaLe hWidth hWidth1 hZeta
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuPrimitiveFourierTerm -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Actual pair of two genuine original primitive Dirichlet
character/conductor indices, with independently selected
target-A and source-B GLOBAL cell indices. -/
abbrev SourceOriginalTruePrimitivePairIndex434 (Q : ℕ) :=
  (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))) ×
    (ℤ × (Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)))

/-- One EXACT source03 primitive comparison summand under
the original independently weighted auxiliary A/B prime laws.
Unlike the full canonical kernel, this term fixes precisely
ONE (jA,χA,jB,χB) primitive mode and does NOT contain the
raw branch. The coupled real -kθ and Mellin ζ product
phase is attached inside the true auxiliary expectation. -/
noncomputable def sourceOriginalTrueNuPrimitiveFourierTerm434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi ζ theta : ℝ) (k : ℤ)
    (t : SourceOriginalTruePrimitivePairIndex434 Q)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) : ℂ :=
  let SA : ν.1 → Finset ℕ := fun a => P a.val.1
  let SB : ν.2 → Finset ℕ := fun b => P b.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun a => sourcePrimeSharedAtom434 (V a.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun b => sourcePrimeSharedAtom434 (V b.val.1)
  let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target
  let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source
  let phase : ℕ → ℂ := fun n =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
    Complex.exp (Complex.I *((ζ*Real.log (n:ℝ)):ℂ))
  ∑ ab : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB,
    ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
     (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
      (-((-1:ℂ)^(ν.1.card+ν.2.card)) *
        sourceOriginalCharacterCellAtom434
          (sourceOriginalLiteralLogCell434 hA)
          (sourceOriginalProbeCellA434 m P V ν hA)
          (fun c n => c.2 (n:ZMod (c.1.val+1)))
          t.1.1 t.1.2 (sourceOriginalGramPrimeProduct434 SA ab.1) XA *
        sourceOriginalCharacterCellAtom434
          (sourceOriginalLiteralLogCell434 hB)
          (sourceOriginalProbeCellB434 m P V ν hB)
          (fun c n => c.2 (n:ZMod (c.1.val+1)))
          t.2.1 t.2.2 (sourceOriginalGramPrimeProduct434 SB ab.2) XB) *
      phase (sourceOriginalGramPrimeProduct434 SA ab.1 *
             sourceOriginalGramPrimeProduct434 SB ab.2)

/-- EXACT raw term of one original SOURCE03 ν, counted ONCE
independently of cell/character expansion multiplicity. -/
noncomputable def sourceOriginalTrueNuRawFourierTerm434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi ζ theta : ℝ) (k : ℤ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) : ℂ :=
  let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target
  let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source
  let σ : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
  let phase : ℕ → ℂ := fun n =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
    Complex.exp (Complex.I *((ζ*Real.log (n:ℝ)):ℂ))
  σ*phase (XA*XB)

end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSignedFourierSelectedFactor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- The ORIGINAL SOURCE03 signed RAW-minus-canonical Knu
error as an honest TWO-INTEGER kernel on its exactly selected
SOURCE-B and TARGET-A products. This keeps the entire
auxiliary independently labelled prime law, both primitive
GLOBAL character kernels, original sign and real
Fourier/Mellin phase. Other unselected free physical marks
do not enter the kernel; the endpoint tests may depend on
all of them. No analytic saving is postulated. -/
noncomputable def sourceOriginalProbeSignedSelectedFourierError434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (ζ theta : ℝ) (k : ℤ)
    (XA XB : ℕ) : ℂ :=
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let σ : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
  let phase : ℕ → ℂ := fun n =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
      Complex.exp (Complex.I *((ζ*Real.log (n:ℝ)):ℂ))
  (∑ ab : SourceOriginalGramPrimeTuple434 SA ×
           SourceOriginalGramPrimeTuple434 SB,
    ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
      (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      hA hB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      (sourceOriginalGramPrimeProduct434 SA ab.1) XA
      (sourceOriginalGramPrimeProduct434 SB ab.2) XB
      (ν.1.card+ν.2.card) *
    phase (sourceOriginalGramPrimeProduct434 SA ab.1 *
      sourceOriginalGramPrimeProduct434 SB ab.2)) -
  σ * phase (XA*XB)
/-- Exact two-product factorization for the ACTUAL ν-dependent
physical source and target mark lists. The full signed Fourier
residual only sees SOURCE-B product XB and TARGET-A product XA,
not other full free-slot marks. THIS justifies, rather than
assumes, conditional projection of arbitrary full-state tests
before applying SOURCE03 true C6 selected-product estimates. -/
theorem source_original_true_signed_fourier_selected_factor434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (ζ theta : ℝ) (k : ℤ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν P V Q hA hB xi ζ theta k source target =
    sourceOriginalProbeSignedSelectedFourierError434
      J ell m hmJ ν P V Q hA hB xi ζ theta k
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target)
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source) := by
  rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePhysicalMaskedSignedCell -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The LITERAL SOURCE03 true signed RAW-minus-primitive-Knu
Fourier/Mellin residual with ONE active SOURCE-B/TARGET-A
original GLOBAL product-log cell pair. A true C6 bound on
the actual selected two-integer JOINT signed kernel restricted
to that pair controls arbitrary original FULL free-prime-mark
physical endpoint tests. Uses kernel-checked exact SOURCE03
B/A marginal probabilities and sharp inverse-atom L2 pushforward.
NO artificial tensor factorization, output-count loss or assumed
physical independence. The selected C6 arithmetic input remains
explicit; this theorem is its exact physical lift. -/
theorem source_original_true_physical_masked_signed_cell434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (hPrime : ∀ g, ∀ p ∈ P g, p.Prime)
    (Q : ℕ) (hA hB xi ζ theta : ℝ) (k : ℤ)
    (jA jB : ℤ) (budget : ℝ) (hBudget : 0 ≤ budget) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let SB : ν.2 → Finset ℕ := fun z => P z.val.1
    let SA : ν.1 → Finset ℕ := fun z => P z.val.1
    let muB : ν.2 → ℕ → ℝ := fun z p =>
      (1/(p:ℝ))/(V z.val.1)
    let muA : ν.1 → ℕ → ℝ := fun z p =>
      (1/(p:ℝ))/(V z.val.1)
    let TB := sourceOriginalPhysicalProductAtomSupport434 SB
    let TA := sourceOriginalPhysicalProductAtomSupport434 SA
    let projS : X → ℕ := fun s =>
      sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val)
    let projT : X → ℕ := fun v =>
      sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val)
    let actB : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 hB n=jB
    let actA : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 hA n=jA
    let H : ℕ → ℕ → ℂ := fun nB nA =>
      if actB nB ∧ actA nA then
        sourceOriginalProbeSignedSelectedFourierError434
          J ell m hmJ ν P V Q hA hB xi ζ theta k nA nB
      else 0
    (∀ a b : ℕ → ℂ,
      ‖(∑ ij ∈ TB.product TA,
        a ij.1*b ij.2*H ij.1 ij.2)‖^2 ≤
      budget *
        (∑ n ∈ TB,
          ‖a n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n) *
        (∑ n ∈ TA,
          ‖b n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n)) →
    ∀ sourceTest targetTest : X → ℂ,
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*
        (if actB (projS ab.1) ∧ actA (projT ab.2) then
          sourceOriginalProbeSignedMajorFourierError434
            J ell m hmJ ν P V Q hA hB xi ζ theta k
            (fun g i => (ab.1 g i).val)
            (fun g i => (ab.2 g i).val)
         else 0))‖^2 ≤
      budget*(∑ s : X, w s*‖sourceTest s‖^2) *
             (∑ v : X, w v*‖targetTest v‖^2) := by
  classical
  dsimp only
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let muB : ν.2 → ℕ → ℝ := fun z p =>
    (1/(p:ℝ))/(V z.val.1)
  let muA : ν.1 → ℕ → ℝ := fun z p =>
    (1/(p:ℝ))/(V z.val.1)
  let TB := sourceOriginalPhysicalProductAtomSupport434 SB
  let TA := sourceOriginalPhysicalProductAtomSupport434 SA
  let projS : X → ℕ := fun s =>
    sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (fun g i => (s g i).val)
  let projT : X → ℕ := fun v =>
    sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (fun g i => (v g i).val)
  let actB : ℕ → Prop := fun n =>
    sourceOriginalLiteralLogCellIndex434 hB n=jB
  let actA : ℕ → Prop := fun n =>
    sourceOriginalLiteralLogCellIndex434 hA n=jA
  let H : ℕ → ℕ → ℂ := fun nB nA =>
    if actB nB ∧ actA nA then
      sourceOriginalProbeSignedSelectedFourierError434
        J ell m hmJ ν P V Q hA hB xi ζ theta k nA nB
    else 0
  intro hSelected sourceTest targetTest
  have hLift := source_original_true_physical_matched_atom_operator434
    J ell m hmJ ν P V hV hVpos hPrime H budget hBudget
    hSelected sourceTest targetTest
  have hKernel (ab : X × X) :
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν P V Q hA hB xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val) =
      sourceOriginalProbeSignedSelectedFourierError434
        J ell m hmJ ν P V Q hA hB xi ζ theta k
        (projT ab.2) (projS ab.1) :=
    source_original_true_signed_fourier_selected_factor434
      J ell m hmJ ν P V Q hA hB xi ζ theta k
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  have hPhysicalMask (ab : X × X) :
      (sourceOriginalLiteralLogCellIndex434 hB
          (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
            (fun g i => (ab.1 g i).val))=jB ∧
       sourceOriginalLiteralLogCellIndex434 hA
          (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
            (fun g i => (ab.2 g i).val))=jA) =
      (actB (projS ab.1) ∧ actA (projT ab.2)) := rfl
  change ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*
        H (projS ab.1) (projT ab.2))‖^2 ≤
      budget*(∑ s : X, w s*‖sourceTest s‖^2) *
             (∑ v : X, w v*‖targetTest v‖^2) at hLift
  calc
    _ = ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*
        H (projS ab.1) (projT ab.2))‖^2 := by
      apply congrArg (fun z : ℂ => ‖z‖^2)
      apply Finset.sum_congr rfl
      intro ab hab
      by_cases hc : actB (projS ab.1) ∧ actA (projT ab.2)
      · simp only [hPhysicalMask ab, H, if_pos hc]
        rw [hKernel ab]
      · simp only [hPhysicalMask ab, H, if_neg hc, mul_zero]
    _ ≤ _ := hLift
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSelectedRawKnuMellinIdentity -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- ORIGINAL SOURCE03 selected two-integer Fourier/Mellin error
is LITERALLY the true signed primitive Knu physical auxiliary
prime-tuple expectation MINUS the true signed RAW output phase.
Both independently labelled prime supports, all active GLOBAL
and primitive-character kernels, the inclusion-exclusion
parity sign, Fourier -k theta and original Mellin zeta match
exactly. No magnitude estimates, independence substitutions
or new arithmetic assumptions are introduced. -/
theorem source_original_true_selected_RAW_Knu_mellin_identity434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi ζ theta : ℝ) (k : ℤ)
    (XA XB : ℕ) :
    let SA : ν.1 → Finset ℕ := fun z => P z.val.1
    let SB : ν.2 → Finset ℕ := fun z => P z.val.1
    let muA : ν.1 → ℕ → ℝ :=
      fun z p => sourcePrimeSharedAtom434 (V z.val.1) p
    let muB : ν.2 → ℕ → ℝ :=
      fun z p => sourcePrimeSharedAtom434 (V z.val.1) p
    let DA : SourceOriginalGramPrimeTuple434 SA → ℕ :=
      sourceOriginalGramPrimeProduct434 SA
    let DB : SourceOriginalGramPrimeTuple434 SB → ℕ :=
      sourceOriginalGramPrimeProduct434 SB
    let Knu : ℂ :=
      ∑ ab : SourceOriginalGramPrimeTuple434 SA ×
             SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
         (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
        sourceOriginalActualPrimitiveComparisonKernel434 Q
          (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
          (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
          hA hB
          (sourceOriginalProbeCellA434 m P V ν hA)
          (sourceOriginalProbeCellB434 m P V ν hB)
          (DA ab.1) XA (DB ab.2) XB
          (ν.1.card+ν.2.card) *
        (Green64SourceC6.integerPhase (-(k:ℝ)*theta)
          (((DA ab.1*DB ab.2:ℕ):ℤ)) *
         sourceOriginalPureMellinPhase434 ζ (DA ab.1*DB ab.2))
    let SignedRaw : ℂ :=
      -((-1:ℂ)^(ν.1.card+ν.2.card)) *
      (Green64SourceC6.integerPhase (-(k:ℝ)*theta) (((XA*XB:ℕ):ℤ)) *
       sourceOriginalPureMellinPhase434 ζ (XA*XB))
    sourceOriginalProbeSignedSelectedFourierError434
      J ell m hmJ ν P V Q hA hB xi ζ theta k XA XB =
      Knu-SignedRaw := by
  classical
  rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSelectedRawKnuHarmonicIdentity -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The two literal SOURCE03 inverse-prime normalization formulas
are equal for ALL real V and natural primes p (including zero
edge cases, without introducing an artificial V>0 axiom).
The actual C6 tuple laws use (1/p)/V, whereas the original
signed selected Fourier kernel uses 1/(p*V). -/
theorem source_original_true_harmonic_inverse_normalizations434
    (V : ℝ) (p : ℕ) :
    sourcePrimeSharedAtom434 V p = (1/(p:ℝ))/V := by
  simp only [sourcePrimeSharedAtom434,div_eq_mul_inv,
    mul_inv_rev,one_mul]
  ring

/-- Same equality at the TRUE labelled-prime product law,
without replacing the variable-size ν-indexed group family. -/
theorem source_original_true_gram_harmonic_normalization434
    {I : Type} [Fintype I] [DecidableEq I]
    (S : I → Finset ℕ) (V : I → ℝ)
    (v : SourceOriginalGramPrimeTuple434 S) :
    sourceOriginalGramPrimeMass434 S
      (fun i p => sourcePrimeSharedAtom434 (V i) p) v =
    sourceOriginalGramPrimeMass434 S
      (fun i p => (1/(p:ℝ))/(V i)) v := by
  unfold sourceOriginalGramPrimeMass434
  apply Finset.prod_congr rfl
  intro i hi
  exact source_original_true_harmonic_inverse_normalizations434
    (V i) (v i).val

/-- The EXACT selected SOURCE03 RAW-minus-primitive-Knu Fourier/
Mellin kernel written in the same true 1/(p V_g) harmonic
tuple masses as our independently C6-verified five-index
signed theorem; no change to character/global families,
inclusion-exclusion sign, selected output products or phase. -/
theorem source_original_true_selected_RAW_Knu_real_masses434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi ζ theta : ℝ) (k : ℤ)
    (XA XB : ℕ) :
    let SA : ν.1 → Finset ℕ := fun z => P z.val.1
    let SB : ν.2 → Finset ℕ := fun z => P z.val.1
    let muA : ν.1 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(V z.val.1)
    let muB : ν.2 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(V z.val.1)
    let X := SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB
    let DA : X → ℕ := fun v =>
      sourceOriginalGramPrimeProduct434 SA v.1
    let DB : X → ℕ := fun v =>
      sourceOriginalGramPrimeProduct434 SB v.2
    let w : X → ℂ := fun v =>
      (sourceOriginalGramPrimeMass434 SA muA v.1:ℂ) *
      (sourceOriginalGramPrimeMass434 SB muB v.2:ℂ)
    let phase : X → ℂ := fun v =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta)
        (((DA v*DB v:ℕ):ℤ)) *
      sourceOriginalPureMellinPhase434 ζ (DA v*DB v)
    let Knu : ℂ := ∑ v : X,
      w v*sourceOriginalActualPrimitiveComparisonKernel434 Q
        (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
        (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
        hA hB
        (sourceOriginalProbeCellA434 m P V ν hA)
        (sourceOriginalProbeCellB434 m P V ν hB)
        (DA v) XA (DB v) XB
        (ν.1.card+ν.2.card) * phase v
    let SignedRaw : ℂ :=
      -((-1:ℂ)^(ν.1.card+ν.2.card)) *
      (Green64SourceC6.integerPhase (-(k:ℝ)*theta)
        (((XA*XB:ℕ):ℤ)) *
       sourceOriginalPureMellinPhase434 ζ (XA*XB))
    sourceOriginalProbeSignedSelectedFourierError434
      J ell m hmJ ν P V Q hA hB xi ζ theta k XA XB =
      Knu-SignedRaw := by
  classical
  have hId :=
    source_original_true_selected_RAW_Knu_mellin_identity434
      J ell m hmJ ν P V Q hA hB xi ζ theta k XA XB
  dsimp only at hId
  simpa only [sourceOriginalGramPrimeMass434,
    source_original_true_harmonic_inverse_normalizations434]
    using hId
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualCanonicalDyadicResidual -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Exact identity with the LITERAL selected SOURCE03 Fourier residual,
including its canonical active cells, true cell probabilities, endpoint
parity sign and all auxiliary prime labels. Endpoint tests remain
arbitrary functions of all their selected prime labels. -/
theorem source_original_actual_canonical_signed_residual_identity434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi ζ theta : ℝ) (k : ℤ)
    (fA : SourceOriginalGramPrimeTuple434 (fun z : ν.1 => P z.val.1) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 (fun z : ν.2 => P z.val.1) → ℂ) :
    let SA : ν.1 → Finset ℕ := fun z => P z.val.1
    let SB : ν.2 → Finset ℕ := fun z => P z.val.1
    let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(V z.val.1)
    let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(V z.val.1)
    let JA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let JB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    sourceOriginalFiniteTwoSidedMinorBilinear434
      (fun p => (sourceOriginalGramPrimeMass434 SA muA p:ℂ))
      (fun p => (sourceOriginalGramPrimeMass434 SB muB p:ℂ))
      fA fB (fun p =>
        sourceOriginalProbeSignedSelectedFourierError434
          J ell m hmJ ν P V Q hA hB xi ζ theta k
          (sourceOriginalGramPrimeProduct434 SA p.1)
          (sourceOriginalGramPrimeProduct434 SB p.2)) =
    sourceOriginalActualKnuPair434 SA muA SB muB
      hA hB JA JB Q (ν.1.card+ν.2.card) fA fB
      (sourceOriginalActualC6Phase434 SA SB theta ζ k) -
      (-((-1:ℂ)^(ν.1.card+ν.2.card))) *
      sourceOriginalFiniteTwoSidedMinorBilinear434
        (fun p => (sourceOriginalGramPrimeMass434 SA muA p:ℂ))
        (fun p => (sourceOriginalGramPrimeMass434 SB muB p:ℂ))
        fA fB (sourceOriginalActualC6Phase434 SA SB theta ζ k) := by
  classical
  dsimp only
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(V z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(V z.val.1)
  have hWeight (v : ℝ) : sourcePrimeSharedAtom434 v =
      (fun p : ℕ => (1/(p:ℝ))/v) := by
    funext p
    exact source_original_true_harmonic_inverse_normalizations434 v p
  have hMA : sourceOriginalProbeCellA434 m P V ν hA =
      sourceOriginalRealGramCellMass434 SA muA hA := by
    funext j
    simpa only [hWeight]
      using source_original_probe_A_cell_probability_gram434 m ν P V hA j
  have hMB : sourceOriginalProbeCellB434 m P V ν hB =
      sourceOriginalRealGramCellMass434 SB muB hB := by
    funext j
    simpa only [hWeight]
      using source_original_probe_B_cell_probability_gram434 m ν P V hB j
  unfold sourceOriginalActualKnuPair434 sourceOriginalFiniteTwoSidedMinorBilinear434
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only
  rw [source_original_true_selected_RAW_Knu_real_masses434]
  dsimp only
  rw [hMA,hMB]
  simp only [sourceOriginalActualC6Phase434,Finset.mul_sum,mul_sub]
  congr 1
  · apply Finset.sum_congr rfl
    intro q hq
    ring
  · ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCanonicalDyadicMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- Genuine C6 minor saving for the LITERAL canonical SOURCE03
signed selected Fourier/Mellin error on one aligned coarse dyad.
The true active cells and their retained masses are DERIVED from
the original definitions, not assumed as free analytical data.
No assumed operator norm/smallness or fine-cell count is used. -/
theorem eventually_source_original_CANONICAL_DYADIC_RESIDUAL_minor434
    (cfg : SourceComparisonFixed434)
    (Cq : ℕ) (Cxi gamma dscale : ℝ)
    (hCxi : 0 ≤ Cxi) (hgamma : 0 < gamma) (hdscale : 0 ≤ dscale) :
    ∃ Y0 : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 d)
      (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (ν : SourceOriginalProbePattern434 β m)
      (hPattern : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (Qchar : ℕ)
      (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
      (xi : ℝ) (hxi : 0 < xi) (hXipoly : xi⁻¹ ≤ L^Cxi)
      (hQchar : (Qchar:ℝ) ≤ L^Cq)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hBIG : ∀ g : β, ∀ p ∈ d.Tb g, Qchar^2 < p)
      (J ell : ℕ) (hmJ : m ≤ J)
      (fA : SourceOriginalGramPrimeTuple434
        (fun z : ν.1 => d.Tb z.val.1) → ℂ)
      (fB : SourceOriginalGramPrimeTuple434
        (fun z : ν.2 => d.Tb z.val.1) → ℂ),
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    ∀ (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^dscale))
      (hvB : (vB:ℝ) ≤ Real.exp (L^dscale))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Qchar^2 ≤ uA) (huBIGB : Qchar^2 ≤ uB)
      (hYA : Y0 ≤ ((uA+1:ℕ):ℝ)) (hYB : Y0 ≤ ((uB+1:ℕ):ℝ))
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (ζ : ℝ)
      (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
      (a : ℤ) (r : ℕ) (beta0 theta : ℝ) (k : ℤ)
      (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
      (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
      (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
      (hP : P ≤ M) (hQ : Q ≤ N)
      (D Bsave : ℝ)
      (hR : L^D ≤ (r:ℝ))
      (hNlarge : L^D ≤ (N:ℝ))
      (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
      (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤ (M:ℝ)*(N:ℝ))
      (C : ℕ)
      (hExponent : cfg.C0*
        Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
          (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
      (hSaving : Bsave+2*(C:ℝ) ≤ D)
      (NA NB : ℕ) (hNA : 0 < NA) (hNB : 0 < NB)
      (hAlignA : hA = Real.log 2/(NA:ℝ))
      (hAlignB : hB = Real.log 2/(NB:ℝ))
      (sA sB : ℕ) (hMA : M = 2^sA) (hNBscale : N = 2^sB)
      (hPM : P = M) (hQN : Q = N)
      (hSuppA : ∀ p, sourceOriginalGramPrimeProduct434 SA p ∉
        Finset.Ico (2^sA) (2^(sA+1)) → fA p = 0)
      (hSuppB : ∀ p, sourceOriginalGramPrimeProduct434 SB p ∉
        Finset.Ico (2^sB) (2^(sB+1)) → fB p = 0),
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    let EA : ℝ := ∑ p : SourceOriginalGramPrimeTuple434 SA,
      sourceOriginalGramPrimeMass434 SA muA p * ‖fA p‖^2
    let EB : ℝ := ∑ p : SourceOriginalGramPrimeTuple434 SB,
      sourceOriginalGramPrimeMass434 SB muB p * ‖fB p‖^2
    ‖sourceOriginalFiniteTwoSidedMinorBilinear434
      (fun p => (sourceOriginalGramPrimeMass434 SA muA p:ℂ))
      (fun p => (sourceOriginalGramPrimeMass434 SB muB p:ℂ))
      fA fB (fun p =>
        sourceOriginalProbeSignedSelectedFourierError434
          J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi ζ theta k
          (sourceOriginalGramPrimeProduct434 SA p.1)
          (sourceOriginalGramPrimeProduct434 SB p.2))‖^2 ≤
      4250*(EA*EB)*L^(-Bsave) := by
  obtain ⟨Y0,hEvent⟩ :=
    eventually_source_original_actual_aligned_DYADIC_RESIDUAL_minor434
      cfg Cq Cxi gamma dscale hCxi hgamma hdscale
  refine ⟨Y0,?_⟩
  filter_upwards [hEvent] with L hMinor
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ fA fB
  dsimp only
  intro iA iB uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    ζ M N P Q hM hN a r beta0 theta k hApprox hr hcop hbeta hP hQ
    D Bsave hR hNlarge hMlarge hMNlarge C hExponent hSaving
    NA NB hNA hNB hAlignA hAlignB sA sB hMA hNBscale hPM hQN hSuppA hSuppB
  classical
  let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
  let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let JA := sourceOriginalProbeActiveCellsA434 m d.Tb d.Vbig ν hA xi
  let JB := sourceOriginalProbeActiveCellsB434 m d.Tb d.Vbig ν hB xi
  have hWeight (v : ℝ) : sourcePrimeSharedAtom434 v =
      (fun p : ℕ => (1/(p:ℝ))/v) := by
    funext p
    exact source_original_true_harmonic_inverse_normalizations434 v p
  have hMassA (j : ℤ) (hj : j ∈ JA) :
      xi ≤ sourceOriginalRealGramCellMass434 SA muA hA j := by
    have hh := (source_original_probe_active_cell_A_mem_iff434
      m d.Tb d.Vbig ν hA xi hhA hxi j).mp hj
    rw [source_original_probe_A_cell_probability_gram434] at hh
    simpa only [hWeight] using hh
  have hMassB (j : ℤ) (hj : j ∈ JB) :
      xi ≤ sourceOriginalRealGramCellMass434 SB muB hB j := by
    have hh := (source_original_probe_active_cell_B_mem_iff434
      m d.Tb d.Vbig ν hB xi hhB hxi j).mp hj
    rw [source_original_probe_B_cell_probability_gram434] at hh
    simpa only [hWeight] using hh
  rw [source_original_actual_canonical_signed_residual_identity434]
  exact hMinor x Y Hprime d sep hVbig blockA blockB hDisjoint m hm ν
    hPattern Qchar JA JB hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG
    fA fB hMassA hMassB iA iB uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    ζ M N P Q hM hN a r beta0 theta k hApprox hr hcop hbeta hP hQ
    D Bsave hR hNlarge hMlarge hMNlarge C hExponent hSaving
    NA NB hNA hNB hAlignA hAlignB sA sB hMA hNBscale hPM hQN hSuppA hSuppB
end Green64Analytic.CorrelationSquare

end

