module

public import Green64.Library.Sieve.Foundations.Part009
public import Green64.Library.Weights.Part117
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-!
# Sieve / Foundations / Part010

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalXASmoothedFullEFibre -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 34000

/-- The complete actual ORIGINAL X cutoff and ORIGINAL real Psi weight
commute EXACTLY with the *already inserted* B590 buffered allocation,
B509 Fourier split, full 20! labelled source and physical P-parity/W1
transfer. The u-range is the positive part of the original XA carrier;
zero is explicitly excluded for the physical source-to-v identity.
This is an exact identity of the SMOOTHED descendant of XA and does
NOT claim that the buffered f0/f1 sum is identically 1 or that the
historical Parity(4.7) post-integration a_e has been identified. -/
theorem parity_actual_original_XA_smoothed_full_source_to_e_v434
    (d : ℕ) (L E x : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (Psi : ℝ → ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ) :
    (∑ u ∈ Finset.Icc 1 (⌊2*x⌋₊),
      (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
        parityActualOriginalAFullBranchWeight434 d L E u band slot ξ z) *
          (Psi ((u:ℝ)/x) : ℂ)) =
    ∑ u ∈ Finset.Icc 1 (⌊2*x⌋₊),
      (∑ e ∈ ((Finset.univ : Finset
        (parityActualOriginalAFullBranchCarrier434 d L band slot)).image
          (parityActualOriginalAFullBranchE434 d L band slot)),
        sourceEndpointFibre
          (Finset.univ : Finset
            (parityActualOriginalAFullBranchCarrier434 d L band slot))
          (parityActualOriginalAFullBranchE434 d L band slot)
          (parityActualOriginalAFullBranchVWeight434 d L E u band slot ξ) e) *
            (Psi ((u:ℝ)/x) : ℂ) := by
  apply Finset.sum_congr rfl
  intro u hu
  have hu0 : u ≠ 0 := by
    have hpos := (Finset.mem_Icc.mp hu).1
    omega
  rw [parity_actual_original_A_full_source_to_e_v_sum434
    d L hL hd E u hu0 band slot ξ]
end Green64Analytic.Parity

end

end

/-! ## OriginalAZeroFourierMass -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000
set_option maxRecDepth 34000

/-- At zero original B509 frequencies the original full-slot phase is
literally one, for arbitrary labelled primes and assignment. -/
theorem parity_source_full_slot_phase_zero434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (s : Fin n → ℝ) (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i}) :
    paritySourceFullSlotFourierPhase434 s (fun _ => 0) δ p = 1 := by
  unfold paritySourceFullSlotFourierPhase434
  simp [sourceSlotFrequency]

/-- Identifies the actual ORIGINAL full labelled tuple's B590 branch
with the actual source weight times its buffered gate, at ξ=0. -/
theorem parity_actual_original_A_zero_freq_branch_exact434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → Bool)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    parityActualOriginalAFullBranchWeight434 d L E u band slot
      (fun _ => 0) (δ,f) =
    ((parityActualOriginalAFullTupleWeight434 d L u f *
      parityOriginalQAllocationBranchWeight434 20 E
        (sourceActualSortedFrequencyScales 20 d L band slot) δ
        (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) : ℝ) : ℂ) := by
  unfold parityActualOriginalAFullBranchWeight434
    parityActualOriginalAFullTupleWeight434
  dsimp only
  by_cases hGate : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
    sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · simp only [if_pos hGate]
    rw [parity_source_full_slot_phase_zero434]
    simp only [mul_one]
    push_cast
    ring
  · simp only [if_neg hGate]
    simp


/-- Every actual assignment at a fixed labelled Q tuple, with zero
Fourier frequency, sums to the original A tuple weight TIMES the true
B590 total buffer mass; there is no hidden normalization assumption. -/
theorem parity_actual_original_A_zero_freq_assignment_sum434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    (∑ δ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → Bool,
        parityActualOriginalAFullBranchWeight434 d L E u band slot
          (fun _ => 0) (δ,f)) =
    ((parityActualOriginalAFullTupleWeight434 d L u f *
      parityActualOriginalAFullTupleAllocationMass434 d L E band slot f : ℝ) : ℂ) := by
  simp_rw [parity_actual_original_A_zero_freq_branch_exact434]
  unfold parityActualOriginalAFullTupleAllocationMass434
  dsimp only
  push_cast
  rw [Finset.mul_sum]

/-- The WHOLE original complete-Q physical zero-frequency smooth
branch family has total mass equal to the exact original labelled
source coefficients weighted by the true buffered allocation mass.
This connects the two previously separate SOURCE objects. -/
theorem parity_actual_original_A_zero_freq_full_branch_mass_exact434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) :
    (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
      parityActualOriginalAFullBranchWeight434 d L E u band slot
        (fun _ => 0) z) =
      ((∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        parityActualOriginalAFullTupleWeight434 d L u f *
          parityActualOriginalAFullTupleAllocationMass434 d L E band slot f : ℝ) : ℂ) := by
  unfold parityActualOriginalAFullBranchCarrier434
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [parity_actual_original_A_zero_freq_assignment_sum434]
  push_cast
  rfl

/-- ACTUAL historical `sourceOriginalXA` is EXACTLY the zero-frequency
smoothed physical whole full-Q / B590 branch family PLUS the precise
unestimated original buffer-partition discrepancy. The u=0 endpoint,
all original P/Q labels, W1/parity, factorials, real Ψ, reserved prime
and complete true B590 gates remain. No partition-of-unity, Fourier
integration, or tail estimate is silently inserted. -/
theorem parity_actual_original_XA_eq_physical_zero_freq_plus_defect434
    (d : ℕ) (L E x : ℝ) (hL : 0 < L)
    (Psi : ℝ → ℝ)
    (band : Fin (d+1)) (slot : Fin 20) :
    ((sourceOriginalXA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) x Psi : ℝ) : ℂ) =
      (∑ u ∈ Finset.range (⌊2*x⌋₊+1),
        (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
          parityActualOriginalAFullBranchWeight434 d L E u band slot
            (fun _ => 0) z) * (Psi ((u:ℝ)/x) : ℂ)) +
      ((parityActualOriginalXAAllocationDefect434 d L E x Psi band slot : ℝ) : ℂ) := by
  rw [parity_actual_source_XA_eq_allocated_plus_exact_buffer_defect434
    d L E x hL Psi band slot]
  push_cast
  congr 1
  unfold parityActualOriginalXAWithAllocationMass434
  push_cast
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_actual_original_A_zero_freq_full_branch_mass_exact434]
  push_cast
  rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalXAToPhysicalEFibreWithDefect -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000
set_option maxRecDepth 34000

/-- The literal HISTORICAL original XA source is EXACTLY the original
full zero-Fourier B590/B509 allocated physical e-v fibre, retaining
all factorial, Q/P/parity, original Psi and finite u cutoff, PLUS the
explicit original f0/f1 buffered allocation defect. At u=0 we retain
its full original branch instead of illegally applying the u=e*v
lemma requiring u≠0. This is true without a source allocation partition
assumption or Type II estimate, but does NOT remove the defect or
identify the post-Fourier historical a_e(4.7). -/
theorem parity_actual_original_XA_physical_e_fibre_plus_buffer_defect434
    (d : ℕ) (L E x : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (Psi : ℝ → ℝ)
    (band : Fin (d+1)) (slot : Fin 20) :
    ((sourceOriginalXA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) x Psi : ℝ) : ℂ) =
      (∑ u ∈ Finset.range (⌊2*x⌋₊+1),
        (if u = 0 then
          (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
            parityActualOriginalAFullBranchWeight434 d L E u band slot
              (fun _ => 0) z)
        else
          (∑ e ∈ ((Finset.univ : Finset
            (parityActualOriginalAFullBranchCarrier434 d L band slot)).image
              (parityActualOriginalAFullBranchE434 d L band slot)),
            sourceEndpointFibre
              (Finset.univ : Finset
                (parityActualOriginalAFullBranchCarrier434 d L band slot))
              (parityActualOriginalAFullBranchE434 d L band slot)
              (parityActualOriginalAFullBranchVWeight434 d L E u band slot
                (fun _ => 0)) e)) *
          (Psi ((u:ℝ)/x) : ℂ)) +
      ((parityActualOriginalXAAllocationDefect434 d L E x Psi band slot : ℝ) : ℂ) := by
  rw [parity_actual_original_XA_eq_physical_zero_freq_plus_defect434
    d L E x hL Psi band slot]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hzero : u = 0
  · simp only [if_pos hzero]
  · simp only [if_neg hzero]
    rw [parity_actual_original_A_full_source_to_e_v_sum434
      d L hL hd E u hzero band slot (fun _ => 0)]


/-- For an ORIGINAL Parity cutoff with Ψ(0)=0 (in particular source Ψ
supported on [1,2]), the apparent u=0 exception vanishes exactly.
No dropped endpoint: zero has zero original Ψ-weight. The result is the
full original source XA = physical selected-e / v B590-B509 sum PLUS
explicit unestimated buffered-partition error, at ξ=0. -/
theorem parity_actual_original_XA_physical_e_fibre_all_u_plus_defect434
    (d : ℕ) (L E x : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (Psi : ℝ → ℝ) (hPsi0 : Psi 0 = 0)
    (band : Fin (d+1)) (slot : Fin 20) :
    ((sourceOriginalXA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) x Psi : ℝ) : ℂ) =
      (∑ u ∈ Finset.range (⌊2*x⌋₊+1),
        (∑ e ∈ ((Finset.univ : Finset
          (parityActualOriginalAFullBranchCarrier434 d L band slot)).image
            (parityActualOriginalAFullBranchE434 d L band slot)),
          sourceEndpointFibre
            (Finset.univ : Finset
              (parityActualOriginalAFullBranchCarrier434 d L band slot))
            (parityActualOriginalAFullBranchE434 d L band slot)
            (parityActualOriginalAFullBranchVWeight434 d L E u band slot
              (fun _ => 0)) e) *
        (Psi ((u:ℝ)/x) : ℂ)) +
      ((parityActualOriginalXAAllocationDefect434 d L E x Psi band slot : ℝ) : ℂ) := by
  rw [parity_actual_original_XA_physical_e_fibre_plus_buffer_defect434
    d L E x hL hd Psi band slot]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hzero : u = 0
  · subst u
    simp [hPsi0]
  · simp only [if_neg hzero]
end Green64Analytic.Parity

end

end

/-! ## OriginalXAPhysicalErrorBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000
set_option maxRecDepth 34000

/-- The ORIGINAL Parity Ψ support condition eliminates u=0, not merely a
convenient user-supplied pointwise Ψ(0)=0 hypothesis. -/
theorem parity_original_Psi_support_zero434
    (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2) :
    Psi 0 = 0 := by
  by_contra hne
  have h := hSupport (by simpa [Function.mem_support] using hne)
  norm_num at h

/-- The exact total original source-to-physical allocation discrepancy
is controlled by the TRUE historical factorial W1/P-parity absolute
mass and the TRUE original buffered f0/f1 partition defect, with
no invented partition unity, no Fourier tail assumed, and no missing
u=0 endpoint. This is a rigorous quantitative input to the missing
boundary-discard saving before Parity historical a_e(4.7). -/
theorem parity_actual_original_XA_to_physical_e_fibre_error_budget434
    (d : ℕ) (L E x : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (band : Fin (d+1)) (slot : Fin 20) :
    ‖((sourceOriginalXA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) x Psi : ℝ) : ℂ) -
      (∑ u ∈ Finset.range (⌊2*x⌋₊+1),
        (∑ e ∈ ((Finset.univ : Finset
          (parityActualOriginalAFullBranchCarrier434 d L band slot)).image
            (parityActualOriginalAFullBranchE434 d L band slot)),
          sourceEndpointFibre
            (Finset.univ : Finset
              (parityActualOriginalAFullBranchCarrier434 d L band slot))
            (parityActualOriginalAFullBranchE434 d L band slot)
            (parityActualOriginalAFullBranchVWeight434 d L E u band slot
              (fun _ => 0)) e) *
        (Psi ((u:ℝ)/x) : ℂ))‖ ≤
      ∑ u ∈ Finset.range (⌊2*x⌋₊+1),
        (∑ f : ((j : Fin (d+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
          |parityActualOriginalAFullTupleWeight434 d L u f| *
            |1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f|) *
          |Psi ((u:ℝ)/x)| := by
  have hPsi0 := parity_original_Psi_support_zero434 Psi hSupport
  have hA := parity_actual_original_XA_physical_e_fibre_all_u_plus_defect434
    d L E x hL hd Psi hPsi0 band slot
  rw [hA]
  simp only [add_sub_cancel_left]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    parity_actual_original_XA_buffer_allocation_absolute_majorant434
      d L E x Psi band slot
end Green64Analytic.Parity

end

end

/-! ## OriginalXABufferDefectPos -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Under the ORIGINAL Parity condition 0≤Ψ, the genuine original XA
B590 allocation defect is NONNEGATIVE, not merely bounded in modulus.
All real source W1/P-parity/factorial weights and the true full
history-dependent allocation subprobability are proved nonnegative. -/
theorem parity_actual_original_XA_allocation_defect_nonneg434
    (d : ℕ) (L E x : ℝ) (Psi : ℝ → ℝ)
    (hPsi : ∀ t, 0 ≤ Psi t)
    (band : Fin (d+1)) (slot : Fin 20) :
    0 ≤ parityActualOriginalXAAllocationDefect434 d L E x Psi band slot := by
  unfold parityActualOriginalXAAllocationDefect434
  apply Finset.sum_nonneg
  intro u hu
  apply mul_nonneg _ (hPsi _)
  apply Finset.sum_nonneg
  intro f hf
  exact mul_nonneg (parity_actual_original_A_full_tuple_weight_nonneg434 d L u f)
    (parity_actual_original_A_full_tuple_buffer_defect_nonneg434 d L E band slot f)

/-- The original positive Ψ source error is exactly the real
nonnegative allocation-defect mass and hence its Complex norm is the
same real number. No Cauchy loss or fake absolute-valued normalizer. -/
theorem parity_actual_original_XA_allocation_defect_complex_norm_exact434
    (d : ℕ) (L E x : ℝ) (Psi : ℝ → ℝ)
    (hPsi : ∀ t, 0 ≤ Psi t)
    (band : Fin (d+1)) (slot : Fin 20) :
    ‖((parityActualOriginalXAAllocationDefect434 d L E x Psi band slot : ℝ) : ℂ)‖ =
      parityActualOriginalXAAllocationDefect434 d L E x Psi band slot := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (parity_actual_original_XA_allocation_defect_nonneg434
    d L E x Psi hPsi band slot)
end Green64Analytic.Parity

end

end

/-! ## ActualOriginalReservedSortedQEquiv -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 35000

/-- EXACT source original labelled r20 Q-prime micro-assignment
bijection with the genuine reserved (band,slot) Q-prime and all
`sourceOrderedLabels` unreserved sorted Q-prime assignments. It is the
composition of the ORIGINAL `sourceOriginalQSlotsCurryEquiv`, the native
`Equiv.piSplitAt` at the original reserved slot and the ACTUAL
`sourceSortedLabelEquiv`; neither Q group nor mark is renamed. -/
noncomputable def parityActualOriginalReservedSortedQEquiv434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20) :
    ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) ≃
    ({q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length) →
          {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i})) := by
  let Q := sourceOriginalQActualBands 20 d L
  let s := sourceActualSortedScales 20 d L
  let e0 := (sourceOriginalQSlotsCurryEquiv 20 Q).symm
  let e1 := Equiv.piSplitAt (band,slot)
    (fun k : Fin (d+1) × Fin 20 => {q : ℕ // q ∈ Q k.1})
  let e2 := (Equiv.piCongrLeft
    (fun z : {z : Fin (d+1) × Fin 20 // z ≠ (band,slot)} =>
      {q : ℕ // q ∈ Q z.val.1})
    (sourceSortedLabelEquiv 20 s band slot)).symm
  exact e0.trans (e1.trans (Equiv.prodCongr (Equiv.refl _) e2))

/-- The reserve index component of that actual original source
bijection is the literal original reserved micro-Q prime. -/
theorem parity_actual_original_reserved_sorted_equiv_fst434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    (parityActualOriginalReservedSortedQEquiv434 d L band slot f).1 = f band slot := by
  rfl

/-- The unreserved component of the exact Q micro-assignment source
bijection is the ALREADY verified `parityActualSourceRemainingFullQTuple434`
and therefore the actual B509 sorted Q-prime carrier. -/
theorem parity_actual_original_reserved_sorted_equiv_rest434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    (parityActualOriginalReservedSortedQEquiv434 d L band slot f).2 =
      parityActualSourceRemainingFullQTuple434 d L band slot f := by
  rfl

/-- The literal full source Q prime product of ANY micro-assignment
is the product of the TWO components of that ACTUAL reserved+sorted
Q bijection. This is exactly the original Parity split of a single
reserved prime and all remaining Q primes, including multiplicities. -/
theorem parity_actual_original_reserved_sorted_equiv_product434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      (parityActualOriginalReservedSortedQEquiv434 d L band slot f).1.val *
      (∏ i, ((parityActualOriginalReservedSortedQEquiv434 d L band slot f).2 i).val) := by
  rw [parity_actual_original_reserved_sorted_equiv_fst434,
    parity_actual_original_reserved_sorted_equiv_rest434]
  exact parity_actual_source_fullQ_split_reserved_sorted_exact434 d L band slot f
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedSumGeneric -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- Source actual labelled Q-family is EQUINUMEROUS with its exact
reserved original prime × sorted unreserved Q prime tuple, preserving
all multiplicity labels. This small reusable lemma avoids unfolding
the whole original SourceOriginalA/Fourier arithmetic in the
expensive dependent `Fintype.sum_equiv` elaborator. -/
theorem parity_original_reserved_sum_generic434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (g : ({q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length) →
         {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i})) → ℂ) :
    (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
       g (parityActualOriginalReservedSortedQEquiv434 d L band slot f)) =
    ∑ x : ({q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length) →
         {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i})), g x := by
  exact Fintype.sum_equiv
    (parityActualOriginalReservedSortedQEquiv434 d L band slot)
    (fun f => g (parityActualOriginalReservedSortedQEquiv434 d L band slot f))
    g (by intro f; rfl)
end Green64Analytic.Parity

end

end

/-! ## ActualOriginalReservedSortedQSum -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 34000

/-- True ORIGINAL Q-prime all-label finite assignment sum reindexed
EXACTLY into a single reserved original prime q and ALL other Q
primes in their source `sourceOrderedLabels` order. The integrand is
an ARBITRARY function of the complete prime product, so this includes
the original literal SOURCE coefficient and all source physical
product gates. No factorial or repeated prime is added or removed. -/
theorem parity_actual_original_fullQ_reserved_sorted_sum_exact434
    {M : Type} [AddCommMonoid M]
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (F : ℕ → M) :
    (∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        F (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val)) =
      ∑ q : {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band},
        ∑ rest : ((i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length) →
          {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i}),
          F (q.val * ∏ i, (rest i).val) := by
  let E := parityActualOriginalReservedSortedQEquiv434 d L band slot
  calc
    (∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        F (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val)) =
      ∑ x : {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band} ×
        ((i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length) →
            {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i}),
        F (x.1.val * ∏ i, (x.2 i).val) := by
      apply Fintype.sum_equiv E
      intro f
      rw [parity_actual_original_reserved_sorted_equiv_product434]
    _ = _ := Fintype.sum_prod_type _
end Green64Analytic.Parity

end

end

/-! ## ActualOriginalAReservedSortedQ -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 32000

/-- True original source `sourceOriginalA`, with all its true Q bands,
marked 20! factorials, W1 and multiplicity parity, separated EXACTLY
at ANY original reserved Q slot into its literal prime q and all
remaining source `sourceOrderedLabels` Q primes. The only physical
gate is the exact arithmetic equality `q*prod(rest)=ordinaryPart(P,u)`.
There is no invented original a_e, no reweighted orbit or changes to
prime multiplicities. This is the genuine arithmetic input to the
historical reserved-prime `H(v_*)` in Parity(4.8). -/
theorem parity_actual_original_A_reserved_sorted_Q_exact434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (u : ℕ) (band : Fin (d+1)) (slot : Fin 20) :
    sourceOriginalA 20
      (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u =
    ∑ q : {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band},
      ∑ rest : ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length) →
          {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i}),
        if q.val * (∏ i, (rest i).val) =
          sourceOriginalOrdinaryPart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
          (∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)) *
            sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
            ((1-(-1:ℝ)^sourceOriginalPParityExponent
              (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)/2)
        else 0 := by
  let v := sourceOriginalOrdinaryPart
    (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  let w : ℝ :=
    (∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)) *
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      ((1-(-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)/2)
  let F : ℕ → ℝ := fun t => if t = v then w else 0
  rw [parity_actual_original_A_all_Q_labelled_exact434 d L hL u]
  change (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
      F (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val)) =
    ∑ q : {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band},
      ∑ rest : ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length) →
          {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i}),
        F (q.val * ∏ i, (rest i).val)
  exact parity_actual_original_fullQ_reserved_sorted_sum_exact434
    d L band slot F

/-- The full HISTORICAL original `sourceOriginalXA`, including its
actual cutoff `u<=floor(2x)`, true W1, P parity projection, Ψ and
all 20!/group normalization, has an EXACT arithmetic reserved-prime
× sorted remaining-Q double-sum at ANY real Q band/mark. This is the
source counterpart of Parity(4.8) BEFORE allocating remaining Q primes
to e and before Mellin/Fourier separation of physical v. -/
theorem parity_actual_original_XA_reserved_sorted_Q_exact434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (x : ℝ) (Psi : ℝ → ℝ)
    (band : Fin (d+1)) (slot : Fin 20) :
    sourceOriginalXA 20
      (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) x Psi =
    ∑ u ∈ Finset.range (⌊2*x⌋₊+1),
      ∑ q : {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band},
        ∑ rest : ((i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length) →
            {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i}),
          if q.val * (∏ i, (rest i).val) =
            sourceOriginalOrdinaryPart
              (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
            (∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)) *
              sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
              ((1-(-1:ℝ)^sourceOriginalPParityExponent
                (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)/2) *
              Psi ((u:ℝ)/x)
          else 0 := by
  unfold sourceOriginalXA
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_actual_original_A_reserved_sorted_Q_exact434 d L hL u band slot]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro rest hrest
  split_ifs <;> ring
end Green64Analytic.Parity

end

end

/-! ## ParamReservedBand -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- The ACTUAL original Parity §4.1 fixed reserved ordinary Q band j**
can be chosen for EVERY b_*>0 so that its entire closed prime window
has exponent at most b_*/4: (6/5)*Q0*2^-j** <= b_*/4.
No hardcoded 1/44 P-part cap or artificial fixed b_* is needed.
This is the true source original r=20 Q0 scale 5/(11*20). -/
theorem parity_original_reserved_Q_band_exists_for_beta434
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ jQ : ℕ,
      (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4 := by
  have hbeta4 : 0 < beta/4 := by positivity
  have hPow : Tendsto (fun j : ℕ => (2:ℝ)^j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨jQ,hjQ⟩ := (hPow.eventually_ge_atTop
    (((6/5:ℝ)*sourceOriginalQ0Scale 20)/(beta/4))).exists
  have hjPos : 0 < (2:ℝ)^jQ := by positivity
  have hUpper : (6/5:ℝ)*sourceOriginalQ0Scale 20 ≤
      (2:ℝ)^jQ*(beta/4) := by
    exact (div_le_iff₀ hbeta4).mp hjQ
  refine ⟨jQ,?_⟩
  unfold sourceOriginalQActualExponent
  calc
    (6/5:ℝ)*(sourceOriginalQ0Scale 20 / (2:ℝ)^jQ) =
        ((6/5:ℝ)*sourceOriginalQ0Scale 20) / (2:ℝ)^jQ := by ring
    _ ≤ beta/4 := (div_le_iff₀ hjPos).mpr (by nlinarith [hUpper])

/-- Every fixed original reserved Parity j** band eventually occurs within
the actual maximal moving source Q depth (not a replacement Q family). -/
theorem parity_eventually_original_reserved_Q_band_in_moving_depth434
    (jQ : ℕ) :
    ∀ᶠ L : ℝ in atTop, jQ ≤ sourceOriginalLiteralDepth 20 L := by
  filter_upwards [source_original_fixed_depth_admissible_eventually 20 jQ (by norm_num),
    source_original_literal_depth_properties_eventually 20 (by norm_num)]
    with L hAdmissible hDepth
  exact hDepth.2 jQ hAdmissible

/-- The actual reserved source prime q from an arbitrary original band
with the honest fixed-b_* band-selection inequality obeys
q <= exp((b_*/4)*L), with no loss from closed Q endpoints. -/
theorem parity_original_reserved_Q_prime_beta_exp_cap434
    (beta : ℝ) (d : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4)
    (q : ℕ) (hq : q ∈ sourceOriginalQActualBands 20 d L band) :
    (q:ℝ) ≤ Real.exp ((beta/4)*L) := by
  have hScale := source_original_Q_actual_scale_eq_P_scale 20 band.val L
    (by norm_num)
  have hMul := mul_le_mul_of_nonneg_right hBand hL
  have hBudget : (6/5:ℝ)*sourceOriginalPGroupScale 20 L band.val ≤
      (beta/4)*L := by
    calc
      _ = ((6/5:ℝ)*sourceOriginalQActualExponent 20 band.val)*L := by
        rw [←hScale]
        ring
      _ ≤ (beta/4)*L := hMul
  have hRange := (source_original_Q_actual_prime_range 20 d L
    (by norm_num) band q hq).2
  exact hRange.trans (Real.exp_le_exp.mpr hBudget)

/-- The LITERAL native source P carrier is parameterised by any
H=floor(exp(b_*L/4)); its members obey v<=exp(b_*L/4), with actual
prime-power multiplicities and no proxy small-P support. -/
theorem parity_original_physical_Ppart_beta_exp_cap434
    (beta L : ℝ) (v : ℕ)
    (hv : v ∈ sourceActualSortedPPartSupport 20 L
      ⌊Real.exp ((beta/4)*L)⌋₊) :
    (v:ℝ) ≤ Real.exp ((beta/4)*L) := by
  have hFloor := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).2
  have hCast : (v:ℝ) ≤ (⌊Real.exp ((beta/4)*L)⌋₊:ℝ) := by
    exact_mod_cast hFloor
  exact hCast.trans (Nat.floor_le (Real.exp_nonneg _))
end Green64Analytic.Parity

end

end

/-! ## ParamPhysicalQMass -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000
set_option maxRecDepth 30000

/-- Parity §4.1 physical total-Q-product budget for ARBITRARY real b_*>0,
not just the previously specialised 1/20. The reserved original Q
band satisfies its actual source b_*/4 exponent gate, and the native
B537 physical P-part is in its parameter-dependent retained carrier
`floor(exp((b_*/4)L))`. Therefore the two non-Q factors cost at most
`exp((b_*/2)L)` and any actual u>=exp L forces unreserved original
Q mass >= exp((1-b_*/2)L). No assumption on Q mass or e is made. -/
theorem parity_original_beta_physical_full_Qmass_lower434
    (beta : ℝ) (d : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4)
    (slot : Fin 20)
    (q : {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band})
    (p : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length) →
      {z : ℕ // z ∈ sourceActualSortedQ 20 d L band slot i})
    (v : ℕ)
    (hv : v ∈ sourceActualSortedPPartSupport 20 L
      ⌊Real.exp ((beta/4)*L)⌋₊)
    (hPhysical : Real.exp L ≤ ((q.val * (∏ i, (p i).val)*v : ℕ) : ℝ)) :
    Real.exp ((1-beta/2)*L) ≤ ((∏ i, (p i).val : ℕ) : ℝ) := by
  let Q := ∏ i, (p i).val
  have hqBound := parity_original_reserved_Q_prime_beta_exp_cap434
    beta d L hL band hBand q.val q.property
  have hvBound := parity_original_physical_Ppart_beta_exp_cap434 beta L v hv
  have hSmall : ((q.val:ℝ)*(v:ℝ)) ≤ Real.exp ((beta/2)*L) := by
    calc
      (q.val:ℝ)*(v:ℝ) ≤
          Real.exp ((beta/4)*L)*Real.exp ((beta/4)*L) := by gcongr
      _ = Real.exp ((beta/2)*L) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hCast : Real.exp L ≤ ((q.val:ℝ)*(Q:ℝ))*(v:ℝ) := by
    simpa only [Q,Nat.cast_mul] using hPhysical
  have hNonneg : 0 ≤ (Q:ℝ) := Nat.cast_nonneg Q
  have hCompare : Real.exp L ≤ (Q:ℝ)*Real.exp ((beta/2)*L) := by
    calc
      Real.exp L ≤ (Q:ℝ)*((q.val:ℝ)*(v:ℝ)) := by
        calc
          _ ≤ (q.val:ℝ)*(Q:ℝ)*(v:ℝ) := hCast
          _ = (Q:ℝ)*((q.val:ℝ)*(v:ℝ)) := by ring
      _ ≤ (Q:ℝ)*Real.exp ((beta/2)*L) :=
        mul_le_mul_of_nonneg_left hSmall hNonneg
  have hExp : Real.exp L =
      Real.exp ((1-beta/2)*L)*Real.exp ((beta/2)*L) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [hExp] at hCompare
  exact (mul_le_mul_iff_of_pos_right (Real.exp_pos _)).mp hCompare

/-- Original Type II range E<=exp((1-b_*)L) yields the whole original
nonreserved Q allocation mass automatically under actual Parity §4.1
b_*/4 P cap and sufficiently late reserved Q band. General b_*>0:
there is NO threshold b_*>=1/20 in this statement. -/
theorem parity_original_beta_physical_E_le_full_Qmass434
    (beta : ℝ) (hbeta : 0 < beta)
    (d : ℕ) (L : ℝ) (hL : 0 ≤ L) (E : ℝ)
    (hE : E ≤ Real.exp ((1-beta)*L))
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4)
    (slot : Fin 20)
    (q : {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band})
    (p : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length) →
      {z : ℕ // z ∈ sourceActualSortedQ 20 d L band slot i})
    (v : ℕ)
    (hv : v ∈ sourceActualSortedPPartSupport 20 L
      ⌊Real.exp ((beta/4)*L)⌋₊)
    (hPhysical : Real.exp L ≤ ((q.val * (∏ i, (p i).val)*v : ℕ) : ℝ)) :
    E ≤ ((∏ i, (p i).val : ℕ) : ℝ) := by
  have hQ := parity_original_beta_physical_full_Qmass_lower434
    beta d L hL band hBand slot q p v hv hPhysical
  have hbetaL : (1-beta)*L ≤ (1-beta/2)*L := by
    nlinarith [mul_nonneg (le_of_lt hbeta) hL]
  exact hE.trans ((Real.exp_le_exp.mpr hbetaL).trans hQ)
end Green64Analytic.Parity

end

end

/-! ## OriginalB590ActualSlotCount -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Exact count of original Q-prime f0/f1 transition slots after
reserving precisely ONE labelled Q prime: N=20(d+1)-1. This is about
the actual sourceOrderedLabels sorted list, not a convenient proxy n. -/
theorem parity_original_B590_actual_slot_count434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20) :
    (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length+1 =
      20*(d+1) := by
  unfold sourceOrderedLabels
  rw [List.length_mergeSort, Finset.length_toList]
  rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Finset.card_product, Fintype.card_prod]
  omega

/-- The genuine original admissibility (not an arbitrary depth)
implies the paper's bound d+1 ≤ 2 log L. -/
theorem parity_original_B590_admissible_depth_le_two_log434
    (d : ℕ) (L : ℝ) (hL : Real.exp 2 ≤ L)
    (hd : sourceOriginalDepthAdmissible 20 d L) :
    ((d+1:ℕ):ℝ) ≤ 2*Real.log L := by
  have hLp : 0 < L := (Real.exp_pos 2).trans_le hL
  have hlog : 2 ≤ Real.log L := by
    simpa using Real.log_le_log (Real.exp_pos 2) hL
  have hp : 0 < (2:ℝ)^d := by positivity
  have hcross : 20*Real.log L * (2:ℝ)^d ≤ (1/44:ℝ)*L := by
    dsimp [sourceOriginalDepthAdmissible] at hd
    norm_num at hd
    rw [div_mul_eq_mul_div] at hd
    exact (le_div_iff₀ hp).1 hd
  have hpow : (2:ℝ)^d ≤ L := by nlinarith [hcross]
  have hlogpow := Real.log_le_log hp hpow
  rw [Real.log_pow] at hlogpow
  have h2 : (2/3:ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hprod := mul_le_mul_of_nonneg_left h2 hd0
  push_cast
  nlinarith

/-- Actual number of complete original B590 Fourier integrations
N after reserving the original labelled band prime is ≤40 log L.
The actual largest admissible source depth is used, with no dependence
on the arbitrary later Type II splitting precision K0. -/
theorem parity_original_B590_actual_slot_count_log_bound434 :
    ∀ᶠ L : ℝ in atTop, ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1))
      (slot : Fin 20),
      (((sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length:ℕ):ℝ) ≤ 40*Real.log L := by
  filter_upwards [source_original_literal_depth_properties_eventually 20 (by norm_num),
    eventually_ge_atTop (Real.exp 2)] with L hDepth hL
  intro band slot
  let d := sourceOriginalLiteralDepth 20 L
  have hCount := parity_original_B590_actual_slot_count434 d L band slot
  have hDepthBound := parity_original_B590_admissible_depth_le_two_log434
    d L hL hDepth.1
  have hNat : (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length ≤ 20*(d+1) := by
    omega
  have hReal : (((sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length:ℕ):ℝ) ≤
      (20*(d+1):ℕ) := by exact_mod_cast hNat
  convert hReal.trans (show ((20*(d+1):ℕ):ℝ) ≤ 40*Real.log L by
    push_cast
    push_cast at hDepthBound
    nlinarith [hDepthBound]) using 1
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierPolynomial -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The FIXED original Fourier variation exponent, chosen from
real original f0/f1 Schwartz Fourier L1 mass rather than a symbol CF
later adjusted with the splitting accuracy K0. -/
def parityOriginalB590FixedFourierPolynomialExponent434 : ℝ :=
  40 * Real.log (2*parityOriginalB590FixedFourierL1Mass434)

/-- Simple exact analytic bridge from N≤40log L to polynomial
Fourier total variation, valid for any L≥1 and original CF≥1. -/
theorem parity_original_B590_fourier_power_to_polylog434
    (N : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hN : (N:ℝ) ≤ 40*Real.log L) :
    (2*parityOriginalB590FixedFourierL1Mass434)^N ≤
      L^parityOriginalB590FixedFourierPolynomialExponent434 := by
  let C : ℝ := 2*parityOriginalB590FixedFourierL1Mass434
  have hCF := parity_original_B590_fixed_fourier_L1_mass_ge_one434
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLog : 0 ≤ Real.log C := Real.log_nonneg hC
  have hScaled : Real.log C*(N:ℝ) ≤
      Real.log C*(40*Real.log L) :=
    mul_le_mul_of_nonneg_left hN hLog
  have hExp := Real.exp_le_exp.mpr hScaled
  rw [Real.rpow_def_of_pos hLp]
  have hNC : C^N = Real.exp (Real.log C * (N:ℝ)) := by
    rw [←Real.rpow_natCast, Real.rpow_def_of_pos hCp]
  change C^N ≤ Real.exp (Real.log L * parityOriginalB590FixedFourierPolynomialExponent434)
  rw [hNC]
  unfold parityOriginalB590FixedFourierPolynomialExponent434
  change Real.exp (Real.log C * (N:ℝ)) ≤
    Real.exp (Real.log L * (40*Real.log C))
  exact (by convert hExp using 1 <;> ring)

/-- ORIGINAL SOURCE Parity (4.6), true polynomial Fourier L1 TOTAL
VARIATION across every one of its N=20(d+1)-1 f0/f1 assignment
slots. The bound uses the actual largest admissible Q-band depth and
real Schwartz gates and is uniform in all later Type II split accuracy
K0, beta and reserved Q label. This proves the manuscript's finite
`(2CF)^N ≤ L^Cf` saving without inventing or changing CF after K0. -/
theorem parity_eventually_original_B590_actual_full_fourier_variation_polylog434 :
    ∀ᶠ L : ℝ in atTop,
    ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20),
      (∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool,
        parityOriginalB590FourierBranchVariation434 δ) ≤
      L^parityOriginalB590FixedFourierPolynomialExponent434 := by
  filter_upwards [parity_original_B590_actual_slot_count_log_bound434,
    eventually_ge_atTop (1:ℝ)] with L hCount hL
  intro band slot
  let N : ℕ := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
    band slot).length
  exact (parity_original_B590_fourier_total_variation_le434 N).trans
    (parity_original_B590_fourier_power_to_polylog434 N L hL (hCount band slot))
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierTailMoment -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- H-th ORIGINAL source B590 Fourier moment from the true C∞ compact
f0/f1 native Schwartz gate. No K0 or Fourier cutoff in the definition. -/
def parityOriginalB590GateFourierMoment434 (H : ℕ) (δ : Bool) : ℝ :=
  ∫ ξ : ℝ, |ξ|^H * ‖(𝓕 (sourceBufferedGate 20 δ) : 𝓢(ℝ,ℂ)) ξ‖

/-- Actual source B590 H-th Fourier moment is integrable for EVERY
fixed H. It is not merely a formal finite constant. -/
theorem parity_original_B590_gate_fourier_moment_integrable434
    (H : ℕ) (δ : Bool) :
    Integrable (fun ξ : ℝ =>
      |ξ|^H * ‖(𝓕 (sourceBufferedGate 20 δ) : 𝓢(ℝ,ℂ)) ξ‖) := by
  have h := (𝓕 (sourceBufferedGate 20 δ) : 𝓢(ℝ,ℂ)).integrable_pow_mul volume H
  simpa only [Real.norm_eq_abs] using h

/-- One original source gate has nonnegative H-th Fourier moment. -/
theorem parity_original_B590_gate_fourier_moment_nonneg434
    (H : ℕ) (δ : Bool) :
    0 ≤ parityOriginalB590GateFourierMoment434 H δ := by
  unfold parityOriginalB590GateFourierMoment434
  exact integral_nonneg (fun ξ => mul_nonneg (pow_nonneg (abs_nonneg ξ) _) (norm_nonneg _))

/-- Original source f0/f1 share ONE genuine finite fixed H-th Fourier
moment bound, independent of K0 and the moving number of slots. -/
def parityOriginalB590FixedFourierMoment434 (H : ℕ) : ℝ :=
  max 1 (max (parityOriginalB590GateFourierMoment434 H false)
    (parityOriginalB590GateFourierMoment434 H true))

theorem parity_original_B590_gate_moment_le_fixed434
    (H : ℕ) (δ : Bool) :
    parityOriginalB590GateFourierMoment434 H δ ≤
      parityOriginalB590FixedFourierMoment434 H := by
  unfold parityOriginalB590FixedFourierMoment434
  cases δ
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- Exact source Parity (4.6) single-coordinate Fourier tail, with the
original real frequency cutoff `|ξ|>T` and true H-th Schwartz moment.
The complement of [-T,T] is kept literal. No postulated Fourier
decay or missing factor T^-H. -/
theorem parity_original_B590_gate_fourier_tail_le_moment434
    (H : ℕ) (δ : Bool) (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (Set.Icc (-T) T)ᶜ,
      ‖(𝓕 (sourceBufferedGate 20 δ) : 𝓢(ℝ,ℂ)) ξ‖) ≤
      parityOriginalB590FixedFourierMoment434 H / T^H := by
  let f := (𝓕 (sourceBufferedGate 20 δ) : 𝓢(ℝ,ℂ))
  let S : Set ℝ := Set.Icc (-T) T
  have hS : MeasurableSet S := measurableSet_Icc
  have hw : Integrable (fun ξ : ℝ => ‖f ξ‖) := f.integrable.norm
  have hx : Integrable (fun ξ : ℝ => |ξ|^H * ‖f ξ‖) :=
    parity_original_B590_gate_fourier_moment_integrable434 H δ
  have hOutside : ∀ᵐ ξ ∂volume.restrict Sᶜ,
      T^H * ‖f ξ‖ ≤ |ξ|^H * ‖f ξ‖ := by
    filter_upwards [ae_restrict_mem hS.compl] with ξ hξ
    have hξT : T ≤ |ξ| := by
      by_contra h
      have ha : |ξ| < T := lt_of_not_ge h
      have hb := abs_lt.mp ha
      exact hξ ⟨hb.1.le,hb.2.le⟩
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hT.le hξT H) (norm_nonneg _)
  have hint := integral_mono_ae (hw.integrableOn.const_mul (T^H))
      hx.integrableOn hOutside
  rw [integral_const_mul] at hint
  have htotal :
      (∫ ξ in Sᶜ, |ξ|^H * ‖f ξ‖) ≤
      parityOriginalB590GateFourierMoment434 H δ :=
    setIntegral_le_integral hx
      (Filter.Eventually.of_forall
        (fun ξ => mul_nonneg (pow_nonneg (abs_nonneg ξ) H) (norm_nonneg _)))
  have hp : 0 < T^H := pow_pos hT _
  have hfirst : (∫ ξ in Sᶜ, ‖f ξ‖) ≤
      parityOriginalB590GateFourierMoment434 H δ / T^H :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hint.trans htotal)
  calc
    _ ≤ parityOriginalB590GateFourierMoment434 H δ / T^H := hfirst
    _ ≤ parityOriginalB590FixedFourierMoment434 H / T^H :=
      div_le_div_of_nonneg_right
        (parity_original_B590_gate_moment_le_fixed434 H δ) hp.le
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierTailUnion -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The true Parity (4.6) union-bound term with one SOURCE B590 Fourier
coordinate |ξ_i|>T and all other N-1 original Fourier frequencies
untruncated, for a given ordered allocation branch δ. -/
def parityOriginalB590OneCoordinateFourierTail434
    {N : ℕ} (δ : Fin N → Bool) (i : Fin N) (T : ℝ) : ℝ :=
  (∫ ξ in (Set.Icc (-T) T)ᶜ,
    ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ‖) *
  ∏ j ∈ (Finset.univ : Finset (Fin N)).erase i,
    (∫ ξ : ℝ,
      ‖(𝓕 (sourceBufferedGate 20 (δ j)) : 𝓢(ℝ,ℂ)) ξ‖)

/-- The precise original source one-coordinate tail bound of Parity
(4.6): the Schwartz H-th constant occurs ONCE, and every remaining
coordinate costs only the fixed SOURCE CF, not the H-dependent CH.
The factorial Q arithmetic is not being estimated here, only the
Fourier integration variation. -/
theorem parity_original_B590_one_coordinate_fourier_tail_bound434
    {N : ℕ} (δ : Fin N → Bool) (i : Fin N)
    (H : ℕ) (T : ℝ) (hT : 0 < T) :
    parityOriginalB590OneCoordinateFourierTail434 δ i T ≤
      (parityOriginalB590FixedFourierMoment434 H / T^H) *
        parityOriginalB590FixedFourierL1Mass434^(N-1) := by
  unfold parityOriginalB590OneCoordinateFourierTail434
  have hTail := parity_original_B590_gate_fourier_tail_le_moment434 H (δ i) T hT
  have hOther :
      (∏ j ∈ (Finset.univ : Finset (Fin N)).erase i,
        (∫ ξ : ℝ, ‖(𝓕 (sourceBufferedGate 20 (δ j)) : 𝓢(ℝ,ℂ)) ξ‖)) ≤
      parityOriginalB590FixedFourierL1Mass434^(N-1) := by
    calc
      _ ≤ ∏ _j ∈ (Finset.univ : Finset (Fin N)).erase i,
        parityOriginalB590FixedFourierL1Mass434 := by
          apply Finset.prod_le_prod₀
          · intro j hj
            exact integral_nonneg (fun ξ => norm_nonneg _)
          · intro j hj
            exact parity_original_B590_gate_fourier_norm_le_fixed_mass434 (δ j)
      _ = _ := by
        simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  have hFourierOther :
      0 ≤ (∏ j ∈ (Finset.univ : Finset (Fin N)).erase i,
        (∫ ξ : ℝ, ‖(𝓕 (sourceBufferedGate 20 (δ j)) : 𝓢(ℝ,ℂ)) ξ‖)) :=
    Finset.prod_nonneg (by intro j hj; exact integral_nonneg (fun ξ => norm_nonneg _))
  have hMoment : 0 ≤ parityOriginalB590FixedFourierMoment434 H/T^H := by
    unfold parityOriginalB590FixedFourierMoment434
    exact div_nonneg (le_trans (by norm_num) (le_max_left _ _)) (pow_pos hT _).le
  calc
    _ ≤ (parityOriginalB590FixedFourierMoment434 H/T^H) *
        (∏ j ∈ (Finset.univ : Finset (Fin N)).erase i,
          (∫ ξ : ℝ, ‖(𝓕 (sourceBufferedGate 20 (δ j)) : 𝓢(ℝ,ℂ)) ξ‖)) :=
            mul_le_mul_of_nonneg_right hTail hFourierOther
    _ ≤ (parityOriginalB590FixedFourierMoment434 H/T^H) *
        parityOriginalB590FixedFourierL1Mass434^(N-1) :=
          mul_le_mul_of_nonneg_left hOther hMoment

/-- The ORIGINAL source's exact (4.6) finite UNION BOUND, preserving
C_H ONCE per defective coordinate: 2^N*N*C_H*C_F^(N-1)*T^-H.
No `C_H^N` loss. The genuine Fourier f0/f1, actual N prime slots,
per-coordinate tail and 2^N allocations are used. This only bounds
frequency INTEGRATION MASS, not yet the original arithmetic source
bilinear integrand or its full multi-dimensional Fourier equality. -/
theorem parity_original_B590_all_assignments_fourier_tail_union434
    (N H : ℕ) (T : ℝ) (hT : 0 < T) :
    (∑ δ : Fin N → Bool, ∑ i : Fin N,
      parityOriginalB590OneCoordinateFourierTail434 δ i T) ≤
      ((2:ℝ)^N * (N:ℝ)) *
      (parityOriginalB590FixedFourierMoment434 H/T^H) *
        parityOriginalB590FixedFourierL1Mass434^(N-1) := by
  let C : ℝ := (parityOriginalB590FixedFourierMoment434 H/T^H)*
        parityOriginalB590FixedFourierL1Mass434^(N-1)
  have hSumSlot (δ : Fin N → Bool) :
      (∑ i : Fin N, parityOriginalB590OneCoordinateFourierTail434 δ i T) ≤
      (N:ℝ)*C := by
    calc
      _ ≤ ∑ _i : Fin N, C := by
        apply Finset.sum_le_sum
        intro i hi
        exact parity_original_B590_one_coordinate_fourier_tail_bound434 δ i H T hT
      _ = _ := by simp [C]
  calc
    _ ≤ ∑ _δ : Fin N → Bool, (N:ℝ)*C := by
      apply Finset.sum_le_sum
      intro δ hδ
      exact hSumSlot δ
    _ = ((2:ℝ)^N * (N:ℝ)) *
        (parityOriginalB590FixedFourierMoment434 H/T^H) *
          parityOriginalB590FixedFourierL1Mass434^(N-1) := by
      simp [C, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      ring
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierTailPolynomial -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- For the exact original N B590 Fourier slots, the source (4.6)
union tail is bounded by the fixed H-th Fourier moment CH times
N L^Cf / L^H as soon as the true original band count satisfies
N≤40 log L. No CH^N, no precision-dependent CF. -/
theorem parity_original_B590_fourier_tail_union_le_log_budget434
    (N H : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hN : (N:ℝ) ≤ 40*Real.log L) :
    (∑ δ : Fin N → Bool, ∑ i : Fin N,
      parityOriginalB590OneCoordinateFourierTail434 δ i L) ≤
      (N:ℝ) * parityOriginalB590FixedFourierMoment434 H *
        (L^parityOriginalB590FixedFourierPolynomialExponent434 / L^H) := by
  let CF := parityOriginalB590FixedFourierL1Mass434
  let CH := parityOriginalB590FixedFourierMoment434 H
  have hCF : 1 ≤ CF := parity_original_B590_fixed_fourier_L1_mass_ge_one434
  have hCH : 0 ≤ CH := by
    dsimp [CH,parityOriginalB590FixedFourierMoment434]
    exact (by norm_num : (0:ℝ)≤1).trans (le_max_left _ _)
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hD : 0 < L^H := pow_pos hLp H
  have hN0 : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hCFpow : 0 ≤ CF^(N-1) := pow_nonneg (le_trans (by norm_num) hCF) _
  have hCFpowLe : CF^(N-1) ≤ CF^N :=
    pow_le_pow_right₀ hCF (Nat.sub_le N 1)
  have hCHdiv : 0 ≤ CH / L^H := div_nonneg hCH hD.le
  have hCFprod : (2:ℝ)^N*CF^N = (2*CF)^N := by rw [mul_pow]
  have hTail := parity_original_B590_all_assignments_fourier_tail_union434 N H L hLp
  have hBase := parity_original_B590_fourier_power_to_polylog434 N L hL hN
  calc
    _ ≤ ((2:ℝ)^N*(N:ℝ))*(CH/L^H)*CF^(N-1) := hTail
    _ ≤ ((2:ℝ)^N*(N:ℝ))*(CH/L^H)*CF^N :=
      mul_le_mul_of_nonneg_left hCFpowLe
        (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hN0) hCHdiv)
    _ = (N:ℝ)*CH*((2*CF)^N/L^H) := by ring
    _ ≤ (N:ℝ)*CH*(L^parityOriginalB590FixedFourierPolynomialExponent434/L^H) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hBase hD.le) (mul_nonneg hN0 hCH)

/-- Original fixed CH and logarithmic band-count cost are polynomially
absorbed AFTER fixing H, for every sufficiently large L. -/
theorem parity_original_B590_fourier_tail_union_poly_absorption434
    (N H : ℕ) (L : ℝ)
    (hL : 1 ≤ L)
    (hN : (N:ℝ) ≤ 40*Real.log L)
    (hCH : 40*parityOriginalB590FixedFourierMoment434 H ≤ L) :
    (∑ δ : Fin N → Bool, ∑ i : Fin N,
      parityOriginalB590OneCoordinateFourierTail434 δ i L) ≤
      L^(parityOriginalB590FixedFourierPolynomialExponent434 + 2 - (H:ℝ)) := by
  let CFexp := parityOriginalB590FixedFourierPolynomialExponent434
  let CH := parityOriginalB590FixedFourierMoment434 H
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLog : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos hLp
    linarith
  have hN0 : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hCH0 : 0 ≤ CH := by
    dsimp [CH,parityOriginalB590FixedFourierMoment434]
    exact (by norm_num : (0:ℝ)≤1).trans (le_max_left _ _)
  have hNC : (N:ℝ)*CH ≤ L^2 := by
    have hnL : (N:ℝ) ≤ 40*L := hN.trans (by linarith)
    calc
      _ ≤ (40*L)*CH := mul_le_mul_of_nonneg_right hnL hCH0
      _ = L*(40*CH) := by ring
      _ ≤ L*L := mul_le_mul_of_nonneg_left hCH hLp.le
      _ = L^2 := by ring
  have hTail := parity_original_B590_fourier_tail_union_le_log_budget434 N H L hL hN
  have hDen : 0 ≤ L^CFexp/L^H := by
    exact div_nonneg (Real.rpow_nonneg hLp.le _) (pow_nonneg hLp.le _)
  have hS :
      (N:ℝ)*CH*(L^CFexp/L^H) ≤ L^2*(L^CFexp/L^H) :=
    mul_le_mul_of_nonneg_right hNC hDen
  have hPower : L^2*(L^CFexp/L^H) = L^(CFexp+2-(H:ℝ)) := by
    rw [div_eq_mul_inv, ←Real.rpow_natCast L 2,
      ←Real.rpow_natCast L H,
      ←Real.rpow_neg hLp.le,
      ←Real.rpow_add hLp, ←Real.rpow_add hLp]
    congr 1
    ring
  exact hTail.trans (hS.trans_eq hPower)
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierTailAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- SOURCE Parity (4.6) choice of Fourier tail precision, after the true
fixed source Schwartz L1 constant CF and the user's requested A.
The moment order H depends only on A and the fixed original gates,
not on L, K0, Q prime bands, reserved prime or allocation branch. -/
def parityOriginalB590FourierTailAccuracy434 (A : ℝ) : ℕ :=
  ⌈A+parityOriginalB590FixedFourierPolynomialExponent434+2⌉₊

/-- The SOURCE original moment order H above absorbs the polynomial
Fourier variation and O(N) union factor for EVERY requested A. -/
theorem parity_original_B590_fourier_tail_accuracy_suffices434 (A : ℝ) :
    parityOriginalB590FixedFourierPolynomialExponent434+2 -
      (parityOriginalB590FourierTailAccuracy434 A : ℝ) ≤ -A := by
  have h := Nat.le_ceil (A+parityOriginalB590FixedFourierPolynomialExponent434+2)
  unfold parityOriginalB590FourierTailAccuracy434
  linarith

/-- Complete SOURCE Parity (4.6) *finite-variation* Fourier tail saving
with actual r0=20, true N=20(jx+1)-1 sorted Q labels and all 2^N
original f0/f1 allocations, the literal fixed cutoff T=L and exact
H-th original Schwartz Fourier moment. For any requested real A, CH
is chosen ONCE after H, then L is sufficiently large. The result is
uniform in all original reserved Q positions and in later splitting
precision K0; no superpolynomial CH^N or illegal pointwise decay.
It bounds the Fourier integration measure's total omitted mass. The
exact multi-dimensional Fourier inversion of B590 arithmetic sum and
full historical Parity(4.7) a_e coefficient are still separate. -/
theorem parity_eventually_original_B590_actual_fourier_tail_all_log434
    (A : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20),
      let N : ℕ := (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length
      (∑ δ : Fin N → Bool, ∑ i : Fin N,
        parityOriginalB590OneCoordinateFourierTail434 δ i L) ≤ L^(-A) := by
  let H := parityOriginalB590FourierTailAccuracy434 A
  let CH := parityOriginalB590FixedFourierMoment434 H
  filter_upwards [parity_original_B590_actual_slot_count_log_bound434,
    eventually_ge_atTop (max 1 (40*CH))] with L hN hThreshold
  intro band slot
  dsimp only
  let N : ℕ := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
    band slot).length
  have hL : 1 ≤ L := (le_max_left _ _).trans hThreshold
  have hCH : 40*parityOriginalB590FixedFourierMoment434 H ≤ L := by
    exact (le_max_right _ _).trans hThreshold
  have hFinite := parity_original_B590_fourier_tail_union_poly_absorption434
    N H L hL (hN band slot) hCH
  exact hFinite.trans (Real.rpow_le_rpow_of_exponent_le hL
    (parity_original_B590_fourier_tail_accuracy_suffices434 A))
end Green64Analytic.Parity

end

end

/-! ## OriginalB590NestedFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- TRUE original B590 gate inverse-Fourier product, written as the
literal sequence of nested Lebesgue integrals over all the original
Q-prime allocation decision slots. The source f0/f1 are actual Schwartz
gates, and frequencies use Mathlib's `exp(2πi ξ t)` convention.
No artificial abstract gates, finite Fourier quadrature or parameter
substitution. This recursive object does not yet claim one product
measure/Fubini equivalence. -/
def parityOriginalB590NestedFourier434 :
    (N : ℕ) → (Fin N → Bool) → (Fin N → ℝ) → ℂ
  | 0, _, _ => 1
  | N+1, δ, t =>
      ∫ ξ : ℝ,
        ((𝓕 (sourceBufferedGate 20 (δ 0)) : 𝓢(ℝ,ℂ)) ξ *
          Complex.exp (((2*Real.pi*ξ*(t 0):ℝ):ℂ)*Complex.I)) *
        parityOriginalB590NestedFourier434 N (Fin.tail δ) (fun i => t i.succ)

/-- Inverting EVERY TRUE source-original B590 f0/f1 gate by induction
on the exact number N of Q decision slots: its nested Fourier integral
is the FULL product of the actual `sourceBufferedGateReal 20` values.
Unlike evaluating all Fourier phases at ξ=0, this integrates EVERY
frequency, one per Q slot. No independence of Q arithmetic is used.
This is the exact scalar multi-gate Fourier inversion before the
product-measure Fubini and historical a_e coefficient extraction. -/
theorem parity_original_B590_nested_fourier_inverts_all_gates434
    (N : ℕ) : ∀ (δ : Fin N → Bool) (t : Fin N → ℝ),
    parityOriginalB590NestedFourier434 N δ t =
      ((∏ i : Fin N, sourceBufferedGateReal 20 (δ i) (t i) : ℝ) : ℂ) := by
  induction N with
  | zero =>
      intro δ t
      simp [parityOriginalB590NestedFourier434]
  | succ N ih =>
      intro δ t
      have htail := ih (Fin.tail δ) (fun i => t i.succ)
      have hGate := parity_original_source_B590_single_gate_fourier_inversion434
        20 (δ 0) (t 0)
      simp only [parityOriginalB590NestedFourier434]
      rw [htail]
      rw [integral_mul_const]
      have hIntegral :
        (∫ ξ : ℝ, (𝓕 (sourceBufferedGate 20 (δ 0)) : 𝓢(ℝ,ℂ)) ξ *
          Complex.exp (((2*Real.pi*ξ*(t 0):ℝ):ℂ)*Complex.I)) =
        ((sourceBufferedGateReal 20 (δ 0) (t 0):ℝ):ℂ) := by
        calc
          _ = ∫ ξ : ℝ,
            Complex.exp (((2*Real.pi*ξ*(t 0):ℝ):ℂ)*Complex.I) *
              (𝓕 (sourceBufferedGate 20 (δ 0)) : 𝓢(ℝ,ℂ)) ξ := by
                apply integral_congr_ae
                filter_upwards [] with ξ
                ring
          _ = _ := hGate.symm
      rw [hIntegral]
      rw [Fin.prod_univ_succ]
      push_cast
      simp only [Fin.tail_def]

/-- The literal original Q-allocation f0/f1 weight from the actual
source is its TRUE nested multi-slot Fourier integral. The residual
`R_i` is history-dependent and includes precisely the ORIGINAL
prime powers and chosen/skipped allocations, not a proxy phase. -/
theorem parity_original_actual_Q_B590_branch_weight_nested_fourier_exact434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ)
    (δ : Fin N → Bool) (p : Fin N → ℕ) :
    (parityOriginalQAllocationBranchWeight434 20 E s δ p : ℂ) =
      parityOriginalB590NestedFourier434 N δ
        (fun i => (parityOriginalQAllocationResidual434 E δ p i -
          Real.log (p i:ℝ))/s i) := by
  rw [parity_original_B590_nested_fourier_inverts_all_gates434]
  unfold parityOriginalQAllocationBranchWeight434
  push_cast
  rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalB590ActualNestedAllocation -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- The ENTIRE actual original Q-labelled full-tuple B590 allocation
mass, summing over ALL 2^N labelled allocation assignments with true
history-dependent prime residuals, is EXACTLY a finite sum of genuine
N-fold NESTED inverse Fourier integrals of the ACTUAL source f0/f1.
There is no Fourier ξ=0 evaluation or artificial gate factorization.
This statement is on the original sorted Q tuple with reserved prime,
not just on an abstract source gate sequence. -/
theorem parity_original_actual_fullQ_B590_mass_eq_nested_fourier_sum434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    ((parityActualOriginalAFullTupleAllocationMass434 d L E band slot f : ℝ) : ℂ) =
      ∑ δ : Fin (sourceOrderedLabels 20
         (sourceActualSortedScales 20 d L) band slot).length → Bool,
        parityOriginalB590NestedFourier434
          (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
          δ (fun i =>
            (parityOriginalQAllocationResidual434 E δ
              (fun j => (parityActualSourceRemainingFullQTuple434 d L band slot f j).val) i -
              Real.log ((parityActualSourceRemainingFullQTuple434 d L band slot f i).val:ℝ)) /
            sourceActualSortedFrequencyScales 20 d L band slot i) := by
  unfold parityActualOriginalAFullTupleAllocationMass434
  push_cast
  apply Finset.sum_congr rfl
  intro δ hδ
  exact parity_original_actual_Q_B590_branch_weight_nested_fourier_exact434
    E (sourceActualSortedFrequencyScales 20 d L band slot) δ
    (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val)

/-- On the ORIGINAL physically retained full-Q product support, the
actual full source δ-sum of nested Fourier integrals is exactly ONE.
This combines source original B590 allocation normalization with the
real N-slot Fourier inversion at every ordered Q prime slot. No
multidimensional product-measure Fubini is silently used. -/
theorem parity_original_actual_fullQ_retained_nested_fourier_mass_one434
    (d : ℕ) (L E : ℝ) (hL : 0 < L) (hE : 1 ≤ E)
    (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (hFull : E ≤ ((∏ i,
      (parityActualSourceRemainingFullQTuple434 d L band slot f i).val : ℕ) : ℝ)) :
    (∑ δ : Fin (sourceOrderedLabels 20
         (sourceActualSortedScales 20 d L) band slot).length → Bool,
        parityOriginalB590NestedFourier434
          (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
          δ (fun i =>
            (parityOriginalQAllocationResidual434 E δ
              (fun j => (parityActualSourceRemainingFullQTuple434 d L band slot f j).val) i -
              Real.log ((parityActualSourceRemainingFullQTuple434 d L band slot f i).val:ℝ)) /
            sourceActualSortedFrequencyScales 20 d L band slot i)) = 1 := by
  rw [← parity_original_actual_fullQ_B590_mass_eq_nested_fourier_sum434]
  rw [parity_original_actual_fullQ_B590_all_assignments_mass_one434
    d L E hL hE band slot f hFull]
  norm_num
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierIntegrand -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Exact real Fourier phase convention between the TRUE B590 source
Schwartz inverse transform and original B509 `Real.fourierChar` in the
Circle→ℂ embedding. This has NO spurious 2π discrepancy. -/
theorem parity_original_B590_inverse_fourier_phase_eq_source_char434 (u : ℝ) :
    Complex.exp (((2*Real.pi*u:ℝ):ℂ)*Complex.I) =
      ((Real.fourierChar u : Circle) : ℂ) := by
  change Complex.exp (((2*Real.pi*u:ℝ):ℂ)*Complex.I) =
    ((Circle.exp (2*Real.pi*u) : Circle) : ℂ)
  rw [Circle.coe_exp]

/-- Complete scalar true ORIGINAL gate product Fourier integrand on
ALL ordered Q slots, with every source buffered f0/f1 transform and
history-dependent logarithmic residual appearing literally. -/
def parityOriginalB590AllGateFourierIntegrand434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ)
    (δ : Fin N → Bool) (p : Fin N → ℕ) (ξ : Fin N → ℝ) : ℂ :=
  ∏ i : Fin N,
    ((𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i) *
      Complex.exp (((2*Real.pi*(ξ i / s i) *
        (parityOriginalQAllocationResidual434 E δ p i -
          Real.log (p i : ℝ)):ℝ):ℂ)*Complex.I))

/-- EXACT complete SOURCE Parity §4.2 (4.7) Fourier integrand algebra:
true product of original f0/f1 Fourier transforms, the unchanged
global frequency factor `log E * sum_i ξ_i/s_i`, and the genuine
B509 full selected/skipped Q-prime source Fourier phase. Includes the
correct `Real.fourierChar` convention: the inverse-gate exponents are
`2πi ξ_i*t_i`, not evaluated at zero. No Fourier integration, no
pre-integrated a_e coefficient or tail saving is asserted here. -/
theorem parity_original_B590_all_gate_integrand_exact434
    {N : ℕ} {Q : Fin N → Finset ℕ}
    (E : ℝ) (s ξ : Fin N → ℝ)
    (δ : Fin N → Bool)
    (p : (i : Fin N) → {q : ℕ // q ∈ Q i}) :
    parityOriginalB590AllGateFourierIntegrand434 E s δ
      (fun i => (p i).val) ξ =
    (∏ i : Fin N,
      (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
    ((Real.fourierChar
      (Real.log E * (∑ i : Fin N, ξ i / s i)) : Circle) : ℂ) *
      paritySourceFullSlotFourierPhase434 s ξ δ p := by
  unfold parityOriginalB590AllGateFourierIntegrand434
  rw [Finset.prod_mul_distrib]
  have hPhase :
      (∏ i : Fin N,
        Complex.exp (((2*Real.pi*(ξ i / s i) *
          (parityOriginalQAllocationResidual434 E δ
            (fun j => (p j).val) i - Real.log ((p i).val : ℝ)):ℝ):ℂ)*Complex.I)) =
      ((Real.fourierChar
        (∑ i : Fin N, (ξ i / s i) *
          (parityOriginalQAllocationResidual434 E δ
            (fun j => (p j).val) i - Real.log ((p i).val : ℝ))) : Circle) : ℂ) := by
    calc
      _ = ∏ i : Fin N,
        ((Real.fourierChar
          ((ξ i / s i) *
            (parityOriginalQAllocationResidual434 E δ
              (fun j => (p j).val) i - Real.log ((p i).val : ℝ))) : Circle) : ℂ) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hArg : 2*Real.pi*(ξ i / s i) *
              (parityOriginalQAllocationResidual434 E δ
                (fun j => (p j).val) i - Real.log ((p i).val : ℝ)) =
              2*Real.pi*((ξ i / s i) *
              (parityOriginalQAllocationResidual434 E δ
                (fun j => (p j).val) i - Real.log ((p i).val : ℝ))) := by ring
          rw [hArg]
          exact parity_original_B590_inverse_fourier_phase_eq_source_char434
            ((ξ i / s i) *
              (parityOriginalQAllocationResidual434 E δ
                (fun j => (p j).val) i - Real.log ((p i).val : ℝ)))
      _ = _ := (parity_source_fourierChar_finset_sum_to_complex_prod434
        (Finset.univ : Finset (Fin N))
        (fun i => (ξ i / s i) *
          (parityOriginalQAllocationResidual434 E δ
            (fun j => (p j).val) i - Real.log ((p i).val : ℝ)))).symm
  rw [hPhase, parity_original_smooth_gate_fourier_character_exact434]
  ring

/-- The original fully separated source (4.7) integrand retains the
same fixed e-selected gate phases and the true B509 ordered QSkip
phase on v, with source W1/parity not yet folded into H(v*). -/
theorem parity_original_B590_all_gate_integrand_selected_skipped434
    {N : ℕ} {Q : Fin N → Finset ℕ}
    (E : ℝ) (s ξ : Fin N → ℝ)
    (δ : Fin N → Bool)
    (p : (i : Fin N) → {q : ℕ // q ∈ Q i}) :
    parityOriginalB590AllGateFourierIntegrand434 E s δ
      (fun i => (p i).val) ξ =
    (∏ i : Fin N,
      (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
    ((Real.fourierChar
      (Real.log E * (∑ i : Fin N, ξ i / s i)) : Circle) : ℂ) *
    paritySourceAllocatedSlotFourierPhase434 s ξ δ p *
    orderedSkipPhase (δ := δ) s ξ
      (fun i : {i : Fin N // ¬δ i = true} => p i.val) := by
  rw [parity_original_B590_all_gate_integrand_exact434,
    parity_source_full_slot_fourier_phase_split434]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalActualFourierIntegrand -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The ORIGINAL 20!-labelled complete-Q real Parity source Fourier
integrand, with its true reserved Q-prime slot, actual sorted
Q frequency scales, original E and true f0/f1 Schwartz transforms.
This is a per-full-Q-tuple and per-δ integrand, not a post-ξ-integral
historical a_e(e) coefficient. -/
def parityOriginalActualQTupleFourierIntegrand434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  parityOriginalB590AllGateFourierIntegrand434 E
    (sourceActualSortedFrequencyScales 20 d L band slot) δ
    (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) ξ

/-- Per TRUE full original Q tuple (including its reserved source Q
prime), EVERY Fourier factor in Parity (4.7) separates exactly: original
Schwartz f0/f1 transforms, the common `log E` character, and the
literal selected-Q/ordered-QSkip Fourier phase on original e and v.
The actual source Q-prime subtype, sorted slot lengths, Fourier
sign, frequency normalization and all Q-prime repeats are kept.
No Fourier integration or coefficient support truncation is assumed. -/
theorem parity_original_actual_Q_tuple_integrand_selected_skipped434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    parityOriginalActualQTupleFourierIntegrand434 d L E band slot f δ ξ =
    (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
    ((Real.fourierChar
      (Real.log E * (∑ i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length,
        ξ i / sourceActualSortedFrequencyScales 20 d L band slot i)) : Circle) : ℂ) *
    paritySourceAllocatedSlotFourierPhase434
      (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ
      (parityActualSourceRemainingFullQTuple434 d L band slot f) *
    orderedSkipPhase (δ := δ)
      (sourceActualSortedFrequencyScales 20 d L band slot) ξ
      (fun i => parityActualSourceRemainingFullQTuple434 d L band slot f i.val) := by
  unfold parityOriginalActualQTupleFourierIntegrand434
  exact parity_original_B590_all_gate_integrand_selected_skipped434
    E (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ
    (parityActualSourceRemainingFullQTuple434 d L band slot f)

/-- The full original factorial labelled Q tuple integral density,
summed over ALL f0/f1 allocations, also has exact source selected/
skipped Fourier phase separation at each actual fixed frequency ξ.
This is the finite source integrand stage of Parity (4.7), retaining all
2^N δ assignments and real f0/f1 transforms. -/
theorem parity_original_actual_Q_tuple_all_assignments_integrand_split434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    (∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
      parityOriginalActualQTupleFourierIntegrand434 d L E band slot f δ ξ) =
    ∑ δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      (∏ i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length,
        (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
      ((Real.fourierChar
        (Real.log E * (∑ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length,
          ξ i / sourceActualSortedFrequencyScales 20 d L band slot i)) : Circle) : ℂ) *
      paritySourceAllocatedSlotFourierPhase434
        (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ
        (parityActualSourceRemainingFullQTuple434 d L band slot f) *
      orderedSkipPhase (δ := δ)
        (sourceActualSortedFrequencyScales 20 d L band slot) ξ
        (fun i => parityActualSourceRemainingFullQTuple434 d L band slot f i.val) := by
  apply Finset.sum_congr rfl
  intro δ hδ
  exact parity_original_actual_Q_tuple_integrand_selected_skipped434
    d L E band slot f δ ξ
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierIntegrandNorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- The GENUINE original B590/Parity(4.7) Fourier integrand has exactly
the product of the true source Schwartz Fourier gate norms. All
history-dependent allocation residual exponentials are unitary,
including reserved-Q and repeated source factors. No hidden growth
from E, Q primes, splitting parameter K0 or 2π normalization. -/
theorem parity_original_B590_all_gate_integrand_norm_exact434
    {N : ℕ} (E : ℝ) (s ξ : Fin N → ℝ)
    (δ : Fin N → Bool) (p : Fin N → ℕ) :
    ‖parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ‖ =
      ∏ i : Fin N,
        ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖ := by
  unfold parityOriginalB590AllGateFourierIntegrand434
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [norm_mul]
  have h :
    ‖Complex.exp (((2*Real.pi*(ξ i / s i) *
      (parityOriginalQAllocationResidual434 E δ p i -
        Real.log (p i : ℝ)):ℝ):ℂ)*Complex.I)‖ = 1 := by
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h,mul_one]

/-- The TRUE original full labelled Q prime source Fourier integrand
also inherits this exact pointwise modulus; no coefficient in the
selected/skipped Q product changes the Fourier cutoff budget. -/
theorem parity_original_actual_Q_tuple_integrand_norm_exact434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    ‖parityOriginalActualQTupleFourierIntegrand434 d L E band slot f δ ξ‖ =
      ∏ i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length,
        ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖ := by
  unfold parityOriginalActualQTupleFourierIntegrand434
  exact parity_original_B590_all_gate_integrand_norm_exact434 E
    (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ
    (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val)
end Green64Analytic.Parity

end

end

/-! ## OriginalB590Fourier46Audit -/

section

/- Parity rev64 original B590 f0/f1 exact source N=20(d+1)-1 and 2^N Fourier L1 variation, H-moment tail (4.6), arbitrarily small total Fourier frequency truncation at |xi|>L, nested all-gate inverse Fourier and exact Parity (4.7) integrand selected/skip phase algebra. Native kernel import audit, not full multi-dimensional Fourier Fubini or historical a_e/E4.1. -/
open Green64Analytic.Parity

end

/-! ## OriginalB590FullFourierFubini -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The TRUE original B590 h=-2 scalar source gate integrand for one
ordered Q-prime slot i, retaining the previous-δ dependent residual
`R_i`, the true 20-slot source f0/f1 Fourier Schwartz transform and
frequency scaling s_i. -/
def parityOriginalB590SingleGateFourierIntegrand434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ)
    (δ : Fin N → Bool) (p : Fin N → ℕ)
    (i : Fin N) (ξ : ℝ) : ℂ :=
  (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ *
    Complex.exp (((2*Real.pi*(ξ/s i) *
      (parityOriginalQAllocationResidual434 E δ p i -
        Real.log (p i : ℝ)):ℝ):ℂ)*Complex.I)

/-- At each ORIGINAL history-dependent Q slot the full source Fourier
integrand is genuinely integrable: Schwartz transform times a unit
real-frequency exponential. This holds for arbitrary original E,s,p,δ
and does NOT assume the full Q branch weight is positive. -/
theorem parity_original_B590_single_gate_fourier_integrable434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ)
    (δ : Fin N → Bool) (p : Fin N → ℕ)
    (i : Fin N) :
    Integrable (parityOriginalB590SingleGateFourierIntegrand434 E s δ p i) := by
  let f := (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ))
  have hC : Continuous (parityOriginalB590SingleGateFourierIntegrand434 E s δ p i) := by
    unfold parityOriginalB590SingleGateFourierIntegrand434
    fun_prop
  apply f.integrable.mono hC.aestronglyMeasurable
  filter_upwards [] with ξ
  unfold parityOriginalB590SingleGateFourierIntegrand434
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- One coordinate of the TRUE original B590 Fourier integrand has
the exact source inverse-gate integral. No illegal Q-slot
independence: all Q/δ/p history stays FIXED during integration over ξ_i.
The original 2π normalization is explicit and verified. -/
theorem parity_original_B590_single_gate_integral_equals_real_gate434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ)
    (δ : Fin N → Bool) (p : Fin N → ℕ)
    (i : Fin N) :
    (∫ ξ : ℝ, parityOriginalB590SingleGateFourierIntegrand434 E s δ p i ξ) =
      ((sourceBufferedGateReal 20 (δ i)
        ((parityOriginalQAllocationResidual434 E δ p i -
          Real.log (p i:ℝ))/s i):ℝ):ℂ) := by
  let t := (parityOriginalQAllocationResidual434 E δ p i -
    Real.log (p i:ℝ))/s i
  have hGate := parity_original_source_B590_single_gate_fourier_inversion434
    20 (δ i) t
  calc
    (∫ ξ : ℝ, parityOriginalB590SingleGateFourierIntegrand434 E s δ p i ξ) =
      ∫ ξ : ℝ,
        Complex.exp (((2*Real.pi*ξ*t:ℝ):ℂ)*Complex.I) *
          (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ := by
            apply integral_congr_ae
            filter_upwards [] with ξ
            unfold parityOriginalB590SingleGateFourierIntegrand434
            have ht : 2*Real.pi*(ξ/s i) *
                (parityOriginalQAllocationResidual434 E δ p i - Real.log (p i:ℝ)) =
              2*Real.pi*ξ*t := by
                dsimp [t]
                ring
            rw [ht]
            ring
    _ = _ := hGate.symm

/-- The FULL original N-dimensional B590 Fourier integrand is
integrable with respect to the TRUE product Lebesgue measure on
`Fin N→ℝ`, using Mathlib's verified finite-product Schwartz theorem.
Original R_i depends on preceding δ primes but is fixed during the
Fourier integration, exactly as in Parity §4.2. -/
theorem parity_original_B590_all_gate_fourier_product_integrable434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ)
    (δ : Fin N → Bool) (p : Fin N → ℕ) :
    Integrable (parityOriginalB590AllGateFourierIntegrand434 E s δ p) := by
  have h : Integrable (fun ξ : Fin N → ℝ =>
      ∏ i : Fin N,
        parityOriginalB590SingleGateFourierIntegrand434 E s δ p i (ξ i)) :=
    Integrable.fin_nat_prod (fun i =>
      parity_original_B590_single_gate_fourier_integrable434 E s δ p i)
  exact h

/-- ORIGINAL Parity (4.7) MULTIDIMENSIONAL f0/f1 Fourier inversion:
the source product of N history-dependent B590 gates is EXACTLY the
integral of the true N-dimensional Fourier integrand over
`Fin N→ℝ`, with actual product Lebesgue measure, not merely a nested
formal integral or the Fourier-ξ=0 evaluation. The finite-product
Fubini lemma `integral_fin_nat_prod_volume_eq_prod` is used with
independently kernel-proved integrability of all original gates.
This result preserves source real Schwartz f0/f1 and 2π convention;
source a_e/H(v*) factorisation and Fourier cutoff error still separate. -/
theorem parity_original_B590_all_gate_full_fourier_integral_exact434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ)
    (δ : Fin N → Bool) (p : Fin N → ℕ) :
    (∫ ξ : Fin N → ℝ,
      parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ) =
    ((parityOriginalQAllocationBranchWeight434 20 E s δ p : ℝ) : ℂ) := by
  unfold parityOriginalB590AllGateFourierIntegrand434
  change (∫ ξ : Fin N → ℝ,
      ∏ i : Fin N, parityOriginalB590SingleGateFourierIntegrand434
        E s δ p i (ξ i)) = _
  rw [MeasureTheory.integral_fin_nat_prod_volume_eq_prod]
  unfold parityOriginalQAllocationBranchWeight434
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  exact parity_original_B590_single_gate_integral_equals_real_gate434 E s δ p i
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierBoxProduct -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Exact ORIGINAL one-coordinate truncated f0/f1 Fourier inversion
on source frequency window [-T,T]. This retains the complex oscillating
source phase, not the modulus or the erroneous ξ=0 value. -/
def parityOriginalB590SingleGateFourierBox434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ) (δ : Fin N → Bool)
    (p : Fin N → ℕ) (i : Fin N) (T : ℝ) : ℂ :=
  ∫ ξ in Set.Icc (-T) T,
    parityOriginalB590SingleGateFourierIntegrand434 E s δ p i ξ

/-- TRUE source original N-dimensional truncated Fourier integral,
with independent fixed windows [-T,T] on all original Q frequencies.
This integral is with respect to the product of restricted Lebesgue
measures. It is not a finite Fourier quadrature or evaluation ξ=0. -/
def parityOriginalB590AllGateFourierBox434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ) (δ : Fin N → Bool)
    (p : Fin N → ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin N → ℝ,
    parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ
      ∂(Measure.pi (fun _ : Fin N => (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- The literal original truncated N-dimensional Fourier integral
factors EXACTLY into the product of its one-dimensional truncated
source f0/f1 Fourier integrals, with no error or fake independence of
Q allocation arithmetic: the latter is fixed in δ,p during integration. -/
theorem parity_original_B590_all_gate_fourier_box_eq_product434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ) (δ : Fin N → Bool)
    (p : Fin N → ℕ) (T : ℝ) :
    parityOriginalB590AllGateFourierBox434 E s δ p T =
      ∏ i : Fin N, parityOriginalB590SingleGateFourierBox434 E s δ p i T := by
  unfold parityOriginalB590AllGateFourierBox434
  unfold parityOriginalB590AllGateFourierIntegrand434
  change (∫ ξ : Fin N → ℝ,
      ∏ i : Fin N, parityOriginalB590SingleGateFourierIntegrand434
        E s δ p i (ξ i)
      ∂(Measure.pi (fun _ : Fin N => (volume : Measure ℝ).restrict (Set.Icc (-T) T)))) = _
  rw [MeasureTheory.integral_fin_nat_prod_eq_prod]
  rfl

/-- Each original truncated source f0/f1 inverse Fourier coordinate
has modulus bounded by its *full* native Fourier L1 mass, without
assuming a positive gate/branch or any Q geometry. -/
theorem parity_original_B590_single_gate_fourier_box_norm_le_L1434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ) (δ : Fin N → Bool)
    (p : Fin N → ℕ) (i : Fin N) (T : ℝ) :
    ‖parityOriginalB590SingleGateFourierBox434 E s δ p i T‖ ≤
      ∫ ξ : ℝ,
        ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ‖ := by
  unfold parityOriginalB590SingleGateFourierBox434
  calc
    _ ≤ ∫ ξ in Set.Icc (-T) T,
      ‖parityOriginalB590SingleGateFourierIntegrand434 E s δ p i ξ‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ ξ in Set.Icc (-T) T,
      ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ‖ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro ξ hξ
      unfold parityOriginalB590SingleGateFourierIntegrand434
      change ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ *
        Complex.exp (((2*Real.pi*(ξ/s i) *
          (parityOriginalQAllocationResidual434 E δ p i -
          Real.log (p i:ℝ)):ℝ):ℂ)*Complex.I)‖ =
        ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ‖
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    _ ≤ _ := setIntegral_le_integral
      ((𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)).integrable.norm)
      (Filter.Eventually.of_forall (fun ξ => norm_nonneg _))

/-- The original full-minus-box single gate Fourier amplitude is
bounded by the TRUE Schwartz L1 mass outside the literal window
[-T,T]. The equality of full and box plus complement requires the
proved original gate integrability, not a formal integral identity. -/
theorem parity_original_B590_single_gate_fourier_full_sub_box_norm_le_tail434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ) (δ : Fin N → Bool)
    (p : Fin N → ℕ) (i : Fin N) (T : ℝ) :
    ‖(∫ ξ : ℝ,
      parityOriginalB590SingleGateFourierIntegrand434 E s δ p i ξ) -
      parityOriginalB590SingleGateFourierBox434 E s δ p i T‖ ≤
      ∫ ξ in (Set.Icc (-T) T)ᶜ,
        ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ‖ := by
  let F := parityOriginalB590SingleGateFourierIntegrand434 E s δ p i
  have hInt : Integrable F :=
    parity_original_B590_single_gate_fourier_integrable434 E s δ p i
  have hSplit := integral_add_compl (s := Set.Icc (-T) T)
    measurableSet_Icc hInt
  change (∫ ξ in Set.Icc (-T) T, F ξ) +
      (∫ ξ in (Set.Icc (-T) T)ᶜ, F ξ) = ∫ ξ, F ξ at hSplit
  have hDiff : (∫ ξ, F ξ) - (∫ ξ in Set.Icc (-T) T, F ξ) =
      ∫ ξ in (Set.Icc (-T) T)ᶜ, F ξ := by
    rw [←hSplit]
    abel
  rw [show (∫ ξ : ℝ, F ξ) -
     parityOriginalB590SingleGateFourierBox434 E s δ p i T =
     ∫ ξ in (Set.Icc (-T) T)ᶜ, F ξ from hDiff]
  calc
    _ ≤ ∫ ξ in (Set.Icc (-T) T)ᶜ, ‖F ξ‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc.compl
      intro ξ hξ
      unfold F parityOriginalB590SingleGateFourierIntegrand434
      change ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ *
        Complex.exp (((2*Real.pi*(ξ/s i) *
          (parityOriginalQAllocationResidual434 E δ p i -
          Real.log (p i:ℝ)):ℝ):ℂ)*Complex.I)‖ =
        ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ‖
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierBoxTelescoping -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Fully algebraic telescoping estimate for the difference between
full and truncated Q-frequency products. Earlier retained box factors
and later full factors are kept in their CORRECT original order, not
replaced by a fictitious independent allocation. -/
theorem parity_original_B590_fourier_box_prod_telescope434
    {N : ℕ} (a b : Fin N → ℂ) :
    ‖(∏ i : Fin N, a i) - ∏ i : Fin N, b i‖ ≤
      ∑ i : Fin N, ‖a i-b i‖ *
        (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => j < i), ‖b j‖) *
        (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => i < j), ‖a j‖) := by
  have hTel := Finset.prod_sub_ordered
    (Finset.univ : Finset (Fin N)) a (fun i => a i-b i)
  have hSimple :
      ∏ i : Fin N, (a i-(a i-b i)) = ∏ i : Fin N, b i := by
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [hSimple] at hTel
  have hEq :
      (∏ i : Fin N, a i) - ∏ i : Fin N, b i =
      ∑ i : Fin N, (a i-b i) *
        (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => j < i), b j) *
        (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => i < j), a j) := by
    rw [hTel]
    ring
  rw [hEq]
  calc
    _ ≤ ∑ i : Fin N, ‖(a i-b i) *
      (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => j < i), b j) *
      (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => i < j), a j)‖ :=
        norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul,norm_mul,norm_prod,norm_prod]

/-- Apply the original telescoping identity to ACTUAL full and box
Schwartz B590 Fourier integrals; this theorem explicitly yields a
rigorous bound for each δ and true history-dependent Q tuple. -/
theorem parity_original_B590_full_fourier_minus_box_ordered_bound434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ) (δ : Fin N → Bool)
    (p : Fin N → ℕ) (T : ℝ) :
    ‖(∫ ξ : Fin N → ℝ,
      parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ) -
      parityOriginalB590AllGateFourierBox434 E s δ p T‖ ≤
      ∑ i : Fin N,
        ‖(∫ ξ : ℝ,
          parityOriginalB590SingleGateFourierIntegrand434 E s δ p i ξ) -
          parityOriginalB590SingleGateFourierBox434 E s δ p i T‖ *
        (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => j < i),
          ‖parityOriginalB590SingleGateFourierBox434 E s δ p j T‖) *
        (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => i < j),
          ‖∫ ξ : ℝ, parityOriginalB590SingleGateFourierIntegrand434 E s δ p j ξ‖) := by
  rw [parity_original_B590_all_gate_fourier_box_eq_product434]
  rw [parity_original_B590_all_gate_full_fourier_integral_exact434]
  have hProduct :
      ((parityOriginalQAllocationBranchWeight434 20 E s δ p : ℝ) : ℂ) =
      ∏ i : Fin N,
        ∫ ξ : ℝ, parityOriginalB590SingleGateFourierIntegrand434 E s δ p i ξ := by
    unfold parityOriginalQAllocationBranchWeight434
    push_cast
    apply Finset.prod_congr rfl
    intro i hi
    exact (parity_original_B590_single_gate_integral_equals_real_gate434 E s δ p i).symm
  rw [hProduct]
  exact parity_original_B590_fourier_box_prod_telescope434
    (fun i => ∫ ξ : ℝ, parityOriginalB590SingleGateFourierIntegrand434 E s δ p i ξ)
    (fun i => parityOriginalB590SingleGateFourierBox434 E s δ p i T)
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierBoxUnion -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Literal original frequency slots before and after i partition
all Q variables other than i. No duplicated or missing reserved index. -/
theorem parity_original_B590_slot_lt_gt_prod_eq_erase434
    {N : ℕ} (i : Fin N) (m : Fin N → ℝ) :
    (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => j < i), m j) *
      (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => i < j), m j) =
    ∏ j ∈ (Finset.univ : Finset (Fin N)).erase i, m j := by
  let S : Finset (Fin N) := Finset.univ.erase i
  have hLow : S.filter (fun j => j < i) =
      (Finset.univ : Finset (Fin N)).filter (fun j => j < i) := by
    ext j
    simp only [S, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, true_and]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨ne_of_lt h,h⟩
  have hHigh : S.filter (fun j => ¬j < i) =
      (Finset.univ : Finset (Fin N)).filter (fun j => i < j) := by
    ext j
    simp only [S, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, true_and]
    constructor
    · intro h
      exact lt_of_le_of_ne (le_of_not_gt h.2) (Ne.symm h.1)
    · intro h
      exact ⟨ne_of_gt h, not_lt_of_ge h.le⟩
  calc
    _ = (∏ j ∈ S.filter (fun j => j < i), m j) *
          (∏ j ∈ S.filter (fun j => ¬j < i), m j) := by
            rw [hLow,hHigh]
    _ = ∏ j ∈ S, m j := Finset.prod_filter_mul_prod_filter_not S (fun j => j < i) m
    _ = _ := rfl

/-- Abstract but EXACT complex original Fourier truncation bound from
a full-vs-box product: if every source coordinate's complex full/box
integrals have individual norm ≤M_i and difference ≤t_i, then the
whole product difference ≤ the one-coordinate tail union. This does
not assume any independence of original Q values or buffered residuals. -/
theorem parity_original_B590_fourier_box_prod_norm_le_union434
    {N : ℕ} (a b : Fin N → ℂ) (M t : Fin N → ℝ)
    (hM : ∀ i, 0 ≤ M i)
    (ht : ∀ i, 0 ≤ t i)
    (ha : ∀ i, ‖a i‖ ≤ M i)
    (hb : ∀ i, ‖b i‖ ≤ M i)
    (hdiff : ∀ i, ‖a i-b i‖ ≤ t i) :
    ‖(∏ i : Fin N, a i) - (∏ i : Fin N, b i)‖ ≤
      ∑ i : Fin N, t i *
        (∏ j ∈ (Finset.univ : Finset (Fin N)).erase i, M j) := by
  have hTel := parity_original_B590_fourier_box_prod_telescope434 a b
  refine hTel.trans (Finset.sum_le_sum ?_)
  intro i hi
  have hLow :
      (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => j < i), ‖b j‖) ≤
      (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => j < i), M j) := by
    apply Finset.prod_le_prod₀
    · intro j hj; exact norm_nonneg _
    · intro j hj; exact hb j
  have hHigh :
      (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => i < j), ‖a j‖) ≤
      (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => i < j), M j) := by
    apply Finset.prod_le_prod₀
    · intro j hj; exact norm_nonneg _
    · intro j hj; exact ha j
  have hLow0 : 0 ≤
      (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => j < i), ‖b j‖) :=
    Finset.prod_nonneg (by intro j hj; exact norm_nonneg _)
  have hHigh0 : 0 ≤
      (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => i < j), ‖a j‖) :=
    Finset.prod_nonneg (by intro j hj; exact norm_nonneg _)
  have hMlow0 : 0 ≤
      (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => j < i), M j) :=
    Finset.prod_nonneg (by intro j hj; exact hM j)
  have hMhigh0 : 0 ≤
      (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => i < j), M j) :=
    Finset.prod_nonneg (by intro j hj; exact hM j)
  calc
    ‖a i-b i‖ * _ * _ ≤ t i * _ * _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hdiff i) hLow0) hHigh0
    _ ≤ (t i * (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => j < i), ‖b j‖)) *
          (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => i < j), M j) := by
      exact mul_le_mul_of_nonneg_left hHigh (mul_nonneg (ht i) hLow0)
    _ ≤ (t i * (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => j < i), M j)) *
          (∏ j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => i < j), M j) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLow (ht i)) hMhigh0
    _ = t i * (∏ j ∈ (Finset.univ : Finset (Fin N)).erase i, M j) := by
      rw [mul_assoc, parity_original_B590_slot_lt_gt_prod_eq_erase434]
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierBoxActualTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The ACTUAL original one-dimensional source Fourier inverse-gate
integral has norm ≤ the full true Schwartz Fourier-L1 mass.
The oscillatory exponential from physical Q-prime residual is unitary. -/
theorem parity_original_B590_single_gate_full_fourier_norm_le_L1434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ) (δ : Fin N → Bool)
    (p : Fin N → ℕ) (i : Fin N) :
    ‖∫ ξ : ℝ, parityOriginalB590SingleGateFourierIntegrand434 E s δ p i ξ‖ ≤
      ∫ ξ : ℝ,
        ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ‖ := by
  calc
    _ ≤ ∫ ξ : ℝ, ‖parityOriginalB590SingleGateFourierIntegrand434 E s δ p i ξ‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      unfold parityOriginalB590SingleGateFourierIntegrand434
      change ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ *
        Complex.exp (((2*Real.pi*(ξ/s i) *
          (parityOriginalQAllocationResidual434 E δ p i -
           Real.log (p i : ℝ)):ℝ):ℂ)*Complex.I)‖ =
        ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ‖
      rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]

/-- FULL ORIGINAL source B590 N-dimensional Fourier integral minus its
literal independent real frequency box [-T,T]^N is bounded directly
by the CORRECT one-coordinate source Fourier tail union. This uses
exact complex product telescoping and true Schwartz L1 gate masses;
no heuristic dimensional independence or missing f0/f1 modes. -/
theorem parity_original_B590_full_fourier_minus_box_le_actual_union434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ) (δ : Fin N → Bool)
    (p : Fin N → ℕ) (T : ℝ) :
    ‖(∫ ξ : Fin N → ℝ,
       parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ) -
       parityOriginalB590AllGateFourierBox434 E s δ p T‖ ≤
      ∑ i : Fin N, parityOriginalB590OneCoordinateFourierTail434 δ i T := by
  let a : Fin N → ℂ := fun i =>
    ∫ ξ : ℝ, parityOriginalB590SingleGateFourierIntegrand434 E s δ p i ξ
  let b : Fin N → ℂ := fun i => parityOriginalB590SingleGateFourierBox434 E s δ p i T
  let M : Fin N → ℝ := fun i =>
    ∫ ξ : ℝ, ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ‖
  let t : Fin N → ℝ := fun i =>
    ∫ ξ in (Set.Icc (-T) T)ᶜ,
      ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) ξ‖
  have hM (i : Fin N) : 0 ≤ M i := integral_nonneg (fun ξ => norm_nonneg _)
  have ht (i : Fin N) : 0 ≤ t i :=
    setIntegral_nonneg measurableSet_Icc.compl (fun ξ _ => norm_nonneg _)
  have ha (i : Fin N) : ‖a i‖ ≤ M i :=
    parity_original_B590_single_gate_full_fourier_norm_le_L1434 E s δ p i
  have hb (i : Fin N) : ‖b i‖ ≤ M i :=
    parity_original_B590_single_gate_fourier_box_norm_le_L1434 E s δ p i T
  have hdiff (i : Fin N) : ‖a i-b i‖ ≤ t i :=
    parity_original_B590_single_gate_fourier_full_sub_box_norm_le_tail434 E s δ p i T
  have hTel := parity_original_B590_fourier_box_prod_norm_le_union434
    a b M t hM ht ha hb hdiff
  have hProd :
      (∫ ξ : Fin N → ℝ,
        parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ) =
        ∏ i : Fin N, a i := by
    rw [parity_original_B590_all_gate_full_fourier_integral_exact434]
    unfold parityOriginalQAllocationBranchWeight434
    push_cast
    apply Finset.prod_congr rfl
    intro i hi
    exact (parity_original_B590_single_gate_integral_equals_real_gate434 E s δ p i).symm
  have hBox : parityOriginalB590AllGateFourierBox434 E s δ p T =
      ∏ i : Fin N, b i :=
    parity_original_B590_all_gate_fourier_box_eq_product434 E s δ p T
  rw [hProd,hBox]
  change ‖(∏ i : Fin N, a i) - ∏ i : Fin N, b i‖ ≤
    ∑ i : Fin N, t i * (∏ j ∈ (Finset.univ : Finset (Fin N)).erase i, M j)
  exact hTel
end Green64Analytic.Parity

end

end

/-! ## OriginalB590EWindowCutoff -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- TRUE historical Parity(4.5) e-window for the source real f0/f1
allocation gate, on actual original full-Q subtyped source tuple.
Unlike the Fourier integrand at one ξ, a real source allocation
weight is LITERALLY ZERO outside this e-window. The lower exponent
88 is already proved using actual source Q geometry and the full Q
capacity E<=Π remaining Q. -/
theorem parity_eventually_original_B590_e_outside_window_real_gate_zero434 :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧
      ∀ (E : ℝ), 1 ≤ E →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (f : (j : Fin (sourceOriginalLiteralDepth 20 L+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20
            (sourceOriginalLiteralDepth 20 L) L j}),
      E ≤ ((∏ i,
        (parityActualSourceRemainingFullQTuple434
          (sourceOriginalLiteralDepth 20 L) L band slot f i).val : ℕ) : ℝ) →
      ∀ (δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool),
      let p := parityActualSourceRemainingFullQTuple434
        (sourceOriginalLiteralDepth 20 L) L band slot f
      let e := paritySourceOrderedAllocatedE434 δ p
      ((e:ℝ) < E*L^((-88:ℝ)) ∨ E < (e:ℝ)) →
      parityOriginalQAllocationBranchWeight434 20 E
        (sourceActualSortedFrequencyScales 20
          (sourceOriginalLiteralDepth 20 L) L band slot) δ
        (fun i => (p i).val) = 0 := by
  filter_upwards [parity_eventually_actual_smooth_e_full_range_of_Q_mass434]
    with L h
  refine ⟨h.1,?_⟩
  intro E hE band slot f hFull δ
  dsimp only
  intro hOutside
  by_contra hWeight
  have hInside := h.2 E hE band slot δ
    (parityActualSourceRemainingFullQTuple434
      (sourceOriginalLiteralDepth 20 L) L band slot f)
    hFull hWeight
  dsimp only at hInside
  rcases hOutside with hLo | hHi
  · exact (not_lt_of_ge hInside.1) hLo
  · exact (not_lt_of_ge hInside.2.1) hHi

/-- A Fourier BOX integral for any original B590 branch with e OUTSIDE
the true historical Parity(4.5) interval is generally NOT identically
zero. Instead, since its COMPLETE N-dimensional Fourier integral is
zero, its truncated integral is bounded by the true δ one-coordinate
Fourier Schwartz tail. This exact inequality is the prerequisite for
legitimately cutting `a_e` support AFTER Fourier truncation. -/
theorem parity_eventually_original_B590_e_outside_window_fourier_box_tail434 :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧
      ∀ (E : ℝ), 1 ≤ E →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (f : (j : Fin (sourceOriginalLiteralDepth 20 L+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20
            (sourceOriginalLiteralDepth 20 L) L j}),
      E ≤ ((∏ i,
        (parityActualSourceRemainingFullQTuple434
          (sourceOriginalLiteralDepth 20 L) L band slot f i).val : ℕ) : ℝ) →
      ∀ (δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool),
      let p := parityActualSourceRemainingFullQTuple434
        (sourceOriginalLiteralDepth 20 L) L band slot f
      let e := paritySourceOrderedAllocatedE434 δ p
      ((e:ℝ) < E*L^((-88:ℝ)) ∨ E < (e:ℝ)) →
      ‖parityOriginalB590AllGateFourierBox434 E
        (sourceActualSortedFrequencyScales 20
          (sourceOriginalLiteralDepth 20 L) L band slot) δ
        (fun i => (p i).val) L‖ ≤
      ∑ i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length,
        parityOriginalB590OneCoordinateFourierTail434 δ i L := by
  filter_upwards [parity_eventually_original_B590_e_outside_window_real_gate_zero434]
    with L h
  refine ⟨h.1,?_⟩
  intro E hE band slot f hFull δ
  dsimp only
  intro hOutside
  have hZero := h.2 E hE band slot f hFull δ hOutside
  let s := sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L band slot
  let p := fun i => (parityActualSourceRemainingFullQTuple434
      (sourceOriginalLiteralDepth 20 L) L band slot f i).val
  have hFullIntegral := parity_original_B590_all_gate_full_fourier_integral_exact434
    E s δ p
  have hTail := parity_original_B590_full_fourier_minus_box_le_actual_union434
    E s δ p L
  rw [hFullIntegral,hZero] at hTail
  simpa only [Complex.ofReal_zero,zero_sub,norm_neg] using hTail
end Green64Analytic.Parity

end

end

/-! ## OriginalB590EWindowAllAssignments -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16500000

/-- TRUE original Parity (4.5) e-window `E*L^-88<=e<=E` for one actual
20!-labelled full-Q tuple and all Boolean B590 Q-history assignments.
The support restriction is on the selected integer e from actual Q
primes; no Fourier-phase pointwise cancellation is assumed. -/
def parityOriginalB590OutsideEWindowAssignments434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    Finset (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) :=
  (Finset.univ : Finset (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)).filter
      (fun δ =>
        let e := paritySourceOrderedAllocatedE434 δ
          (parityActualSourceRemainingFullQTuple434 d L band slot f)
        ((e:ℝ) < E*L^((-88:ℝ)) ∨ E < (e:ℝ)))

/-- For any requested A, original source Parity (4.5) window removal at
Fourier frequency cutoff [-L,L]^N is rigorously negligible UNIFORMLY
on every physically retained full Q tuple `E<=ΠQremaining`. The
real B590 gate vanishes outside [E L^-88,E], and the remaining
Fourier-box leakage is bounded by the *existing all-δ/source Schwartz*
tail L^-A, not by asserting pointwise box weights vanish.
All original reserved Q slots, labelled factorial Q tuples and E>=1
are quantified universally. The bound is on the genuine COMPLEX
sum of outside-window truncated Fourier branch integrals. -/
theorem parity_eventually_original_B590_fullQ_outside_e_fourier_box_all_log434
    (A : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧
      ∀ (E : ℝ), 1 ≤ E →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (f : (j : Fin (sourceOriginalLiteralDepth 20 L+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20
            (sourceOriginalLiteralDepth 20 L) L j}),
      E ≤ ((∏ i,
        (parityActualSourceRemainingFullQTuple434
          (sourceOriginalLiteralDepth 20 L) L band slot f i).val : ℕ) : ℝ) →
      ‖∑ δ ∈ parityOriginalB590OutsideEWindowAssignments434
          (sourceOriginalLiteralDepth 20 L) L E band slot f,
        parityOriginalB590AllGateFourierBox434 E
          (sourceActualSortedFrequencyScales 20
            (sourceOriginalLiteralDepth 20 L) L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434
            (sourceOriginalLiteralDepth 20 L) L band slot f i).val) L‖ ≤
        L^(-A) := by
  filter_upwards [parity_eventually_original_B590_e_outside_window_fourier_box_tail434,
    parity_eventually_original_B590_actual_fourier_tail_all_log434 A]
    with L hEwin hTail
  refine ⟨hEwin.1,?_⟩
  intro E hE band slot f hFull
  let d := sourceOriginalLiteralDepth 20 L
  let N : ℕ := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let outside := parityOriginalB590OutsideEWindowAssignments434 d L E band slot f
  let p := fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  let tail : (Fin N → Bool) → ℝ := fun δ =>
    ∑ i : Fin N, parityOriginalB590OneCoordinateFourierTail434 δ i L
  have hPart (δ : Fin N → Bool) (hδ : δ ∈ outside) :
      ‖parityOriginalB590AllGateFourierBox434 E s δ p L‖ ≤ tail δ := by
    have hOutside :
        ((paritySourceOrderedAllocatedE434 δ
          (parityActualSourceRemainingFullQTuple434 d L band slot f):ℝ) <
          E*L^((-88:ℝ)) ∨
          E < (paritySourceOrderedAllocatedE434 δ
            (parityActualSourceRemainingFullQTuple434 d L band slot f):ℝ)) :=
      (Finset.mem_filter.mp hδ).2
    exact hEwin.2 E hE band slot f hFull δ hOutside
  have hTailPos (δ : Fin N → Bool) : 0 ≤ tail δ := by
    apply Finset.sum_nonneg
    intro i hi
    unfold parityOriginalB590OneCoordinateFourierTail434
    exact mul_nonneg
      (setIntegral_nonneg measurableSet_Icc.compl (by intro ξ hξ; exact norm_nonneg _))
      (Finset.prod_nonneg (by intro j hj; exact integral_nonneg (fun ξ => norm_nonneg _)))
  calc
    _ ≤ ∑ δ ∈ outside, ‖parityOriginalB590AllGateFourierBox434 E s δ p L‖ :=
      norm_sum_le _ _
    _ ≤ ∑ δ ∈ outside, tail δ := by
      apply Finset.sum_le_sum
      intro δ hδ
      exact hPart δ hδ
    _ ≤ ∑ δ : Fin N → Bool, tail δ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ outside)
      intro δ hδ hnot
      exact hTailPos δ
    _ ≤ L^(-A) := hTail band slot
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FullAssignmentFubini -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Original B590 N-slot Fourier representation, now summed over ALL
2^N history-dependent Boolean Q allocations. Integrability of the
full sum is a conclusion, not a Fubini premise. The original gates
and residuals are literal, and no ξ=0 shortcut is used. -/
theorem parity_original_B590_all_assignments_full_fourier_fubini434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ) (p : Fin N → ℕ) :
    Integrable (fun ξ : Fin N → ℝ =>
      ∑ δ : Fin N → Bool,
        parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ) ∧
    ((∑ δ : Fin N → Bool,
      parityOriginalQAllocationBranchWeight434 20 E s δ p : ℝ) : ℂ) =
      ∫ ξ : Fin N → ℝ,
        ∑ δ : Fin N → Bool,
          parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ := by
  have hInt (δ : Fin N → Bool) (hδ : δ ∈ (Finset.univ : Finset (Fin N → Bool))) :
      Integrable (parityOriginalB590AllGateFourierIntegrand434 E s δ p) :=
    parity_original_B590_all_gate_fourier_product_integrable434 E s δ p
  refine ⟨integrable_finsetSum Finset.univ hInt, ?_⟩
  calc
    ((∑ δ : Fin N → Bool,
      parityOriginalQAllocationBranchWeight434 20 E s δ p : ℝ) : ℂ) =
        ∑ δ : Fin N → Bool,
          ((parityOriginalQAllocationBranchWeight434 20 E s δ p : ℝ) : ℂ) := by
            push_cast
            rfl
    _ = ∑ δ : Fin N → Bool, ∫ ξ : Fin N → ℝ,
          parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ := by
            apply Finset.sum_congr rfl
            intro δ hδ
            exact (parity_original_B590_all_gate_full_fourier_integral_exact434 E s δ p).symm
    _ = _ := (integral_finsetSum Finset.univ hInt).symm

/-- Exact original complete 20!-labelled Q-tuple with one reserved
prime: the FULL real f0/f1 B590 allocation mass equals the true
multi-dimensional Fourier integral of all original allocation paths.
Each Fourier integrand contains the true source Q bands, residual and
historic Schwartz gate. -/
theorem parity_original_actual_fullQ_B590_all_assignments_full_fourier434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    let s := sourceActualSortedFrequencyScales 20 d L band slot
    let p := fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val
    Integrable (fun ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      ∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ) ∧
    ((parityActualOriginalAFullTupleAllocationMass434 d L E band slot f : ℝ) : ℂ) =
      ∫ ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ,
        ∑ δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ := by
  dsimp only
  have h := parity_original_B590_all_assignments_full_fourier_fubini434 E
    (sourceActualSortedFrequencyScales 20 d L band slot)
    (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val)
  refine ⟨h.1, ?_⟩
  unfold parityActualOriginalAFullTupleAllocationMass434
  exact h.2

/-- The same full multi-dimensional original Fourier integral is
exactly one on the genuine E≤Q_remaining physical retained support.
This directly bridges prior source-original B590 mass normalization
to its true product-measure Fourier representation, not a nested
formal substitute. -/
theorem parity_original_actual_fullQ_retained_full_fourier_mass_one434
    (d : ℕ) (L E : ℝ) (hL : 0 < L) (hE : 1 ≤ E)
    (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (hFull : E ≤ ((∏ i,
      (parityActualSourceRemainingFullQTuple434 d L band slot f i).val : ℕ) : ℝ)) :
    (∫ ξ : Fin (sourceOrderedLabels 20
       (sourceActualSortedScales 20 d L) band slot).length → ℝ,
      ∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        parityOriginalB590AllGateFourierIntegrand434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) ξ) = 1 := by
  have h := (parity_original_actual_fullQ_B590_all_assignments_full_fourier434
    d L E band slot f).2
  rw [← h]
  rw [parity_original_actual_fullQ_B590_all_assignments_mass_one434
    d L E hL hE band slot f hFull]
  norm_num
end Green64Analytic.Parity

end

end

