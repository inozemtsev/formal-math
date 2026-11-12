module

public import Green64.Library.Sieve.Foundations.Part010
public import Green64.Library.Sieve.Foundations.Part009
public import Green64.Library.Correlation.Part072
public import Green64.Library.Sieve.Foundations.Part008

@[expose] public section

/-!
# Sieve / Foundations / Part011

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalB590FourierBoxAllAssignments -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Exact ORIGINAL all-B590-allocation Fourier box approximation on a
fixed ordered Q tuple. Summing ALL history-dependent 2^N branch
integrals does not lose any delta assignment or source prime. -/
theorem parity_original_B590_all_assignments_full_minus_box_le_tail_union434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ) (p : Fin N → ℕ)
    (T : ℝ) :
    ‖(∑ δ : Fin N → Bool,
        ∫ ξ : Fin N → ℝ,
          parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ) -
      (∑ δ : Fin N → Bool,
          parityOriginalB590AllGateFourierBox434 E s δ p T)‖ ≤
      ∑ δ : Fin N → Bool, ∑ i : Fin N,
        parityOriginalB590OneCoordinateFourierTail434 δ i T := by
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ δ : Fin N → Bool,
      ‖(∫ ξ : Fin N → ℝ,
          parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ) -
        parityOriginalB590AllGateFourierBox434 E s δ p T‖ :=
        norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro δ hδ
      exact parity_original_B590_full_fourier_minus_box_le_actual_union434
        E s δ p T

/-- The literal full SOURCE r0=20 Q-labelled B590 **total allocation
mass** differs from its true finite Fourier box approximation by at
most the all-2^N source one-slot Schwartz tail union, independent of
original E, Q-prime magnitudes and splitting parameter K0. -/
theorem parity_original_actual_fullQ_B590_mass_minus_fourier_box_le_union434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (T : ℝ) :
    ‖((parityActualOriginalAFullTupleAllocationMass434 d L E band slot f : ℝ) : ℂ) -
      (∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        parityOriginalB590AllGateFourierBox434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot f i).val) T)‖ ≤
      ∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∑ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length,
          parityOriginalB590OneCoordinateFourierTail434 δ i T := by
  have h := parity_original_B590_all_assignments_full_minus_box_le_tail_union434
    E (sourceActualSortedFrequencyScales 20 d L band slot)
    (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) T
  have hIntegral (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
      (_hδ : δ ∈ Finset.univ) :
      Integrable (parityOriginalB590AllGateFourierIntegrand434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) δ
        (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val)) :=
    parity_original_B590_all_gate_fourier_product_integrable434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) δ
      (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val)
  have hMass := (parity_original_actual_fullQ_B590_all_assignments_full_fourier434
    d L E band slot f).2
  rw [integral_finsetSum Finset.univ hIntegral] at hMass
  rw [hMass]
  exact h
end Green64Analytic.Parity

end

end

/-! ## OriginalB590ActualBoxAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- COMPLETE original Parity §4.2 (4.6) replacement: for any requested
inverse-log precision A, on the true moving Q-depth `d(L)` and
EVERY original full 20!-labelled Q tuple (with arbitrary reserved
Q prime), the source full B590 mass is approximated by the genuine
N-dimensional Fourier box [-L,L]^N with absolute error L^-A.
The proof uses kernel-verified real multi-product Fourier inversion,
complex product telescoping, true 2^N union bound, fixed Schwartz
moments and actual depth N≤40log L. It never replaces Fourier
integration by evaluation ξ=0. -/
theorem parity_eventually_original_actual_B590_fullQ_fourier_box_all_log434
    (A : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ)
        (f : (j : Fin (sourceOriginalLiteralDepth 20 L+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20
            (sourceOriginalLiteralDepth 20 L) L j}),
      ‖((parityActualOriginalAFullTupleAllocationMass434
          (sourceOriginalLiteralDepth 20 L) L E band slot f : ℝ) : ℂ) -
        (∑ δ : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20
              (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool,
          parityOriginalB590AllGateFourierBox434 E
            (sourceActualSortedFrequencyScales 20
              (sourceOriginalLiteralDepth 20 L) L band slot) δ
            (fun i => (parityActualSourceRemainingFullQTuple434
              (sourceOriginalLiteralDepth 20 L) L band slot f i).val) L)‖ ≤
        L^(-A) := by
  filter_upwards [parity_eventually_original_B590_actual_fourier_tail_all_log434 A]
    with L hL
  intro band slot E f
  exact (parity_original_actual_fullQ_B590_mass_minus_fourier_box_le_union434
    (sourceOriginalLiteralDepth 20 L) L E band slot f L).trans (hL band slot)

/-- Same true source full Q box inversion, with retained physical
`1≤E≤Qproduct` allocation normalisation as an exact equality:
`‖1 - sumδ boxFourier‖≤L^-A`. There is no approximate source mass
or hidden B590 ζ assumption. -/
theorem parity_eventually_original_actual_retained_B590_box_mass_one_all_log434
    (A : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      0 < L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ) (hE : 1 ≤ E)
        (f : (j : Fin (sourceOriginalLiteralDepth 20 L+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20
            (sourceOriginalLiteralDepth 20 L) L j})
        (hFull : E ≤ ((∏ i,
          (parityActualSourceRemainingFullQTuple434
            (sourceOriginalLiteralDepth 20 L) L band slot f i).val : ℕ) : ℝ)),
      ‖(1:ℂ) -
        (∑ δ : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20
              (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool,
          parityOriginalB590AllGateFourierBox434 E
            (sourceActualSortedFrequencyScales 20
              (sourceOriginalLiteralDepth 20 L) L band slot) δ
            (fun i => (parityActualSourceRemainingFullQTuple434
              (sourceOriginalLiteralDepth 20 L) L band slot f i).val) L)‖ ≤
        L^(-A) := by
  filter_upwards [parity_eventually_original_actual_B590_fullQ_fourier_box_all_log434 A,
    eventually_gt_atTop (0:ℝ)] with L hBox hLp
  refine ⟨hLp,?_⟩
  intro band slot E hE f hFull
  have hMass := parity_original_actual_fullQ_B590_all_assignments_mass_one434
    (sourceOriginalLiteralDepth 20 L) L E hLp hE band slot f hFull
  simpa only [hMass, Complex.ofReal_one] using hBox band slot E f
end Green64Analytic.Parity

end

end

/-! ## OriginalB590WeightedFullFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Literal source original B590/B509 **arithmetic** coefficient with
all 20! normalization, original P-W1/parity and full labelled Q-product
gate, leaving only the actual real B590 f0/f1 allocation gates to be
reconstructed by multi-dimensional Fourier inversion. The original
B509 character at any fixed χ is preserved, not replaced by ξ=0. -/
def parityOriginalB590FullBranchArithmetic434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (χ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (z : parityActualOriginalAFullBranchCarrier434 d L band slot) : ℂ :=
  let P := sourceOriginalPAllActualBands 20 L
  let p := parityActualSourceRemainingFullQTuple434 d L band slot z.2
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  if (∏ j : Fin (d+1), ∏ i : Fin 20, (z.2 j i).val) =
     sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u then
    (((∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)) *
       (sourceOriginalW1 P u *
         ((1-(-1:ℝ)^sourceOriginalPParityExponent
           (Finset.univ.biUnion P) u)/2)) : ℝ) : ℂ) *
      paritySourceFullSlotFourierPhase434 s χ z.1 p
  else 0

/-- The TRUE historic original smooth physical branch factors
EXACTLY into its arithmetic factorial/W1/P parity/full-Q/χ character
coefficient times the single full history-dependent B590 δ weight.
This identity holds for bad Q gates too, which both vanish. -/
theorem parity_original_B590_full_branch_weight_arithmetic_factor434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (χ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (z : parityActualOriginalAFullBranchCarrier434 d L band slot) :
    parityActualOriginalAFullBranchWeight434 d L E u band slot χ z =
      parityOriginalB590FullBranchArithmetic434 d L u band slot χ z *
        ((parityOriginalQAllocationBranchWeight434 20 E
           (sourceActualSortedFrequencyScales 20 d L band slot) z.1
           (fun i => (parityActualSourceRemainingFullQTuple434
             d L band slot z.2 i).val) : ℝ) : ℂ) := by
  unfold parityActualOriginalAFullBranchWeight434
    parityOriginalB590FullBranchArithmetic434
  by_cases hgate : (∏ j : Fin (d+1), ∏ i : Fin 20, (z.2 j i).val) =
       sourceOriginalOrdinaryPart
         (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · simp only [if_pos hgate]
    ring
  · simp only [if_neg hgate, zero_mul]

/-- Original Schwartz full Q-label Fourier integral: the arithmetic
factorial/W1/parity/χ physical coefficient is constant in the B590
integration frequency, so it can be pulled out and its exact gate
weight reconstructed. No nonzero branch assumption or heuristic
oscillatory cancellation. -/
theorem parity_original_B590_full_branch_weight_fourier_integral434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (χ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (z : parityActualOriginalAFullBranchCarrier434 d L band slot) :
    parityActualOriginalAFullBranchWeight434 d L E u band slot χ z =
      ∫ ξ : Fin (sourceOrderedLabels 20
         (sourceActualSortedScales 20 d L) band slot).length → ℝ,
        parityOriginalB590FullBranchArithmetic434 d L u band slot χ z *
          parityOriginalB590AllGateFourierIntegrand434 E
             (sourceActualSortedFrequencyScales 20 d L band slot) z.1
             (fun i => (parityActualSourceRemainingFullQTuple434
                d L band slot z.2 i).val) ξ := by
  rw [parity_original_B590_full_branch_weight_arithmetic_factor434]
  rw [integral_const_mul]
  congr 1
  exact (parity_original_B590_all_gate_full_fourier_integral_exact434 E
    (sourceActualSortedFrequencyScales 20 d L band slot) z.1
    (fun i => (parityActualSourceRemainingFullQTuple434
       d L band slot z.2 i).val)).symm

/-- Real full original source branch-integrand is integrable with
factorial W1/parity, true Q product gate and actual B509 character χ,
because the original full B590 Fourier integrand is independently
integrable on finite-dimensional product Lebesgue measure. -/
theorem parity_original_B590_full_branch_arithmetic_fourier_integrable434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (χ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (z : parityActualOriginalAFullBranchCarrier434 d L band slot) :
    Integrable (fun ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      parityOriginalB590FullBranchArithmetic434 d L u band slot χ z *
        parityOriginalB590AllGateFourierIntegrand434 E
           (sourceActualSortedFrequencyScales 20 d L band slot) z.1
           (fun i => (parityActualSourceRemainingFullQTuple434
              d L band slot z.2 i).val) ξ) :=
    (parity_original_B590_all_gate_fourier_product_integrable434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) z.1
      (fun i => (parityActualSourceRemainingFullQTuple434
        d L band slot z.2 i).val)).const_mul _
end Green64Analytic.Parity

end

end

/-! ## OriginalB590ArithmeticZero -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Exactly at the original B509 χ=0, the FULL true arithmetic Q/P
coefficient is precisely the preexisting factorial-labelled W1/parity
source real weight, independent of δ. This is proved by the original
full-slot Fourier character identity and actual Q full-product gate,
not by replacing a source coefficient by a synthetic positive mass. -/
theorem parity_original_B590_arithmetic_at_zero_eq_actual_tuple_weight434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (z : parityActualOriginalAFullBranchCarrier434 d L band slot) :
    parityOriginalB590FullBranchArithmetic434 d L u band slot (fun _ => 0) z =
      ((parityActualOriginalAFullTupleWeight434 d L u z.2 : ℝ) : ℂ) := by
  unfold parityOriginalB590FullBranchArithmetic434
    parityActualOriginalAFullTupleWeight434
  by_cases hgate : (∏ j : Fin (d+1), ∏ i : Fin 20, (z.2 j i).val) =
    sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · simp only [if_pos hgate]
    rw [parity_source_full_slot_phase_zero434]
    push_cast
    ring
  · simp only [if_neg hgate]
    norm_num

/-- The same original scalar arithmetic weight has modulus exactly
the true nonnegative W1×parity×factorial labelled Q-tuple weight. -/
theorem parity_original_B590_arithmetic_at_zero_norm_exact434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (z : parityActualOriginalAFullBranchCarrier434 d L band slot) :
    ‖parityOriginalB590FullBranchArithmetic434 d L u band slot (fun _ => 0) z‖ =
      parityActualOriginalAFullTupleWeight434 d L u z.2 := by
  rw [parity_original_B590_arithmetic_at_zero_eq_actual_tuple_weight434]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (parity_actual_original_A_full_tuple_weight_nonneg434 d L u z.2)
end Green64Analytic.Parity

end

end

/-! ## OriginalSelectedECoefficientPolylog -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Fixed actual Parity(4.9) selected Q-only Fourier coefficient
polylog exponent, from the REAL 20! band permutation count and the
literal largest admissible original Q-band depth, independent of K0
and Fourier truncation precision H. -/
def parityOriginalSelectedECoefficientPolylogExponent434 : ℝ :=
  2*Real.log ((20:ℕ).factorial:ℝ)

/-- The original exact `(20!)^(d+1)` selected-e Fourier endpoint
collision bound is polynomial in L at actual SOURCE moving Q depth.
The coefficient is the literal selected Q-prime Fourier e-fibre,
not yet the full historical post-integration a_e. -/
theorem parity_original_selected_e_factorial_to_polylog434
    (d : ℕ) (L : ℝ) (hL : Real.exp 2 ≤ L)
    (hd : sourceOriginalDepthAdmissible 20 d L) :
    (((20:ℕ).factorial:ℝ)^(d+1)) ≤
      L^parityOriginalSelectedECoefficientPolylogExponent434 := by
  let C : ℝ := ((20:ℕ).factorial:ℝ)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact_mod_cast (Nat.factorial_pos 20)
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hLp : 0 < L := (Real.exp_pos 2).trans_le hL
  have hLog : 0 ≤ Real.log C := Real.log_nonneg hC
  have hD : (((d+1:ℕ):ℝ)) ≤ 2*Real.log L :=
    parity_original_B590_admissible_depth_le_two_log434 d L hL hd
  have hScale := mul_le_mul_of_nonneg_left hD hLog
  have hEq : C^(d+1) = Real.exp (Real.log C * ((d+1:ℕ):ℝ)) := by
    rw [←Real.rpow_natCast,Real.rpow_def_of_pos hCp]
  dsimp [parityOriginalSelectedECoefficientPolylogExponent434]
  change C^(d+1) ≤ L^(2*Real.log C)
  rw [hEq,Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  nlinarith [hScale]

/-- Genuine SOURCE Parity(4.9) e-side selected-only Fourier coefficient
for ANY δ, physical Q-band/slot, real frequencies and e value has
uniform fixed polynomial bound `L^Ca` at the actual moving source depth.
The proof uses the already verified PRIME-FIBRE collision ≤(20!)^(d+1)
and true source depth ≤2logL; it makes NO claim that the separate skipped
Q/P/H(v*) physical residual is already fully factored. -/
theorem parity_eventually_original_selected_e_fourier_coeff_polylog434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (e : ℕ),
      ‖paritySourceQSelectedFourierEFibre434
        (Q := sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot)
        δ (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
          band slot) ξ e‖ ≤
        L^parityOriginalSelectedECoefficientPolylogExponent434 := by
  filter_upwards [source_original_literal_depth_properties_eventually 20 (by norm_num),
    eventually_ge_atTop (Real.exp 2)] with L hDepth hL
  intro band slot δ ξ e
  have hF := parity_actual_source_selected_fourier_e_fibre_norm_le_factorials434
    20 (sourceOriginalLiteralDepth 20 L) L (by omega)
    (by exact (Real.exp_pos 2).trans_le hL) band slot δ ξ e
  exact hF.trans (parity_original_selected_e_factorial_to_polylog434
    (sourceOriginalLiteralDepth 20 L) L hL hDepth.1)
end Green64Analytic.Parity

end

end

/-! ## OriginalSelectedEGateFourierCoeff -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The TRUE original historical Parity(4.7) **selected-Q-side**
frequency-dependent e coefficient at one fixed source Boolean B590
allocation δ and Q-frequency vector ξ: actual original f0/f1 Schwartz
Fourier transforms times the global log E character and the native
selected-Q Fourier e-endpoint fibre. Its signature has NO skipped-Q,
reserved-Q, P-group W1/parity, alpha/beta or physical v argument.
This is precisely the a_e-SIDE factor before the unproved compatibility
with the complete original v-side coefficient c_r/H(v*). -/
def parityOriginalSelectedEGateFourierCoefficient434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (e : ℕ) : ℂ :=
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  let Q := sourceActualSortedQ 20 d L band slot
  (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
    (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
  (((Real.fourierChar (Real.log E * (∑ i, ξ i/s i)) : Circle):ℂ)) *
  paritySourceQSelectedFourierEFibre434 (Q:=Q) δ s ξ e

/-- The source selected-e Fourier coefficient factor has EXACT
modulus equal to the original product of f0/f1 Fourier norms TIMES the
magnitude of its TRUE selected-Q endpoint fibre. Global log E character
is unitary even for E<0; no coefficient size is invented. -/
theorem parity_original_selected_e_gate_coeff_norm_factor434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (e : ℕ) :
    ‖parityOriginalSelectedEGateFourierCoefficient434 d L E band slot δ ξ e‖ =
      (∏ i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length,
        ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖) *
      ‖paritySourceQSelectedFourierEFibre434
        (Q := sourceActualSortedQ 20 d L band slot) δ
        (sourceActualSortedFrequencyScales 20 d L band slot) ξ e‖ := by
  unfold parityOriginalSelectedEGateFourierCoefficient434
  rw [norm_mul,norm_mul,norm_prod]
  simp only [Circle.norm_coe]
  ring

/-- True original Parity(4.9) selected-e source Fourier amplitude:
for any fixed δ,ξ at the actual moving Q depth, this candidate
a_e-SIDE factor has polynomial-in-L size *relative to the product
of actual B590 f0/f1 Fourier transforms*, with exponent independent
of K0 and Fourier cutoff moment H. The separate physical skipped-Q,
reserved-H and P-group v factor is still to be literally assembled. -/
theorem parity_eventually_original_selected_e_gate_coeff_polylog434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (e : ℕ),
      ‖parityOriginalSelectedEGateFourierCoefficient434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ e‖ ≤
        L^parityOriginalSelectedECoefficientPolylogExponent434 *
        (∏ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length,
          ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖) := by
  filter_upwards [parity_eventually_original_selected_e_fourier_coeff_polylog434]
    with L h
  intro band slot E δ ξ e
  rw [parity_original_selected_e_gate_coeff_norm_factor434]
  have hF : 0 ≤ (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length,
      ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖) :=
    Finset.prod_nonneg (by intro i hi; exact norm_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (h band slot δ ξ e) hF
  convert hh using 1 <;> ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSelectedEGateResidualFactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Exact SOURCE Parity(4.7) **selected e / B509 residual factorisation**
at any fixed original B590 allocation δ and real Fourier frequency ξ.
On the LEFT is the genuine Q-full factorial-labelled Fourier-character
sum, multiplied by original product of f0/f1 Schwartz transforms and
log(E) character. On the RIGHT selected e is OUTERMOST, and its
coefficient is the TRUE e-only `parityOriginalSelectedEGateFourierCoefficient434`;
the other factor is the NATIVE full B509 `sourceNativePrimeCore.residual`
summed over actual skipped-Q product h and original factorials.

The equality is on real source Q bands with the reserved prime and
all repeated labels, not an abstract coefficient. Its left/right
factors keep K,alpha,q,χ,σ_0,σ_1 as actual source parameters.
This still does NOT identify `residual` with historical reserved
`H(v*)` and W1/P parity, so it is an algebraic e-residual source
interface, not final Parity(4.7) or TypeII(4.2). -/
theorem parity_original_actual_B590_gate_selected_e_native_residual_factor434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    let Q := sourceActualSortedQ 20 d L band slot
    let s := sourceActualSortedFrequencyScales 20 d L band slot
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
    ((∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
        (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
      ((Real.fourierChar
        (Real.log E * (∑ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length,
          ξ i/s i)) : Circle) : ℂ)) *
      (∑ p : (i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length) →
          {z : ℕ // z ∈ Q i},
        sourceActualSortedFactorial 20 d *
          paritySourceFullSlotFourierPhase434 s ξ δ p) =
      ∑ e ∈ paritySourceQSelectedESupport434 (Q:=Q) δ,
        parityOriginalSelectedEGateFourierCoefficient434 d L E band slot δ ξ e *
        (∑ h ∈ paritySourceB509SkipEndpointSupport434 (Q:=Q) δ,
           F.residual h) := by
  dsimp only
  let Q := sourceActualSortedQ 20 d L band slot
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
  have hFactor := parity_actual_B509_original_fullQ_e_fibre_native_residual_factor434
    20 d L band slot δ ξ K alpha q χ σ₀ σ₁
  dsimp only at hFactor
  rw [hFactor]
  let C : ℂ := (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
    ((Real.fourierChar (Real.log E * (∑ i, ξ i/s i)) : Circle):ℂ)
  let R : ℂ := ∑ h ∈ paritySourceB509SkipEndpointSupport434 (Q:=Q) δ,
    F.residual h
  let a : ℕ → ℂ := paritySourceQSelectedFourierEFibre434 (Q:=Q) δ s ξ
  change C * ((∑ e ∈ paritySourceQSelectedESupport434 (Q:=Q) δ, a e)*R) =
    ∑ e ∈ paritySourceQSelectedESupport434 (Q:=Q) δ, (C*a e)*R
  rw [←Finset.sum_mul,←Finset.mul_sum]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSelectedEResidualProductBound -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Original native B509 source residual coefficient at an arbitrary
actual skipped-Q product h has norm ≤1, because the true factorial
normalization cancels the labelled skip-prime collision count.
This is the REAL residual, not an assumed bound on historical H(v*). -/
theorem parity_original_B509_native_residual_actual_norm_le_one434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) (h : ℕ) :
    ‖(sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).residual h‖ ≤ 1 := by
  exact source_native_residual_norm_le_one 20 d L (by omega) hL
    band slot δ ξ K alpha q χ σ₀ σ₁ h

/-- Full true original selected-Q a_e-SIDE × B509 native skipped-Q
residual c_h has fixed source polynomial (4.9)-type size, after
paying the actual f0/f1 Fourier gate product. The skipped factor is
kernel-proved ≤1 and the selected-only e endpoint ≤L^(2log20!).
No extra factor of 20! or 2^N is introduced, and no conjectural
physical H(v*) formula is asserted. -/
theorem parity_eventually_original_selected_e_residual_product_polylog434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (e h : ℕ) (K : Finset ℕ) (alpha : ℕ → ℂ)
        (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ),
      ‖parityOriginalSelectedEGateFourierCoefficient434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ e *
        (sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L
          band slot δ ξ K alpha q χ σ₀ σ₁).residual h‖ ≤
        L^parityOriginalSelectedECoefficientPolylogExponent434 *
        (∏ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length,
          ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖) := by
  filter_upwards [parity_eventually_original_selected_e_gate_coeff_polylog434,
    eventually_gt_atTop (0:ℝ)] with L hCoefficient hL
  intro band slot E δ ξ e h K alpha q χ σ₀ σ₁
  have hR := parity_original_B509_native_residual_actual_norm_le_one434
    (sourceOriginalLiteralDepth 20 L) L hL band slot δ ξ
    K alpha q χ σ₀ σ₁ h
  have hC := hCoefficient band slot E δ ξ e
  have hCnonneg : 0 ≤ ‖parityOriginalSelectedEGateFourierCoefficient434
      (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ e‖ := norm_nonneg _
  rw [norm_mul]
  calc
    _ ≤ ‖parityOriginalSelectedEGateFourierCoefficient434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ e‖ * 1 :=
        mul_le_mul_of_nonneg_left hR hCnonneg
    _ ≤ _ := by
      simpa only [mul_one] using hC
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHConvolution -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The ACTUAL original Parity(4.8) reserved-prime source convolution
carrier: one real original reserved Q-band prime p and one actual
B509 skipped-Q product r, with exact total product `t=p*r`.
No invented independent support, no cancellation or co-primality
assumption. The original factorials remain in the native residual. -/
def parityOriginalReservedHCarrier434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) :
    Finset (ℕ × ℕ) :=
  (sourceOriginalQActualBands 20 d L band).product
    (paritySourceB509SkipEndpointSupport434
      (Q := sourceActualSortedQ 20 d L band slot) δ)

/-- Literal HISTORICAL Parity(4.8) H(t) source convolution at fixed
B590 δ,ξ and original reserved Q slot, with its reserved prime
character `p^(iσ)` and genuine native B509 skipped-Q residual c_r.
The integer t is the exact reserved-prime×skipped-product `p*r`,
which is the manuscript's v_* before original P-part is attached.
The native residual includes the original 20! factorial normalizer.
This is a precise source definition, not yet the complete a_v(v). -/
def parityOriginalReservedH434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ)
    (t : ℕ) : ℂ :=
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
  sourceEndpointFibre (parityOriginalReservedHCarrier434 d L band slot δ)
    (fun a : ℕ × ℕ => a.1*a.2)
    (fun a => (sourceOriginalPureMellinPhase434 σ a.1) * F.residual a.2) t

/-- EXACT historical double-sum shape Parity(4.8):
H(t)=sum_{p in actual reserved Q band} sum_{r in actual native
skipped Q endpoint support, p*r=t} p^(iσ)c_r.
No support/factorial source replacements and no exceptional omitted
reserved prime. -/
theorem parity_original_reserved_H_literal_prime_convolution434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ)
    (t : ℕ) :
    parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ t =
      ∑ p ∈ sourceOriginalQActualBands 20 d L band,
        ∑ r ∈ paritySourceB509SkipEndpointSupport434
          (Q := sourceActualSortedQ 20 d L band slot) δ,
          if p*r=t then
            sourceOriginalPureMellinPhase434 σ p *
              (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).residual r
          else 0 := by
  unfold parityOriginalReservedH434 sourceEndpointFibre
    parityOriginalReservedHCarrier434
  rw [Finset.sum_filter]
  exact Finset.sum_product _ _ _

/-- The genuinely reserved Parity(4.8) H support is the EXACT set of
products p*r with p in original reserved Q band and r in the native
skipped-Q support; no material from the physical P-part is absorbed. -/
def parityOriginalReservedHSupport434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) :
    Finset ℕ := (parityOriginalReservedHCarrier434 d L band slot δ).image
      (fun a : ℕ × ℕ => a.1*a.2)

/-- Original Parity(4.8) finite reserved-prime convolution is exactly
mass-preserving under product-endpoint reindexing. This binds the
native c_r factorial source to the literal H(v*) coefficient. -/
theorem parity_original_reserved_H_sum_over_support_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ) :
    (∑ t ∈ parityOriginalReservedHSupport434 d L band slot δ,
      parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ t) =
      ∑ p ∈ sourceOriginalQActualBands 20 d L band,
        ∑ r ∈ paritySourceB509SkipEndpointSupport434
          (Q := sourceActualSortedQ 20 d L band slot) δ,
          sourceOriginalPureMellinPhase434 σ p *
            (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).residual r := by
  let S := parityOriginalReservedHCarrier434 d L band slot δ
  let g : ℕ × ℕ → ℕ := fun a => a.1*a.2
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
  let w : ℕ × ℕ → ℂ := fun a =>
    sourceOriginalPureMellinPhase434 σ a.1 * F.residual a.2
  have h := Finset.sum_image' (s := S) (g := g)
    (f := fun t => sourceEndpointFibre S g w t) w
    (by intro a ha; rfl)
  change (∑ t ∈ S.image g, sourceEndpointFibre S g w t) = _
  rw [h]
  unfold S parityOriginalReservedHCarrier434
  exact Finset.sum_product _ _ _
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHDivisor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Every ACTUAL original reserved-prime/skipped-Q pair `p*r=t` maps
to a DISTINCT ordinary divisor p of t, because t>0 ensures p>0,
and for a given p the partner r is unique. This source combinatorial
bound requires no hypothetical prime uniqueness or Q-band disjointness:
even repeated source labels are handled by their endpoint set. -/
theorem parity_original_reserved_H_fibre_card_le_tau434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (t : ℕ) (ht : 0 < t) :
    ((parityOriginalReservedHCarrier434 d L band slot δ).filter
      (fun a : ℕ×ℕ => a.1*a.2=t)).card ≤ t.divisors.card := by
  let S := (parityOriginalReservedHCarrier434 d L band slot δ).filter
    (fun a : ℕ×ℕ => a.1*a.2=t)
  apply Finset.card_le_card_of_injOn (fun a : ℕ×ℕ => a.1)
  · intro a ha
    have hh : a.1*a.2=t := (Finset.mem_filter.mp ha).2
    exact Nat.mem_divisors.mpr ⟨⟨a.2,hh.symm⟩,by omega⟩
  · intro a ha b hb hab
    change a.1 = b.1 at hab
    have haEq : a.1*a.2=t := (Finset.mem_filter.mp ha).2
    have hbEq : b.1*b.2=t := (Finset.mem_filter.mp hb).2
    have hpa : 0 < a.1 := by
      by_contra h
      have hz : a.1=0 := Nat.eq_zero_of_not_pos h
      rw [hz,zero_mul] at haEq
      omega
    have hsecond : a.2=b.2 := Nat.mul_left_cancel hpa (by
      calc
        a.1*a.2 = t := haEq
        _ = b.1*b.2 := hbEq.symm
        _ = a.1*b.2 := by rw [hab])
    exact Prod.ext hab hsecond

/-- EACH true original Parity(4.8) physical reserved-prime coefficient
`p^(iσ)*nativeResidual(r)` has complex norm at most one. The p phase
is exactly imaginary and native factorial QSkip residual has its
independent verified collision-cancellation bound. -/
theorem parity_original_reserved_H_pair_weight_norm_le_one434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ)
    (a : ℕ×ℕ) :
    ‖sourceOriginalPureMellinPhase434 σ a.1 *
      (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).residual a.2‖ ≤ 1 := by
  rw [norm_mul,source_original_pure_mellin_phase_norm_one434,one_mul]
  exact parity_original_B509_native_residual_actual_norm_le_one434
    d L hL band slot δ ξ K alpha q χ σ₀ σ₁ a.2

/-- Complete TRUE original Parity(4.9) coefficient bound on the actual
reserved-prime convolution H(v*), with no LOSS of the Q-band CARDINALITY:
for each t>0, `|H(t)| ≤ τ(t)`. The proof is independent of K0 and
Fourier precision; it uses EXACT true reserved-prime × native skipped-Q
product gating and the physical factorial source residual bound ≤1.
This is a real historical H-side arithmetic bound, but full a_v(v)
still needs the remaining original P-part/W1/parity physical identity. -/
theorem parity_original_reserved_H_norm_le_divisor_count434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ)
    (t : ℕ) (ht : 0 < t) :
    ‖parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ t‖ ≤
      (t.divisors.card:ℝ) := by
  let S := (parityOriginalReservedHCarrier434 d L band slot δ).filter
    (fun a : ℕ×ℕ => a.1*a.2=t)
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
  let w : ℕ×ℕ → ℂ := fun a => sourceOriginalPureMellinPhase434 σ a.1 * F.residual a.2
  have hweights (a : ℕ×ℕ) (ha : a∈S) : ‖w a‖ ≤ 1 :=
    parity_original_reserved_H_pair_weight_norm_le_one434
      d L hL band slot δ ξ K alpha q χ σ₀ σ₁ σ a
  have hcard : S.card ≤ t.divisors.card :=
    parity_original_reserved_H_fibre_card_le_tau434 d L band slot δ t ht
  unfold parityOriginalReservedH434 sourceEndpointFibre
  change ‖∑ a ∈ S, w a‖ ≤ (t.divisors.card:ℝ)
  calc
    _ ≤ ∑ a ∈ S, ‖w a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ S, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact hweights a ha
    _ = (S.card:ℝ) := by simp
    _ ≤ (t.divisors.card:ℝ) := by exact_mod_cast hcard
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHPhysicalVStar -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15500000

/-- The literal physical v_* underlying historical Parity(4.8) is
precisely the ORIGINAL reserved Q prime p times ALL skipped original
Q primes, without the multiplicity-counted P-part.
All actual Q prime labels and reserved band/slot are preserved. -/
def parityOriginalPhysicalVStar434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) : ℕ :=
  (f band slot).val * paritySourceOrderedAllocatedV434 δ
    (parityActualSourceRemainingFullQTuple434 d L band slot f)

/-- Every TRUE original physical v_*=p*skippedQ belongs to the
literal reserved-prime native H-support. This is not an inferred
independent endpoint: its p is the actual reserved Q-band entry of
the labelled source tuple and its r is the native skipped-Q product. -/
theorem parity_original_actual_vstar_in_reserved_H_support434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) :
    parityOriginalPhysicalVStar434 d L band slot f δ ∈
      parityOriginalReservedHSupport434 d L band slot δ := by
  unfold parityOriginalReservedHSupport434
  apply Finset.mem_image.mpr
  let p := parityActualSourceRemainingFullQTuple434 d L band slot f
  let r := paritySourceOrderedAllocatedV434 δ p
  refine ⟨((f band slot).val,r),?_,rfl⟩
  unfold parityOriginalReservedHCarrier434
  apply Finset.mem_product.mpr
  constructor
  · exact (f band slot).property
  · unfold paritySourceB509SkipEndpointSupport434
    apply Finset.mem_image.mpr
    refine ⟨(fun i : {i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length // ¬δ i = true} => p i.val),?_,rfl⟩
    exact Finset.mem_univ _

/-- The same complete original source h=-2 physical v decomposes
EXACTLY as `v = v_* * Ppart(u)` (with the original reserved p and all
unselected Q primes in v_*), and `u=e*v` at every original Q-product
gate. This is a SOURCE equality of natural integers, not a cofactor
assumption or an altered definition of Ω. -/
theorem parity_original_actual_vstar_Ppart_and_e_v_exact434
    (d : ℕ) (L : ℝ) (u : ℕ) (hu : u ≠ 0)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (hf : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) :
    let e := paritySourceOrderedAllocatedE434 δ
      (parityActualSourceRemainingFullQTuple434 d L band slot f)
    let vStar := parityOriginalPhysicalVStar434 d L band slot f δ
    let v := vStar * sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
    e*v = u ∧ vStar ∈ parityOriginalReservedHSupport434 d L band slot δ := by
  dsimp only
  have hEV := parity_actual_original_A_labelled_allocated_ev_exact434
    d L u hu f hf band slot δ
  exact ⟨hEV,parity_original_actual_vstar_in_reserved_H_support434
    d L band slot f δ⟩

/-- The ACTUAL original W1(P,u) and odd Ω_P projector transfer
EXACTLY onto the physical v=v_*×Ppart with the reserved H-prime
remaining part of v_*. This carries the unmodified parity projector
and all prime multiplicities into the historic v-side. -/
theorem parity_original_actual_vstar_Ppart_W1_odd_projector_transfer434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (hf : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → Bool) :
    let P := sourceOriginalPAllActualBands 20 L
    let vStar := parityOriginalPhysicalVStar434 d L band slot f δ
    let v := vStar * sourceOriginalPPrimePart (Finset.univ.biUnion P) u
    sourceOriginalW1 P u *
      ((1-(-1:ℝ)^sourceOriginalPParityExponent (Finset.univ.biUnion P) u)/2) =
    sourceOriginalW1 P v *
      ((1-(-1:ℝ)^sourceOriginalPParityExponent (Finset.univ.biUnion P) v)/2) := by
  dsimp only
  exact parity_actual_original_A_labelled_W1_projector_transfer434
    d L hL hd u hu f hf band slot δ
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHPhysicalWeight -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15500000

/-- TRUE multiplicity-counted original P-parity projector: zero on
even Ω_P(v), one on odd Ω_P(v). No substitution of Liouville sign
for the source odd-projector. -/
theorem parity_original_P_parity_projector_between_zero_one434 (n : ℕ) :
    0 ≤ ((1-(-1:ℝ)^n)/2) ∧ ((1-(-1:ℝ)^n)/2) ≤ 1 := by
  rcases neg_one_pow_eq_or ℝ n with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

/-- The genuine source physical v-side Parity(4.7),(4.8) component,
keeping the ACTUAL original P-multiplicity odd projector and W1(v)
separate from the reserved-Q convolution `H(v_*)`.
The original imaginary power `v^{iρ}` has norm 1. The variable vStar
is the actual reserved prime×skipped-Q product, not an arbitrary
unconnected cofactor. This is a SOURCE physical coefficient; its exact
match to historical signed epsilon(v) still requires identifying the
manuscript's parity convention with the original projector. -/
def parityOriginalReservedPhysicalAV434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ ρ : ℝ)
    (vStar v : ℕ) : ℂ :=
  sourceOriginalPureMellinPhase434 ρ v *
    (((sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v *
      ((1-(-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) v)/2)):ℝ):ℂ) *
    parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ vStar

/-- The exact genuine original physical coefficient on v=v_*×Ppart
satisfies Parity(4.9)'s SOURCE H-divisor size with NO reserved-band
cardinality: |a_v(v)|≤W1(P,v) τ(v_*) for v_*>0.
This is a literal bound on the new SOURCE physical H convolution and
original odd projector, not the historically unverified epsilon sign. -/
theorem parity_original_reserved_physical_aV_norm_le_W1_tau434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ ρ : ℝ)
    (vStar v : ℕ) (hvStar : 0 < vStar) :
    ‖parityOriginalReservedPhysicalAV434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ
      vStar v‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v *
        (vStar.divisors.card:ℝ) := by
  let P := sourceOriginalPAllActualBands 20 L
  let W : ℝ := sourceOriginalW1 P v
  let odd : ℝ :=
    ((1-(-1:ℝ)^sourceOriginalPParityExponent (Finset.univ.biUnion P) v)/2)
  have hW : 0 ≤ W := source_original_W1_nonneg P v
  have hOdd := parity_original_P_parity_projector_between_zero_one434
    (sourceOriginalPParityExponent (Finset.univ.biUnion P) v)
  have hH := parity_original_reserved_H_norm_le_divisor_count434
    d L hL band slot δ ξ K alpha q χ σ₀ σ₁ σ vStar hvStar
  have hDiv : (0:ℝ) ≤ (vStar.divisors.card:ℝ) := Nat.cast_nonneg _
  unfold parityOriginalReservedPhysicalAV434
  rw [norm_mul,norm_mul,source_original_pure_mellin_phase_norm_one434,one_mul]
  rw [Complex.norm_real,Real.norm_eq_abs]
  have hProduct : 0 ≤ W*odd := mul_nonneg hW hOdd.1
  rw [abs_of_nonneg hProduct]
  calc
    _ ≤ (W*odd) * (vStar.divisors.card:ℝ) :=
      mul_le_mul_of_nonneg_left hH hProduct
    _ ≤ W * (vStar.divisors.card:ℝ) := by
      have hOddW : W*odd ≤ W := mul_le_of_le_one_right hW hOdd.2
      exact mul_le_mul_of_nonneg_right hOddW hDiv
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHPhysicalFactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The literal original Parity(4.8) reserved-Q p/skip-r source
physical v-side double sum with EXACT product gate p*r=vStar,
source W1(P,v), multiplicity-counted P-parity projector and
imaginary v^(iρ). Factorials stay in the real B509 residual c_r.
Nothing is replaced by an independent Dirichlet-coefficient proxy. -/
def parityOriginalReservedPhysicalSourceDoubleSum434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ ρ : ℝ)
    (vStar v : ℕ) : ℂ :=
  ∑ p ∈ sourceOriginalQActualBands 20 d L band,
    ∑ r ∈ paritySourceB509SkipEndpointSupport434
      (Q := sourceActualSortedQ 20 d L band slot) δ,
      if p*r=vStar then
        (sourceOriginalPureMellinPhase434 ρ v *
          (((sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v *
            ((1-(-1:ℝ)^sourceOriginalPParityExponent
              (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) v)/2)):ℝ):ℂ)) *
          (sourceOriginalPureMellinPhase434 σ p *
            (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).residual r)
      else 0

/-- The actual original 20!-labelled reserved prime × skipped-Q
physical source sum with projector/W1(v) and phase `v^(iρ)` factors
EXACTLY as physical a_v(v)=phase(v)*W1(v)*oddProjector(v)*H(vStar),
where H(vStar) is the TRUE reserved-prime convolution of the native
B509 c_r. This is the literal algebraic Parity(4.7),(4.8) v-side, not
yet the global αβ source full coefficient identity over all Mellin/
Fourier parameters, nor the manuscript's signed epsilon(v) equivalence. -/
theorem parity_original_reserved_physical_double_sum_eq_aV434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ ρ : ℝ)
    (vStar v : ℕ) :
    parityOriginalReservedPhysicalSourceDoubleSum434
      d L band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ vStar v =
    parityOriginalReservedPhysicalAV434
      d L band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ vStar v := by
  let C : ℂ := sourceOriginalPureMellinPhase434 ρ v *
    (((sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v *
      ((1-(-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) v)/2)):ℝ):ℂ)
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
  unfold parityOriginalReservedPhysicalSourceDoubleSum434
    parityOriginalReservedPhysicalAV434
  rw [parity_original_reserved_H_literal_prime_convolution434]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> ring

/-- Complete ORIGINAL v-side coefficient with the native reserved
H convolution admits the expected historical divisor bound after
factorisation, at the true physical cofactor v*=p*skippedQ. -/
theorem parity_original_reserved_physical_double_sum_norm_le_W1_tau434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ ρ : ℝ)
    (vStar v : ℕ) (hv : 0 < vStar) :
    ‖parityOriginalReservedPhysicalSourceDoubleSum434
      d L band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ vStar v‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v *
        (vStar.divisors.card:ℝ) := by
  rw [parity_original_reserved_physical_double_sum_eq_aV434]
  exact parity_original_reserved_physical_aV_norm_le_W1_tau434
    d L hL band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ vStar v hv
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHSkipGate -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- EXACT original B509 factorial-labelled skipped Q-source sum with
reserved p times skip-prime product fixed to t: the same source
quantity after the real endpoint-fibre regrouping into native
`sourceNativePrimeCore.residual` c_r, still subject to `p*r=t`.
No endpoint injection or false uniqueness of Q-prime labellings is
assumed. This is the actual local c_r bridge for Parity(4.8). -/
theorem parity_original_B509_skip_reserved_product_gate_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (p t : ℕ) :
    (∑ b : OrderedQSkip (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length
      (sourceActualSortedQ 20 d L band slot) δ,
      if p*orderedSkipProduct b=t then
        sourceActualSortedFactorial 20 d *
          orderedSkipPhase (sourceActualSortedFrequencyScales 20 d L band slot) ξ b
      else 0) =
    (∑ h ∈ paritySourceB509SkipEndpointSupport434
      (Q := sourceActualSortedQ 20 d L band slot) δ,
      if p*h=t then
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).residual h
      else 0) := by
  let n := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let Q := sourceActualSortedQ 20 d L band slot
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  let S : Finset (OrderedQSkip n Q δ) := Finset.univ
  let g : OrderedQSkip n Q δ → ℕ := orderedSkipProduct
  let base : OrderedQSkip n Q δ → ℂ := fun b =>
    sourceActualSortedFactorial 20 d * orderedSkipPhase s ξ b
  let w : OrderedQSkip n Q δ → ℂ := fun b =>
    if p*g b=t then base b else 0
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
  have hFiber (h : ℕ) : sourceEndpointFibre S g w h =
      if p*h=t then sourceEndpointFibre S g base h else 0 := by
    unfold sourceEndpointFibre
    by_cases hp : p*h=t
    · simp only [if_pos hp]
      apply Finset.sum_congr rfl
      intro b hb
      have hprod : g b=h := (Finset.mem_filter.mp hb).2
      dsimp [w]
      rw [hprod]
      simp [hp]
    · simp only [if_neg hp]
      apply Finset.sum_eq_zero
      intro b hb
      have hprod : g b=h := (Finset.mem_filter.mp hb).2
      dsimp [w]
      rw [hprod]
      simp [hp]
  have hEndpoint := Finset.sum_image' (s := S) (g := g)
    (f := fun h => sourceEndpointFibre S g w h) w (by intro b hb; rfl)
  change (∑ b ∈ S, w b) =
    ∑ h ∈ S.image g, if p*h=t then F.residual h else 0
  rw [←hEndpoint]
  apply Finset.sum_congr rfl
  intro h hh
  rw [hFiber]
  congr 1
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHFixedEVStar -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The literal source ORIGINAL reserved p and all nonreserved Q-labelled
prime slots at FIXED selected e and physical vStar=p*skippedQ. Every
20! factorial, full B509 Fourier phase and exact endpoint conditions
are included. The REAL original reserved-prime factor p^(iσ) occurs
inside this double source sum, not as an independent placeholder. -/
def parityOriginalReservedFullQFixedEVStar434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (σ : ℝ) (e vStar : ℕ) : ℂ :=
  let Q := sourceActualSortedQ 20 d L band slot
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  ∑ p ∈ sourceOriginalQActualBands 20 d L band,
    ∑ rest : ((i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length) →
       {q : ℕ // q ∈ Q i}),
      if paritySourceQSelectedPrimeProduct434 (δ:=δ) (fun i=>rest i.val)=e ∧
          p*orderedSkipProduct (fun i : {i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length // ¬δ i=true} =>
              rest i.val)=vStar then
        sourceOriginalPureMellinPhase434 σ p *
          (sourceActualSortedFactorial 20 d *
            paritySourceFullSlotFourierPhase434 s ξ δ rest)
      else 0

/-- ACTUAL original Parity (4.7)--(4.8) full reserved Q + selected Q +
skipped Q endpoint source factorization at EACH fixed `(e,vStar)`:

`sum_{p, all remaining labelled Q, selectedQ=e, p*skippedQ=vStar}
  p^(iσ) * factorial * fullFourierPhase
 = selected-Q e-Fourier fibre(e) * H(vStar)`.

The H is exactly the native B509 QSkip c_r convolution and retains the
reserved ORIGINAL p∈Q-band. This is a substantive SOURCE equality,
not a definition of the RHS, and includes repeated prime labels.
The subsequent multiplication by original W1/parity and h=-2 αβ is
separate; global Parity(4.7) integration and TypeII remain open. -/
theorem parity_original_reserved_fullQ_fixed_e_vStar_eq_selected_H434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ)
    (e vStar : ℕ) :
    parityOriginalReservedFullQFixedEVStar434 d L band slot δ ξ σ e vStar =
      paritySourceQSelectedFourierEFibre434
        (Q:=sourceActualSortedQ 20 d L band slot) δ
        (sourceActualSortedFrequencyScales 20 d L band slot) ξ e *
      parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ vStar := by
  let Q := sourceActualSortedQ 20 d L band slot
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  let A : paritySourceQSelected434
      (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length Q δ → ℂ :=
    fun a => if paritySourceQSelectedPrimeProduct434 a=e then
      paritySourceQSelectedFourierPhase434 s ξ δ a else 0
  let B : ℕ → OrderedQSkip
      (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length Q δ → ℂ :=
    fun p b => if p*orderedSkipProduct b=vStar then
      sourceActualSortedFactorial 20 d * orderedSkipPhase s ξ b else 0
  have hSel :
      (∑ a : paritySourceQSelected434
        (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length Q δ,
          A a) =
      paritySourceQSelectedFourierEFibre434 (Q:=Q) δ s ξ e := by
    unfold A paritySourceQSelectedFourierEFibre434 sourceEndpointFibre
    rw [Finset.sum_filter]
  have hPerP (p : ℕ) :
      (∑ rest : ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length) →
         {q : ℕ // q ∈ Q i}),
        if paritySourceQSelectedPrimeProduct434 (δ:=δ) (fun i=>rest i.val)=e ∧
            p*orderedSkipProduct (fun i : {i : Fin (sourceOrderedLabels 20
              (sourceActualSortedScales 20 d L) band slot).length // ¬δ i=true} =>
              rest i.val)=vStar then
          sourceOriginalPureMellinPhase434 σ p *
            (sourceActualSortedFactorial 20 d *
              paritySourceFullSlotFourierPhase434 s ξ δ rest)
        else 0) =
       sourceOriginalPureMellinPhase434 σ p *
         ((∑ a : paritySourceQSelected434
           (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length Q δ,
           A a) *
          (∑ b : OrderedQSkip
           (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length Q δ,
           B p b)) := by
    have hSplit := parity_source_Q_full_factor_selected_skipped434 Q δ A (B p)
    calc
      _ = sourceOriginalPureMellinPhase434 σ p *
            (∑ rest : ((i : Fin (sourceOrderedLabels 20
              (sourceActualSortedScales 20 d L) band slot).length) →
                {q : ℕ // q ∈ Q i}),
              A (fun i=>rest i.val) * B p (fun i=>rest i.val)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro rest hrest
          by_cases he : paritySourceQSelectedPrimeProduct434 (δ:=δ)
              (fun i=>rest i.val)=e
          · by_cases hv : p*orderedSkipProduct
                (fun i : {i : Fin (sourceOrderedLabels 20
                (sourceActualSortedScales 20 d L) band slot).length // ¬δ i=true} =>
                rest i.val)=vStar
            · simp only [he,hv,and_self,ite_true]
              dsimp [A,B]
              rw [if_pos he,if_pos hv,
                parity_source_full_fourier_factorial_as_selected_skip434]
            · simp [A,B,he,hv]
          · simp [A,B,he]
      _ = _ := by rw [hSplit]
  have hSkip (p : ℕ) :
      (∑ b : OrderedQSkip
        (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length Q δ,
        B p b) =
      ∑ h ∈ paritySourceB509SkipEndpointSupport434 (Q:=Q) δ,
        if p*h=vStar then
          (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).residual h
        else 0 :=
    parity_original_B509_skip_reserved_product_gate_exact434
      d L band slot δ ξ K alpha q χ σ₀ σ₁ p vStar
  have hOuter : parityOriginalReservedFullQFixedEVStar434 d L band slot δ ξ σ e vStar =
      ∑ p ∈ sourceOriginalQActualBands 20 d L band,
        sourceOriginalPureMellinPhase434 σ p *
        ((∑ a : paritySourceQSelected434
          (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length Q δ,
          A a) *
         (∑ b : OrderedQSkip
          (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length Q δ,
          B p b)) := by
    unfold parityOriginalReservedFullQFixedEVStar434
    apply Finset.sum_congr rfl
    intro p hp
    exact hPerP p
  rw [hOuter]
  simp_rw [hSel]
  calc
    (∑ p ∈ sourceOriginalQActualBands 20 d L band,
      sourceOriginalPureMellinPhase434 σ p *
        (paritySourceQSelectedFourierEFibre434 (Q:=Q) δ s ξ e *
          ∑ b : OrderedQSkip
             (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length Q δ,
             B p b)) =
      paritySourceQSelectedFourierEFibre434 (Q:=Q) δ s ξ e *
        (∑ p ∈ sourceOriginalQActualBands 20 d L band,
          sourceOriginalPureMellinPhase434 σ p *
            (∑ b : OrderedQSkip
              (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length Q δ,
               B p b)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = paritySourceQSelectedFourierEFibre434 (Q:=Q) δ s ξ e *
          parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ vStar := by
          congr 1
          simp_rw [hSkip]
          rw [parity_original_reserved_H_literal_prime_convolution434]
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h hh
          split_ifs <;> ring
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedFullQPhysicalFactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The complete original reserved-p/all-Q source at fixed e,vStar,
with the original physical P-part W1 and odd multiplicity projector
ON THE v SIDE, and exact imaginary v^(iρ) Fourier-Mellin phase.
The underlying Q sum is the literal original full prime-labelling
not a coefficient proxy; v=vStar*Ppart(u) is the real physical integer.
This object still needs equality with the entire unrestricted
sourceOriginalA h=-2 bilinear after all Ψ/Fourier/Mellin integrations. -/
def parityOriginalReservedFullQPhysicalFixedEVStar434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (σ ρ : ℝ) (e vStar : ℕ) : ℂ :=
  let P := sourceOriginalPAllActualBands 20 L
  let v := vStar * sourceOriginalPPrimePart (Finset.univ.biUnion P) u
  parityOriginalReservedFullQFixedEVStar434 d L band slot δ ξ σ e vStar *
    (sourceOriginalPureMellinPhase434 ρ v *
      (((sourceOriginalW1 P v *
        ((1-(-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion P) v)/2)):ℝ):ℂ))

/-- The ACTUAL complete original reserved-p, selected and skipped Q
coefficient at fixed physical e,vStar, with literal source parity/W1,
factors as original selected e-Fourier fibre × real historical
reserved-Q physical a_v(v)=v^(iρ)W1(v)oddProjector(v)H(vStar).
This is a SOURCE algebraic equality at fixed B590 δ,ξ and Mellin σ,ρ,
with factorials included once in native c_r. No `epsilon(v)=oddProjector`
assertion is made; parity transfer to v for actual source rows was
independently proved by `parity_actual_original_A_labelled_...transfer434`. -/
theorem parity_original_reserved_fullQ_physical_fixed_e_vStar_factor434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ ρ : ℝ)
    (e vStar : ℕ) :
    parityOriginalReservedFullQPhysicalFixedEVStar434
      d L u band slot δ ξ σ ρ e vStar =
    paritySourceQSelectedFourierEFibre434
      (Q:=sourceActualSortedQ 20 d L band slot) δ
      (sourceActualSortedFrequencyScales 20 d L band slot) ξ e *
    parityOriginalReservedPhysicalAV434
      d L band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ vStar
      (vStar * sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) := by
  unfold parityOriginalReservedFullQPhysicalFixedEVStar434
    parityOriginalReservedPhysicalAV434
  rw [parity_original_reserved_fullQ_fixed_e_vStar_eq_selected_H434
    d L band slot δ ξ K alpha q χ σ₀ σ₁ σ e vStar]
  ring

/-- Source Parity(4.9) full selected-e Fourier fibre × honest physical
H(vStar) W1/parity coefficient has the unconditional pointwise
bound `(20!)^(d+1)*W1(P,v)*τ(vStar)` on positive vStar.
No K0-dependent constant or artificial independent v-side residual. -/
theorem parity_original_reserved_fullQ_physical_fixed_e_vStar_norm_bound434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (u : ℕ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ ρ : ℝ)
    (e vStar : ℕ) (hvStar : 0 < vStar) :
    ‖parityOriginalReservedFullQPhysicalFixedEVStar434
      d L u band slot δ ξ σ ρ e vStar‖ ≤
      (((20:ℕ).factorial:ℝ)^(d+1)) *
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L)
        (vStar * sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) *
      (vStar.divisors.card:ℝ) := by
  rw [parity_original_reserved_fullQ_physical_fixed_e_vStar_factor434
    d L u band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ e vStar]
  rw [norm_mul]
  have hA := parity_actual_source_selected_fourier_e_fibre_norm_le_factorials434
    20 d L (by omega) hL band slot δ ξ e
  have hV := parity_original_reserved_physical_aV_norm_le_W1_tau434
    d L hL band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ vStar
    (vStar * sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) hvStar
  have hV0 : 0 ≤ ‖parityOriginalReservedPhysicalAV434
      d L band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ vStar
      (vStar * sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)‖ := norm_nonneg _
  have hR : 0 ≤ (((20:ℕ).factorial:ℝ)^(d+1)) := by positivity
  calc
    _ ≤ (((20:ℕ).factorial:ℝ)^(d+1)) *
      ‖parityOriginalReservedPhysicalAV434
        d L band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ vStar
        (vStar * sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)‖ :=
      mul_le_mul_of_nonneg_right hA hV0
    _ ≤ (((20:ℕ).factorial:ℝ)^(d+1)) *
      (sourceOriginalW1 (sourceOriginalPAllActualBands 20 L)
        (vStar * sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) *
        (vStar.divisors.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hV hR
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHGlobalFibre -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- True two-integer endpoint fibre, preserving original labelled Q
multiplicity. Unlike `sourceEndpointFibre` (which targets Nat), this
canonical finite fibre targets actual `(selected e, physical vStar)`
and makes no assumption of endpoint injectivity. -/
def parityOriginalReservedTwoEndpointFibre434
    {α : Type} [DecidableEq α]
    (S : Finset α) (g : α → ℕ×ℕ) (w : α → ℂ)
    (z : ℕ×ℕ) : ℂ :=
  ∑ a ∈ S.filter (fun a => g a = z), w a

/-- Literal selected-Q product coincides with actual source B590
`allocatedE` for every full nonreserved labelled Q tuple and Boolean
assignment, without any distinct-prime assumption. -/
theorem parity_original_ordered_allocated_e_eq_selected_Q_product434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (δ : Fin n → Bool)
    (rest : (i : Fin n) → {q : ℕ // q ∈ Q i}) :
    paritySourceOrderedAllocatedE434 δ rest =
      paritySourceQSelectedPrimeProduct434 (δ:=δ) (fun i => rest i.val) := by
  unfold paritySourceOrderedAllocatedE434 paritySourceQSelectedPrimeProduct434
  rw [←Finset.prod_filter]
  exact (Finset.prod_subtype
    (s := Finset.univ.filter (fun i : Fin n => δ i = true))
    (p := fun i : Fin n => δ i = true)
    (by intro i; simp)
    (fun i => (rest i).val))

/-- The ACTUAL source Q support of original Parity(4.7) fixed
`(e,vStar)`, obtained by applying the two product maps to the
REAL ORIGINAL reserved prime + entire nonreserved labelled Q tuple.
Repeated labels are retained in its preimage; support is an image
Finset, not an invented rectangular independent range. -/
def parityOriginalReservedFullQEVStarSupport434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) :
    Finset (ℕ×ℕ) :=
  let n := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
    band slot).length
  let Q := sourceActualSortedQ 20 d L band slot
  (Finset.univ : Finset
    ({p : ℕ // p ∈ sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin n) → {q : ℕ // q ∈ Q i}))).image
    (fun a =>
      (paritySourceOrderedAllocatedE434 δ a.2,
       a.1.val*paritySourceOrderedAllocatedV434 δ a.2))

/-- Every genuine original full Q tuple contributing to the source
`(e,vStar)` endpoint satisfies the exact partition of its complete
prime product: `p*prod rest=e*vStar`, including its reserved Q prime. -/
theorem parity_original_reserved_Q_product_eq_e_times_vStar434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (δ : Fin n → Bool) (p : ℕ)
    (rest : (i : Fin n) → {q : ℕ // q∈Q i}) :
    p*(∏ i, (rest i).val) =
      (paritySourceOrderedAllocatedE434 δ rest) *
        (p*paritySourceOrderedAllocatedV434 δ rest) := by
  rw [←parity_source_ordered_allocation_partition434 δ rest]
  ac_rfl

/-- The literal original full reserved-Q + all nonreserved-Q source
finite Fourier sum at fixed (e,vStar) is EXACTLY the endpoint fibre
of the real labelled Q pairs under `(selectedProduct, p*skipProduct)`.
The full original 20! factorial and B509 Fourier phases are carried
inside the true fibre. No Q-label injectivity is postulated. -/
theorem parity_original_reserved_fullQ_fixed_e_vStar_eq_endpoint_fibre434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (σ : ℝ) (e vStar : ℕ) :
    let n := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length
    let Q := sourceActualSortedQ 20 d L band slot
    let S : Finset ({p : ℕ // p ∈ sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin n) → {q : ℕ // q ∈ Q i})) := Finset.univ
    let g := fun a : {p : ℕ // p ∈ sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin n) → {q : ℕ // q ∈ Q i}) =>
      (paritySourceOrderedAllocatedE434 δ a.2,
       a.1.val*paritySourceOrderedAllocatedV434 δ a.2)
    let w := fun a : {p : ℕ // p ∈ sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin n) → {q : ℕ // q ∈ Q i}) =>
      sourceOriginalPureMellinPhase434 σ a.1.val *
        (sourceActualSortedFactorial 20 d *
          paritySourceFullSlotFourierPhase434
            (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ a.2)
    parityOriginalReservedFullQFixedEVStar434 d L band slot δ ξ σ e vStar =
      parityOriginalReservedTwoEndpointFibre434 S g w (e,vStar) := by
  dsimp only
  unfold parityOriginalReservedFullQFixedEVStar434 parityOriginalReservedTwoEndpointFibre434
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_subtype (sourceOriginalQActualBands 20 d L band)
    (by intro p; rfl)]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro rest hrest
  have hPair :
      (paritySourceOrderedAllocatedE434 δ rest,
        p.val*paritySourceOrderedAllocatedV434 δ rest) = (e,vStar) ↔
      paritySourceQSelectedPrimeProduct434 (δ:=δ)
        (fun i => rest i.val)=e ∧
      p.val*orderedSkipProduct
        (fun i : {i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length // ¬δ i=true} =>
          rest i.val)=vStar := by
    simp only [Prod.mk.injEq]
    rw [parity_original_ordered_allocated_e_eq_selected_Q_product434]
    rfl
  by_cases h : (paritySourceOrderedAllocatedE434 δ rest,
      p.val*paritySourceOrderedAllocatedV434 δ rest) = (e,vStar)
  · simp only [if_pos h, hPair.mp h]
    rfl
  · simp only [if_neg h, not_and]
    rw [if_neg (by intro hh; exact h (hPair.mpr hh))]

/-- Literal mass-preserving source reindex: summing original
full-Q reserved-prime prime powers and full Fourier phases over ALL
`(e,vStar)` endpoints yields exactly the sum over ALL actual
reserved p and labelled nonreserved Q tuples, with no missing or
extra factorial. In conjunction with fixed-e×H factorisation,
this is the precise finite source core of Parity(4.7) before the
original Ppart and Fourier/Mellin integrals are joined. -/
theorem parity_original_reserved_fullQ_all_e_vStar_fibre_mass_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (σ : ℝ) :
    (∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
       parityOriginalReservedFullQFixedEVStar434 d L band slot δ ξ σ z.1 z.2) =
      ∑ p ∈ sourceOriginalQActualBands 20 d L band,
        ∑ rest : ((i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length) →
          {q : ℕ // q∈sourceActualSortedQ 20 d L band slot i}),
          sourceOriginalPureMellinPhase434 σ p *
            (sourceActualSortedFactorial 20 d *
              paritySourceFullSlotFourierPhase434
                (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ rest) := by
  let n := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
    band slot).length
  let Q := sourceActualSortedQ 20 d L band slot
  let S : Finset ({p : ℕ // p ∈ sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin n) → {q : ℕ // q∈Q i})) := Finset.univ
  let g : ({p : ℕ // p ∈ sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin n) → {q : ℕ // q∈Q i})) → ℕ×ℕ :=
      fun a => (paritySourceOrderedAllocatedE434 δ a.2,
          a.1.val*paritySourceOrderedAllocatedV434 δ a.2)
  let w : ({p : ℕ // p ∈ sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin n) → {q : ℕ // q∈Q i})) → ℂ :=
      fun a => sourceOriginalPureMellinPhase434 σ a.1.val *
        (sourceActualSortedFactorial 20 d *
          paritySourceFullSlotFourierPhase434
            (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ a.2)
  have hImage := Finset.sum_image' (s:=S) (g:=g)
    (f:=fun z => parityOriginalReservedTwoEndpointFibre434 S g w z) w (by intro a ha; rfl)
  have hFixed (z : ℕ×ℕ) :
      parityOriginalReservedFullQFixedEVStar434 d L band slot δ ξ σ z.1 z.2 =
      parityOriginalReservedTwoEndpointFibre434 S g w z :=
    parity_original_reserved_fullQ_fixed_e_vStar_eq_endpoint_fibre434
      d L band slot δ ξ σ z.1 z.2
  unfold parityOriginalReservedFullQEVStarSupport434
  simp_rw [hFixed]
  rw [hImage]
  change (∑ a ∈ S, w a) = _
  unfold S
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_subtype (sourceOriginalQActualBands 20 d L band)
    (by intro p; rfl)]
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHGlobalFactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- TRUE original Parity §4.2 Q-prime coefficient factorization after
summing over ALL PHYSICAL `(e,vStar)` endpoints, not just a single
e/vStar: the ACTUAL original one reserved band-prime and all
nonreserved 20!-labelled Q tuples, with full factorial and B509
Fourier phase, equal the source selected-e coefficient times literal
reserved-prime/native-skipped-Q convolution H(vStar), summed over the
exact finite original source endpoint image. No fake independent
rectangular prime supports or cardinality loss. This proves the
ENTIRE finite Q coefficient source algebra of (4.7)--(4.8), before
Mellin/B590 Fourier integration and the physical W1/parity/h=-2 join. -/
theorem parity_original_reserved_fullQ_global_e_vStar_factor434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ) :
    (∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
       paritySourceQSelectedFourierEFibre434
         (Q:=sourceActualSortedQ 20 d L band slot) δ
         (sourceActualSortedFrequencyScales 20 d L band slot) ξ z.1 *
       parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ z.2) =
      ∑ p ∈ sourceOriginalQActualBands 20 d L band,
        ∑ rest : ((i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length) →
          {q : ℕ // q∈sourceActualSortedQ 20 d L band slot i}),
          sourceOriginalPureMellinPhase434 σ p *
            (sourceActualSortedFactorial 20 d *
              paritySourceFullSlotFourierPhase434
                (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ rest) := by
  rw [←parity_original_reserved_fullQ_all_e_vStar_fibre_mass_exact434]
  apply Finset.sum_congr rfl
  intro z hz
  exact (parity_original_reserved_fullQ_fixed_e_vStar_eq_selected_H434
    d L band slot δ ξ K alpha q χ σ₀ σ₁ σ z.1 z.2).symm

/-- Original f0/f1 SOURCE Fourier gate product and global E-character
multiply the exact original complete reserved-Q×all-Q source algebra;
after extracting those true frequency factors, the coefficient
containing selected integer e is precisely the native selected-only
`parityOriginalSelectedEGateFourierCoefficient434` and the physical
vStar factor is exactly Parity(4.8) original H(vStar). This is a genuine
fixed-frequency original source equality across ALL e and vStar. -/
theorem parity_original_reserved_fullQ_global_gate_selected_H_factor434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ) :
    (∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      parityOriginalSelectedEGateFourierCoefficient434 d L E band slot δ ξ z.1 *
      parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ z.2) =
    ((∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
      ((Real.fourierChar (Real.log E *
        (∑ i, ξ i/sourceActualSortedFrequencyScales 20 d L band slot i)) : Circle):ℂ)) *
    (∑ p ∈ sourceOriginalQActualBands 20 d L band,
      ∑ rest : ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length) →
          {q : ℕ // q∈sourceActualSortedQ 20 d L band slot i}),
        sourceOriginalPureMellinPhase434 σ p *
          (sourceActualSortedFactorial 20 d *
            paritySourceFullSlotFourierPhase434
              (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ rest)) := by
  let C : ℂ := ((∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
      ((Real.fourierChar (Real.log E *
        (∑ i, ξ i/sourceActualSortedFrequencyScales 20 d L band slot i)) : Circle):ℂ))
  have hBase := parity_original_reserved_fullQ_global_e_vStar_factor434
    d L band slot δ ξ K alpha q χ σ₀ σ₁ σ
  unfold parityOriginalSelectedEGateFourierCoefficient434
  change (∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      (C*paritySourceQSelectedFourierEFibre434
        (Q:=sourceActualSortedQ 20 d L band slot) δ
        (sourceActualSortedFrequencyScales 20 d L band slot) ξ z.1) *
      parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ z.2) = _
  calc
    _ = C * (∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      paritySourceQSelectedFourierEFibre434
        (Q:=sourceActualSortedQ 20 d L band slot) δ
        (sourceActualSortedFrequencyScales 20 d L band slot) ξ z.1 *
      parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ z.2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        ring
    _ = _ := by rw [hBase]
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHProductGate -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- ORIGINAL physically supported reserved-p + full Q Fourier
coefficient at integer u with the COMPLETE source Q-product gate
`p*prod(nonreserved labelled Q)=ordinaryPart(P,u)`. No other
coefficients or original factorials are modified. -/
def parityOriginalReservedFullQPhysicalProductGate434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (σ : ℝ) (u : ℕ) : ℂ :=
  ∑ p ∈ sourceOriginalQActualBands 20 d L band,
    ∑ rest : ((i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length) →
      {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i}),
      if p*(∏ i, (rest i).val)=
          sourceOriginalOrdinaryPart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        sourceOriginalPureMellinPhase434 σ p *
          (sourceActualSortedFactorial 20 d *
            paritySourceFullSlotFourierPhase434
              (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ rest)
      else 0

/-- EXACT original Parity(4.7),(4.8) full Q-prime source with its
original real Q-product=u/Ppart condition factors at fixed u into the
TRUE joint endpoint `(e,vStar)` with `e*vStar=ordinaryPart(P,u)`:

`sum_{reserved p, labelled nonreserved Q : q*prod(rest)=ordinaryPart(u)}
  p^(iσ) factorial fullFourierPhase
 =sum_{(e,vStar):e*vStar=ordinaryPart(u)}
   selectedQ_Fourier_e(e) * H(vStar)`.

Every source Q band, reserved prime, factorial and Fourier character
is retained. The summation carrier is the REAL image of the original
reserved-p and remaining-Q tuple. This closes the ORIGINAL Q-product
support gate at fixed u without assuming e and vStar independent.
Original Pparity/W1 and h=-2 αβ incorporation and subsequent actual
multi-frequency Fourier/Mellin integration remain separate. -/
theorem parity_original_reserved_fullQ_product_gate_eq_selected_H434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ)
    (u : ℕ) :
    parityOriginalReservedFullQPhysicalProductGate434 d L band slot δ ξ σ u =
      ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
        if z.1*z.2 = sourceOriginalOrdinaryPart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
          paritySourceQSelectedFourierEFibre434
            (Q:=sourceActualSortedQ 20 d L band slot) δ
            (sourceActualSortedFrequencyScales 20 d L band slot) ξ z.1 *
          parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ z.2
        else 0 := by
  let n := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
    band slot).length
  let Q := sourceActualSortedQ 20 d L band slot
  let P := sourceOriginalPAllActualBands 20 L
  let target := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u
  let S : Finset ({p : ℕ // p∈sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin n) → {q : ℕ // q∈Q i})) := Finset.univ
  let g : ({p : ℕ // p∈sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin n) → {q : ℕ // q∈Q i})) → ℕ×ℕ :=
    fun a => (paritySourceOrderedAllocatedE434 δ a.2,
      a.1.val * paritySourceOrderedAllocatedV434 δ a.2)
  let w : ({p : ℕ // p∈sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin n) → {q : ℕ // q∈Q i})) → ℂ :=
    fun a => sourceOriginalPureMellinPhase434 σ a.1.val *
      (sourceActualSortedFactorial 20 d *
        paritySourceFullSlotFourierPhase434
          (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ a.2)
  let wGate : ({p : ℕ // p∈sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin n) → {q : ℕ // q∈Q i})) → ℂ :=
    fun a => if (g a).1*(g a).2=target then w a else 0
  have hFiber (z : ℕ×ℕ) :
      parityOriginalReservedTwoEndpointFibre434 S g wGate z =
      if z.1*z.2=target then
        parityOriginalReservedTwoEndpointFibre434 S g w z else 0 := by
    unfold parityOriginalReservedTwoEndpointFibre434
    by_cases hg : z.1*z.2=target
    · simp only [if_pos hg]
      apply Finset.sum_congr rfl
      intro a ha
      have hEq : g a=z := (Finset.mem_filter.mp ha).2
      dsimp [wGate]
      rw [hEq]
      simp only [if_pos hg]
    · simp only [if_neg hg]
      apply Finset.sum_eq_zero
      intro a ha
      have hEq : g a=z := (Finset.mem_filter.mp ha).2
      dsimp [wGate]
      rw [hEq]
      simp only [if_neg hg]
  have hImage := Finset.sum_image' (s:=S) (g:=g)
    (f:=fun z => parityOriginalReservedTwoEndpointFibre434 S g wGate z)
    wGate (by intro a ha; rfl)
  have hFixed (z : ℕ×ℕ) :
      parityOriginalReservedFullQFixedEVStar434 d L band slot δ ξ σ z.1 z.2 =
        parityOriginalReservedTwoEndpointFibre434 S g w z :=
    parity_original_reserved_fullQ_fixed_e_vStar_eq_endpoint_fibre434
      d L band slot δ ξ σ z.1 z.2
  have hProduct (a : {p : ℕ // p∈sourceOriginalQActualBands 20 d L band} ×
      ((i : Fin n) → {q : ℕ // q∈Q i})) :
      (g a).1*(g a).2 = a.1.val*(∏ i, (a.2 i).val) := by
    exact (parity_original_reserved_Q_product_eq_e_times_vStar434
      δ a.1.val a.2).symm
  have hGateSum :
      (∑ a ∈ S, wGate a) =
      parityOriginalReservedFullQPhysicalProductGate434 d L band slot δ ξ σ u := by
    unfold S parityOriginalReservedFullQPhysicalProductGate434
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_subtype (sourceOriginalQActualBands 20 d L band)
      (by intro p; rfl)]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro rest hr
    unfold wGate
    rw [hProduct (p,rest)]
  rw [←hGateSum]
  unfold parityOriginalReservedFullQEVStarSupport434
  calc
    (∑ a ∈ S, wGate a) =
      ∑ z ∈ S.image g,
        parityOriginalReservedTwoEndpointFibre434 S g wGate z := hImage.symm
    _ = ∑ z ∈ S.image g,
      if z.1*z.2=target then
        parityOriginalReservedTwoEndpointFibre434 S g w z else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hFiber z
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [←hFixed z,parity_original_reserved_fullQ_fixed_e_vStar_eq_selected_H434
        d L band slot δ ξ K alpha q χ σ₀ σ₁ σ z.1 z.2]
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHProductGatePWeight -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- On EVERY original physically supported source `(e,vStar)` endpoint
with `e*vStar=ordinaryPart(P,u)` and u>0, the full genuine P-group
multiplicity parity projector and original W1(P,u) transfer EXACTLY
to physical `v=vStar*Ppart(P,u)`. The selected e is an ACTUAL Q-product
from the source full labelled prime tuple. No independent e/P-coprime
hypothesis is invented; Q/P separation follows from the native
source allocated-Q invariant. -/
theorem parity_original_reserved_product_gate_P_weight_transfer434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (z : ℕ×ℕ)
    (hz : z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ)
    (hgate : z.1*z.2=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) :
    let P := sourceOriginalPAllActualBands 20 L
    let v := z.2*sourceOriginalPPrimePart (Finset.univ.biUnion P) u
    sourceOriginalW1 P u *
      ((1-(-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion P) u)/2) =
    sourceOriginalW1 P v *
      ((1-(-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion P) v)/2) := by
  subst d
  dsimp only
  let P := sourceOriginalPAllActualBands 20 L
  let v := z.2*sourceOriginalPPrimePart (Finset.univ.biUnion P) u
  have hsplit := source_original_ordinary_times_P_part
    (Finset.univ.biUnion P) u hu
  have hEv : z.1*v=u := by
    dsimp [v]
    calc
      _ = (z.1*z.2)*sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by ac_rfl
      _ = sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u *
          sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by rw [hgate]
      _ = u := hsplit
  have hv : v ≠ 0 := by
    intro hv0
    apply hu
    rw [←hEv,hv0,mul_zero]
  unfold parityOriginalReservedFullQEVStarSupport434 at hz
  obtain ⟨⟨p,rest⟩,hrest,hendpoint⟩ := Finset.mem_image.mp hz
  have he : paritySourceOrderedAllocatedE434 δ rest = z.1 :=
    congrArg Prod.fst hendpoint
  have hNative := parity_actual_Q_allocated_e_P_weight_parity_invariant434
    L hL band slot δ rest v hv
  dsimp only at hNative
  have hEval : paritySourceOrderedAllocatedE434 δ rest*v=u := by rw [he]; exact hEv
  have hW : sourceOriginalW1 P u=sourceOriginalW1 P v :=
    (congrArg (sourceOriginalW1 P) hEval).symm.trans hNative.1
  have hParity : sourceOriginalPParityExponent (Finset.univ.biUnion P) u =
      sourceOriginalPParityExponent (Finset.univ.biUnion P) v :=
    (congrArg (sourceOriginalPParityExponent (Finset.univ.biUnion P)) hEval).symm.trans
      hNative.2.1
  rw [hW,hParity]

/-- EXACT full ORIGINAL reserved-Q+remaining-Q real source coefficient
at u INCLUDING true original W1(P,u) and the odd multiplicity-counted
P projector. The original source full Q-product gate is enforced
literally, and the reserved p imaginary phase is from the source.
This is the source-facing fixed δ,ξ coefficient prior to physical
Fourier/Mellin integration, not an abstract a_v substitute. -/
def parityOriginalReservedFullQProductGatePWeight434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (σ : ℝ) : ℂ :=
  ((sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      ((1-(-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)/2):ℝ):ℂ) *
    parityOriginalReservedFullQPhysicalProductGate434 d L band slot δ ξ σ u

/-- The actual original source ALL-Q-product/u physical gate,
WITH its complete W1/P multiplicity odd projector, is EXACTLY the
selected-e source Fourier coefficient times literal historical
reserved-prime/native B509 H(vStar), with the physical v-side W1/P
projector evaluated at `v=vStar*Ppart(P,u)`, on true `e*vStar=ordinaryPart(u)`.

This closes the finite Parity(4.7),(4.8) SOURCE full-Q physical/parity
algebra at each u and fixed original δ,ξ,σ, WITHOUT multiplying by
a false pointwise Fourier coefficient outside the historical e-window.
It does not by itself identify the fully post-integrated h=-2 alpha/beta
historical B' or the manuscript epsilon(v) signed convention. -/
theorem parity_original_reserved_fullQ_product_gate_P_weight_eq_e_H_v434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ) :
    parityOriginalReservedFullQProductGatePWeight434 d L u band slot δ ξ σ =
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if z.1*z.2=sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        paritySourceQSelectedFourierEFibre434
          (Q:=sourceActualSortedQ 20 d L band slot) δ
          (sourceActualSortedFrequencyScales 20 d L band slot) ξ z.1 *
        ((sourceOriginalW1 (sourceOriginalPAllActualBands 20 L)
            (z.2*sourceOriginalPPrimePart
              (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) *
          ((1-(-1:ℝ)^sourceOriginalPParityExponent
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
            (z.2*sourceOriginalPPrimePart
              (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u))/2):ℝ):ℂ) *
        parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ z.2
      else 0 := by
  unfold parityOriginalReservedFullQProductGatePWeight434
  rw [parity_original_reserved_fullQ_product_gate_eq_selected_H434
    d L band slot δ ξ K alpha q χ σ₀ σ₁ σ u]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hgate : z.1*z.2=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · simp only [if_pos hgate]
    have hW := parity_original_reserved_product_gate_P_weight_transfer434
      d L hL hd u hu band slot δ z hz hgate
    rw [hW]
    ring
  · simp only [if_neg hgate]
    ring
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHFullIntegrand -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- COMPLETE original §4.2 B590 SOURCE full-Q physical Fourier
INTEGRAND at fixed nonzero u and fixed δ,ξ, including the full
native original gate Fourier product and `log E` character, original
reserved q phase, factorial and true Q-product/Ppart gate, W1 and
multiplicity-counted odd P parity. No approximation or postulated
Fourier coefficient support. -/
def parityOriginalReservedFullQCompleteFourierIntegrand434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (σ : ℝ) : ℂ :=
  (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
  (((Real.fourierChar (Real.log E *
    (∑ i, ξ i/sourceActualSortedFrequencyScales 20 d L band slot i)) : Circle):ℂ)) *
  parityOriginalReservedFullQProductGatePWeight434 d L u band slot δ ξ σ

/-- The ACTUAL full original Parity(4.7),(4.8) source INTEGRAND,
not just a coefficient proxy, factors exactly into:

`Σ_(e,vStar : e*vStar=ordinaryPart(P,u))
  a_e^selected(δ,ξ,e) × a_v^physical(vStar,v)`

where `a_e^selected` contains the TRUE native f0/f1 Fourier product,
log(E) character and all selected Q primes, while the v-side has
`v=vStar*Ppart(P,u)`, real original W1(v), odd Ω_P projector and
H(vStar)=Σ_{reserved p*skipped r=vStar} p^(iσ)c_r with real native B509
factorial-cancelled coefficients. The v^(iρ) Mellin phase is evaluated
at ρ=0 here, BEFORE the independent true Mellin integral of Ψ is
inserted. This is an EXACT original fixed-frequency/u source algebraic
identity, not a Type II or post-integrated Parity(4.7) statement. -/
theorem parity_original_reserved_fullQ_complete_integrand_eq_e_aV434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ) :
    parityOriginalReservedFullQCompleteFourierIntegrand434
      d L E u band slot δ ξ σ =
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if z.1*z.2 = sourceOriginalOrdinaryPart
         (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateFourierCoefficient434
          d L E band slot δ ξ z.1 *
        parityOriginalReservedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ σ 0 z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0 := by
  let C : ℂ := (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
    ((Real.fourierChar (Real.log E *
      (∑ i, ξ i/sourceActualSortedFrequencyScales 20 d L band slot i)) : Circle):ℂ)
  unfold parityOriginalReservedFullQCompleteFourierIntegrand434
  rw [parity_original_reserved_fullQ_product_gate_P_weight_eq_e_H_v434
    d L hL hd u hu band slot δ ξ K alpha q χ σ₀ σ₁ σ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hgate : z.1*z.2=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · simp only [if_pos hgate]
    unfold parityOriginalSelectedEGateFourierCoefficient434
      parityOriginalReservedPhysicalAV434
    have hPhase0 : sourceOriginalPureMellinPhase434 (0:ℝ)
      (z.2*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) = 1 := by
      simp [sourceOriginalPureMellinPhase434]
    rw [hPhase0]
    ring
  · simp only [if_neg hgate]
    ring
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHActualFullQJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- ACTUAL unsmoothed original source Q tuple Fourier integrand at
one fixed h=-2 physical u, one B590 branch δ and one real Fourier
vector ξ: full original `sourceOriginalA` factorial 20!-labelled
Q tuple weight with W1/P odd parity, and complete B509 source
nonreserved selected/skipped Fourier character, without any invented
reserved q prime coefficient. -/
def parityOriginalActualFullQSourceFourierAtU434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    ((parityActualOriginalAFullTupleWeight434 d L u f : ℝ):ℂ) *
      paritySourceFullSlotFourierPhase434
        (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ
        (parityActualSourceRemainingFullQTuple434 d L band slot f)

/-- The ACTUAL original full Q-tuple Fourier weight at fixed u
is EXACTLY the real original reserved prime / all sorted Q source
product-gated coefficient with original factorial, W1 and odd parity
and reserved p^0=1, not just an unrelated Fourier object.
The source original `Fin (d+1)→Fin20` Q labels are transferred through
the verified reserved micro-Q / sorted remaining-Q equivalence. -/
theorem parity_original_actual_fullQ_fourier_source_eq_reserved_H_product_gate434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    parityOriginalActualFullQSourceFourierAtU434 d L u band slot δ ξ =
      parityOriginalReservedFullQProductGatePWeight434 d L u band slot δ ξ 0 := by
  let D := parityActualOriginalReservedSortedQEquiv434 d L band slot
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  let P := sourceOriginalPAllActualBands 20 L
  let W : ℝ := sourceOriginalW1 P u *
      ((1-(-1:ℝ)^sourceOriginalPParityExponent (Finset.univ.biUnion P) u)/2)
  let Fact : ℝ := ∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)
  let F : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) → ℂ :=
    fun f => ((parityActualOriginalAFullTupleWeight434 d L u f:ℝ):ℂ) *
      paritySourceFullSlotFourierPhase434 s ξ δ
        (parityActualSourceRemainingFullQTuple434 d L band slot f)
  have hEquiv : (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}), F f) =
      ∑ x : ({q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band} ×
        ((i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length) →
          {q : ℕ // q∈sourceActualSortedQ 20 d L band slot i})),
        F (D.symm x) := by
    have h := parity_original_reserved_sum_generic434 d L band slot
      (fun x => F (D.symm x))
    simpa only [D,parityActualOriginalReservedSortedQEquiv434,
      Equiv.symm_apply_apply] using h
  unfold parityOriginalActualFullQSourceFourierAtU434
    parityOriginalReservedFullQProductGatePWeight434
  change (∑ f, F f) = _
  rw [hEquiv]
  rw [Fintype.sum_prod_type]
  unfold parityOriginalReservedFullQPhysicalProductGate434
  rw [Finset.sum_subtype (sourceOriginalQActualBands 20 d L band)
    (by intro p; rfl)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest hrest
  let f := D.symm (p,rest)
  have hD : D f=(p,rest) := D.apply_symm_apply _
  have hfull := parity_actual_original_reserved_sorted_equiv_product434
    d L band slot f
  rw [hD] at hfull
  have hRest := parity_actual_original_reserved_sorted_equiv_rest434
    d L band slot f
  rw [hD] at hRest
  have hFact : (sourceActualSortedFactorial 20 d:ℂ) = (Fact:ℂ) := by
    unfold sourceActualSortedFactorial Fact
    push_cast
    rfl
  unfold F parityActualOriginalAFullTupleWeight434
  rw [←hRest,hfull]
  by_cases hgate : p.val*(∏ i, (rest i).val) =
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u
  · dsimp only [P,s] at hgate ⊢
    simp only [if_pos hgate]
    rw [show sourceOriginalPureMellinPhase434 (0:ℝ) p.val=1 by
      simp [sourceOriginalPureMellinPhase434]]
    rw [hFact]
    dsimp only [Fact]
    push_cast
    ring_nf
  · dsimp only [P,s] at hgate ⊢
    simp only [if_neg hgate]
    norm_num
end Green64Analytic.Parity

end

end

/-! ## OriginalActualFullQEFactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- The EXACT original `sourceOriginalA` factorial-labelled full Q
Fourier coefficient at one true physical u, together with the real
B590 f0/f1 Fourier transforms and source log(E) character, factors as
sum over actual (e,vStar) with original product gate e*vStar=
ordinaryPart(P,u) of source selected-Q e-only Fourier coefficient
× original physical W1(v) odd Ω_P projector × genuine reserved-prime
H(vStar) (native B509 factorial-cancelled residual).

This is no longer only a reserved-Q prototype: LEFT uses actual full
`parityActualOriginalAFullTupleWeight434` source A definition, verified
reserved sorted micro-Q equivalence and the literal original 20! real
normalization. RHS retains all actual repeated Q labels and original
reserved prime. This holds at fixed δ,ξ,u and Mellin v phase ρ=0.
The all-δ Fourier integral, true Ψ(ev/x) Mellin and historical ε(v)
sign convention still require separate SOURCE join. -/
theorem parity_original_actual_fullQ_fourier_integrand_eq_e_aV434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    ((∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
      ((Real.fourierChar (Real.log E *
        (∑ i, ξ i/sourceActualSortedFrequencyScales 20 d L band slot i)) : Circle):ℂ)) *
      parityOriginalActualFullQSourceFourierAtU434 d L u band slot δ ξ =
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if z.1*z.2 = sourceOriginalOrdinaryPart
         (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateFourierCoefficient434
          d L E band slot δ ξ z.1 *
        parityOriginalReservedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 0 z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0 := by
  rw [parity_original_actual_fullQ_fourier_source_eq_reserved_H_product_gate434]
  change parityOriginalReservedFullQCompleteFourierIntegrand434
    d L E u band slot δ ξ 0 = _
  exact (parity_original_reserved_fullQ_complete_integrand_eq_e_aV434
    d L E hL hd u hu band slot δ ξ K alpha q χ σ₀ σ₁ 0)
end Green64Analytic.Parity

end

end

/-! ## OriginalActualFullB590EFactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- ACTUAL full original source B590 f0/f1 Fourier integrand at fixed
physical u, selected allocation δ and source Fourier ξ: all genuine
20!-labelled Q tuples, source original parity/W1 weights and true
Q-history f0/f1 Fourier phases, with reserved Q prime integrated in
its ORIGINAL σ=0 state (before the separate Mellin/Ψ split).
No native source coefficient is replaced by synthetic e/v masses. -/
def parityOriginalActualFullQAllGateFourierAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    ((parityActualOriginalAFullTupleWeight434 d L u f : ℝ):ℂ) *
      parityOriginalB590AllGateFourierIntegrand434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) δ
        (fun i => (parityActualSourceRemainingFullQTuple434
          d L band slot f i).val) ξ

/-- Full **literal sourceOriginalA** all-labelled-Q real B590 Fourier
integrand at fixed u≠0,δ,ξ equals sum over true joint original
`(e,vStar)` prime-product support `e*vStar=ordinaryPart(P,u)` of:

`a_e^selected(δ,ξ,e) × v^0 W1(P,v) oddProjector_P(v) H_0(vStar)`

with `v=vStar*Ppart(P,u)` and H_0 the EXACT reserved-Q p^0/native B509
factorial-cancelled c_r convolution. This theorem connects the true
source f0/f1 Fourier gates to physical selected-e × reserved-prime
factorisation, not just an abstract Q coefficient. There is no missing
20! factorial. Nonzero Mellin σ,ρ and historical epsilon(v) sign
still require subsequent SOURCE integration, and Parity(4.17)/TypeII
remain open. -/
theorem parity_original_actual_fullQ_all_gate_fourier_eq_e_aV434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    parityOriginalActualFullQAllGateFourierAtU434
      d L E u band slot δ ξ =
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if z.1*z.2 = sourceOriginalOrdinaryPart
         (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateFourierCoefficient434
          d L E band slot δ ξ z.1 *
        parityOriginalReservedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 0 z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0 := by
  rw [←parity_original_actual_fullQ_fourier_integrand_eq_e_aV434
    d L E hL hd u hu band slot δ ξ K alpha q χ σ₀ σ₁]
  unfold parityOriginalActualFullQAllGateFourierAtU434
    parityOriginalActualFullQSourceFourierAtU434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [parity_original_B590_all_gate_integrand_exact434]
  ring
end Green64Analytic.Parity

end

end

