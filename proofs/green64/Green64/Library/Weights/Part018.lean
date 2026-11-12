module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib
public import Green64.Library.Weights.Part016
public import Green64.Library.Weights.Part017
public import Green64.Library.Weights.Part014

@[expose] public section

/-!
# Weights / Part018

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalSlowPhaseLipschitz -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Unit circle complex exponential is globally 1-Lipschitz
in its REAL phase. This supplies the genuine irrational
perturbation/Mellin-phase error, independent of q, characters,
or BIG-prime distribution. -/
theorem source_original_complex_unit_phase_lipschitz434
    (s t : ℝ) :
    ‖Complex.exp (Complex.I*(s:ℂ)) -
      Complex.exp (Complex.I*(t:ℂ))‖ ≤ |s-t| := by
  have hAdd :
      Complex.I*(t:ℂ) + Complex.I*((s-t:ℝ):ℂ) =
      Complex.I*(s:ℂ) := by
    push_cast
    ring
  have hexp :
      Complex.exp (Complex.I*(s:ℂ)) =
        Complex.exp (Complex.I*(t:ℂ)) *
        Complex.exp (Complex.I*((s-t:ℝ):ℂ)) := by
    rw [← Complex.exp_add,hAdd]
  have hFactor :
      Complex.exp (Complex.I*(s:ℂ)) -
        Complex.exp (Complex.I*(t:ℂ)) =
      Complex.exp (Complex.I*(t:ℂ)) *
        (Complex.exp (Complex.I*((s-t:ℝ):ℂ)) - 1) := by
    rw [hexp]
    ring
  calc
    _ = ‖Complex.exp (Complex.I*(t:ℂ)) *
        (Complex.exp (Complex.I*((s-t:ℝ):ℂ)) - 1)‖ := by
          rw [hFactor]
    _ = ‖Complex.exp (Complex.I*(t:ℂ))‖ *
        ‖Complex.exp (Complex.I*((s-t:ℝ):ℂ)) - 1‖ := norm_mul _ _
    _ = ‖Complex.exp (Complex.I*((s-t:ℝ):ℂ)) - 1‖ := by
      rw [Complex.norm_exp_I_mul_ofReal]
      ring
    _ ≤ ‖s-t‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |s-t| := by rw [Real.norm_eq_abs]

/-- Exact original slowly-varying phase in the SOURCE03
major-rational comparison:
M(n)=exp(i*(ζ log n + 2π β n)).
No use of an artificial product proxy. -/
noncomputable def sourceOriginalSlowMellinAdditivePhase434
    (ζ beta : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (Complex.I *
    ((ζ * Real.log (n:ℝ) +
       2*Real.pi*beta*(n:ℝ)):ℂ))

/-- Physical irrational remainder plus Mellin factor is bounded
directly by the LOG product discrepancy and the ORIGINAL
integer product discrepancy, for arbitrary integer marks D,X.
This is a real pointwise error, without an unproved derivative
or SW hypothesis. -/
theorem source_original_slow_mellin_additive_phase_oscillation434
    (ζ beta : ℝ) (D X : ℕ) :
    ‖sourceOriginalSlowMellinAdditivePhase434 ζ beta D -
      sourceOriginalSlowMellinAdditivePhase434 ζ beta X‖ ≤
    |ζ| * |Real.log (D:ℝ) - Real.log (X:ℝ)| +
       2 * Real.pi * |beta| * |(D:ℝ)-(X:ℝ)| := by
  let s : ℝ := ζ * Real.log (D:ℝ) + 2*Real.pi*beta*(D:ℝ)
  let t : ℝ := ζ * Real.log (X:ℝ) + 2*Real.pi*beta*(X:ℝ)
  have hSt : s-t =
      ζ*(Real.log (D:ℝ)-Real.log (X:ℝ)) +
      (2*Real.pi)*beta*((D:ℝ)-(X:ℝ)) := by
    dsimp [s,t]
    ring
  have hAbs :
      |s-t| ≤
        |ζ| * |Real.log (D:ℝ)-Real.log (X:ℝ)| +
        2 * Real.pi * |beta| * |(D:ℝ)-(X:ℝ)| := by
    rw [hSt]
    calc
      _ ≤ |ζ*(Real.log (D:ℝ)-Real.log (X:ℝ))| +
          |(2*Real.pi)*beta*((D:ℝ)-(X:ℝ))| := abs_add_le _ _
      _ = _ := by
        rw [abs_mul,abs_mul,abs_mul,abs_mul]
        norm_num [abs_of_pos Real.pi_pos]
  have hEqD :
      sourceOriginalSlowMellinAdditivePhase434 ζ beta D =
      Complex.exp (Complex.I*(s:ℂ)) := by
    simp [sourceOriginalSlowMellinAdditivePhase434,s]
  have hEqX :
      sourceOriginalSlowMellinAdditivePhase434 ζ beta X =
      Complex.exp (Complex.I*(t:ℂ)) := by
    simp [sourceOriginalSlowMellinAdditivePhase434,t]
  rw [hEqD,hEqX]
  exact (source_original_complex_unit_phase_lipschitz434 s t).trans hAbs
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSlowPhaseUnit -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false

/-- The actual irrational-beta/Mellin phase in source03 has
unit modulus for every natural product, including n=0.
This does not rely on character or prime distribution. -/
theorem source_original_slow_mellin_additive_phase_norm_one434
    (ζ beta : ℝ) (n : ℕ) :
    ‖sourceOriginalSlowMellinAdditivePhase434 ζ beta n‖ = 1 := by
  unfold sourceOriginalSlowMellinAdditivePhase434
  have h : ‖Complex.exp (Complex.I *
    (((ζ * Real.log (n:ℝ)+2*Real.pi*beta*(n:ℝ)):ℝ):ℂ))‖ = 1 :=
    Complex.norm_exp_I_mul_ofReal _
  simpa only [Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_ofNat] using h
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFiniteWeightedMinorSum -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Finite weighted L¹-to-squared-L² saving for the
genuine source03 five-index sum. Individual saving is
proportional to the SQUARE of each true cell coefficient,
not to the number of active character modes. This
elementary estimate loses only the SQUARED TOTAL cell
weight; no external family-cardinality hypothesis. -/
theorem source_original_true_finite_weighted_minor_square434
    {I : Type} (family : Finset I)
    (terms : I → ℂ) (cost : I → ℝ)
    (save : ℝ) (hSave : 0 ≤ save)
    (hCost : ∀ i ∈ family, 0 ≤ cost i)
    (hTerm : ∀ i ∈ family,
      ‖terms i‖^2 ≤ (cost i)^2*save) :
    ‖∑ i ∈ family, terms i‖^2 ≤
      (∑ i ∈ family, cost i)^2*save := by
  let r := Real.sqrt save
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r^2 = save := Real.sq_sqrt hSave
  have hEach (i : I) (hi : i ∈ family) :
      ‖terms i‖ ≤ cost i*r := by
    have hh := hTerm i hi
    have hc := hCost i hi
    have hcr : 0 ≤ cost i*r := mul_nonneg hc hr
    have hnorm : 0 ≤ ‖terms i‖ := norm_nonneg _
    have hSquare : ‖terms i‖^2 ≤ (cost i*r)^2 := by
      nlinarith [hh,hrSq]
    nlinarith
  have hSum : ‖∑ i ∈ family, terms i‖ ≤
      (∑ i ∈ family, cost i)*r := by
    calc
      _ ≤ ∑ i ∈ family, ‖terms i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ family, cost i*r :=
        Finset.sum_le_sum hEach
      _ = (∑ i ∈ family, cost i)*r := by
        rw [Finset.sum_mul]
  have hnonnegCost : 0 ≤ ∑ i ∈ family, cost i :=
    Finset.sum_nonneg hCost
  have hnonnegTotal : 0 ≤ (∑ i ∈ family, cost i)*r :=
    mul_nonneg hnonnegCost hr
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hSum 2
  calc
    _ ≤ ((∑ i ∈ family, cost i)*r)^2 := hSq
    _ = (∑ i ∈ family, cost i)^2*save := by
      rw [mul_pow,hrSq]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteFourMatchedOperatorSaving -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The four TRUE dyadic rectangles attached to one source03
GLOBAL output cell pair incur exactly factor 16 in the SQUARED
Hilbert operator bound, with no loss counting physical primes,
fibres, output atoms or all dyads. The analytic saving in each
rectangle must be genuinely proved; this lemma is the exact
four-channel quantitative reassembly. -/
theorem source_original_finite_four_matched_operator_saving434
    (z00 z01 z10 z11 : ℂ) (saving : ℝ)
    (hSaving : 0 ≤ saving)
    (h00 : ‖z00‖^2 ≤ saving)
    (h01 : ‖z01‖^2 ≤ saving)
    (h10 : ‖z10‖^2 ≤ saving)
    (h11 : ‖z11‖^2 ≤ saving) :
    ‖z00+z01+z10+z11‖^2 ≤ 16*saving := by
  classical
  let mode : ℕ → ℂ := fun i =>
    if i=0 then z00 else if i=1 then z01
    else if i=2 then z10 else z11
  have hTerm (i : ℕ) (hi : i ∈ Finset.range 4) :
      ‖mode i‖^2 ≤ (1:ℝ)^2*saving := by
    have hlt : i < 4 := Finset.mem_range.mp hi
    interval_cases i <;> simp only [mode,one_pow,one_mul] at *
    all_goals first | exact h00 | exact h01 | exact h10 | exact h11
  have hCost (i : ℕ) (hi : i ∈ Finset.range 4) :
      (0:ℝ) ≤ 1 := by norm_num
  have hResult := source_original_true_finite_weighted_minor_square434
    (Finset.range 4) mode (fun _ => (1:ℝ))
    saving hSaving hCost hTerm
  have hSum : (∑ i ∈ Finset.range 4, mode i) =
      z00+z01+z10+z11 := by
    norm_num [Finset.sum_range_succ,mode]
  have hCostSum : (∑ i ∈ Finset.range 4, (1:ℝ)) = 4 := by
    norm_num
  rw [hSum,hCostSum] at hResult
  norm_num at hResult ⊢
  exact hResult
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteSignedFourWindowOperator -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Four genuine SOURCE03 matched dyadic OUTPUT windows after
the original inclusion-exclusion complex sign sigma has been
applied to EACH window. If every signed window has the SAME
true arithmetic squared-L2 budget, the full signed operator
loses exactly factor 16. Sigma can be arbitrary complex and
need not be assumed positive, real, or factorizable. -/
theorem source_original_finite_signed_four_window_operator434
    (sigma full z00 z01 z10 z11 : ℂ)
    (saving : ℝ) (hsave : 0 ≤ saving)
    (hExact : full = z00+z01+z10+z11)
    (h00 : ‖sigma*z00‖^2 ≤ saving)
    (h01 : ‖sigma*z01‖^2 ≤ saving)
    (h10 : ‖sigma*z10‖^2 ≤ saving)
    (h11 : ‖sigma*z11‖^2 ≤ saving) :
    ‖sigma*full‖^2 ≤ 16*saving := by
  have hDist :
      sigma*full =
      sigma*z00+sigma*z01+sigma*z10+sigma*z11 := by
    rw [hExact]
    ring
  rw [hDist]
  exact source_original_finite_four_matched_operator_saving434
    (sigma*z00) (sigma*z01) (sigma*z10) (sigma*z11)
    saving hsave h00 h01 h10 h11
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueTwoBlockSignedPatternTotal -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The ACTUAL two-block SOURCE03 comparison patterns have total
inclusion-exclusion sign -1 when both designated probe blocks
are nonempty. This is an exact signed combinatorial identity,
not an absolute cell/character counting estimate.
It does not on its own identify nu-dependent RAW integrands
with one common physical RAW operator. -/
theorem source_original_true_two_block_signed_pattern_total434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (hA : (sourceOriginalProbeBlock434 blockA m).Nonempty)
    (hB : (sourceOriginalProbeBlock434 blockB m).Nonempty) :
    (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      -((-1:ℤ)^(ν.1.card+ν.2.card))) = -1 := by
  classical
  let IA := (sourceOriginalProbeBlock434 blockA m).powerset.filter
    Finset.Nonempty
  let IB := (sourceOriginalProbeBlock434 blockB m).powerset.filter
    Finset.Nonempty
  have hSumA : (∑ a ∈ IA, (-1:ℤ)^a.card) = -1 := by
    simpa only [IA] using
      (source_original_probe_nonempty_alternation434
        (sourceOriginalProbeBlock434 blockA m)).trans (if_pos hA)
  have hSumB : (∑ a ∈ IB, (-1:ℤ)^a.card) = -1 := by
    simpa only [IB] using
      (source_original_probe_nonempty_alternation434
        (sourceOriginalProbeBlock434 blockB m)).trans (if_pos hB)
  change (∑ ν ∈ IA.product IB,
      -((-1:ℤ)^(ν.1.card+ν.2.card))) = -1
  rw [Finset.product_eq_sprod,Finset.sum_product]
  simp_rw [pow_add]
  simp only [Finset.sum_neg_distrib]
  calc
    _ = -((∑ a ∈ IA, (-1:ℤ)^a.card) *
          (∑ b ∈ IB, (-1:ℤ)^b.card)) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = -1 := by rw [hSumA,hSumB]; norm_num
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueMixedEndpointParityPattern -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- If ONE source03 endpoint has a parity twist that the
other does not, shared-label removal introduces the
ν-dependent sign of the number of freed probe slots, up
to one common constant sign. Multiplying the original
inclusion-exclusion coefficient by that ν-dependent sign
DESTROYS the ordinary signed alternating cancellation:
the total is the NEGATIVE actual number of comparison
patterns, not -1. This is a genuine four-sign issue,
not a missing Lean norm inequality. -/
theorem source_original_true_mixed_endpoint_freed_parity_sum434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ) :
    (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
       (-((-1:ℤ)^(ν.1.card+ν.2.card))) *
         (-1:ℤ)^(ν.1.card+ν.2.card)) =
      -((sourceOriginalTwoBlockProbePatterns434
        blockA blockB m).card:ℤ) := by
  classical
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  have hTerm (ν : SourceOriginalProbePattern434 G m) :
      (-((-1:ℤ)^(ν.1.card+ν.2.card))) *
        (-1:ℤ)^(ν.1.card+ν.2.card) = -1 := by
    let n := ν.1.card+ν.2.card
    have hSquare : ((-1:ℤ)^n)*((-1:ℤ)^n) = 1 := by
      calc
        _ = ((-1:ℤ)*(-1))^n := (mul_pow (-1:ℤ) (-1:ℤ) n).symm
        _ = 1 := by norm_num
    calc
      _ = - (((-1:ℤ)^n)*((-1:ℤ)^n)) := by dsimp only [n];ring
      _ = -1 := by rw [hSquare]
  calc
    _ = ∑ ν ∈ family, (-1:ℤ) := by
      apply Finset.sum_congr rfl
      intro ν hν
      exact hTerm ν
    _ = -((family.card:ℤ)) := by simp

/-- Precise cardinality of the miscancelled mixed-sign
family, with no synthetic combinatorial majorant. -/
theorem source_original_true_mixed_endpoint_freed_parity_exact434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ) :
    (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
       (-((-1:ℤ)^(ν.1.card+ν.2.card))) *
         (-1:ℤ)^(ν.1.card+ν.2.card)) =
     -(((2^(blockA.card*m)-1) *
         (2^(blockB.card*m)-1):ℕ):ℤ) := by
  rw [source_original_true_mixed_endpoint_freed_parity_sum434,
    source_original_two_block_probe_pattern_exact_card434]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalUnfilteredIdealModes -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Finite linearity of the actual coordinate-mode list. -/
theorem source_original_unfiltered_ideal_list_sum434
    {P I : Type} [Fintype P] [DecidableEq P] [DecidableEq I]
    {M : ℕ} (mu : P → ℂ) (S : Finset (Fin M))
    (K : List (Fin M)) (a : Finset I) (f : I → (Fin M → P) → ℂ) :
    sourceOriginalHoeffdingList434 mu S K (fun x => ∑ i ∈ a, f i x) =
      (fun x => ∑ i ∈ a, sourceOriginalHoeffdingList434 mu S K (f i) x) := by
  classical
  induction a using Finset.induction_on with
  | empty => simpa using source_original_hoeffding_list_zero434 mu S K
  | @insert i a hi ih =>
    simp only [Finset.sum_insert hi]
    rw [source_original_hoeffding_list_add434, ih]

/-- Each actual mean/difference acts diagonally on a full Hoeffding mode. -/
theorem source_original_unfiltered_ideal_mode_eigen434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (hmu : (∑ p, mu p) = 1)
    (S T : Finset (Fin M)) (i : Fin M)
    (f : (Fin M → P) → ℂ) :
    sourceOriginalHoeffdingMode434 mu T i
      (sourceOriginalHoeffdingList434 mu S (Finset.univ.toList) f) =
      if (i ∈ T ↔ i ∈ S) then
        sourceOriginalHoeffdingList434 mu S (Finset.univ.toList) f
      else (fun _ => 0) := by
  funext x
  have he := source_original_hoeffding_list_mode_eigen434 mu hmu S
    (Finset.univ.toList) (Finset.nodup_toList _) i (by simp) f x
  by_cases ht : i ∈ T <;> by_cases hs : i ∈ S <;>
    simp_all [sourceOriginalHoeffdingMode434, sourceOriginalBigCoordinateDiff434]

/-- A partial list selects precisely modes with the specified coordinate eigenvalues.
No phase or multiplication operator is moved through the means. -/
theorem source_original_unfiltered_ideal_list_eigen434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (hmu : (∑ p, mu p) = 1)
    (S T : Finset (Fin M)) (K : List (Fin M))
    (f : (Fin M → P) → ℂ) :
    sourceOriginalHoeffdingList434 mu T K
      (sourceOriginalHoeffdingList434 mu S (Finset.univ.toList) f) =
      if (∀ i ∈ K, (i ∈ T ↔ i ∈ S)) then
        sourceOriginalHoeffdingList434 mu S (Finset.univ.toList) f
      else (fun _ => 0) := by
  induction K with
  | nil => simp [sourceOriginalHoeffdingList434]
  | cons i K ih =>
    change sourceOriginalHoeffdingList434 mu T K
      (sourceOriginalHoeffdingMode434 mu T i
        (sourceOriginalHoeffdingList434 mu S Finset.univ.toList f)) = _
    rw [source_original_unfiltered_ideal_mode_eigen434 mu hmu]
    by_cases hi : (i ∈ T ↔ i ∈ S)
    · rw [if_pos hi, ih]
      simp only [List.mem_cons, forall_eq_or_imp]
      simp only [hi, true_and]
    · rw [if_neg hi, source_original_hoeffding_list_zero434]
      have hn : ¬ (∀ j ∈ i :: K, (j ∈ T ↔ j ∈ S)) := by
        intro h
        exact hi (h i (by simp))
      rw [if_neg hn]

/-- Reconstruction turns a concrete list of means/differences into its selected
full Hoeffding sum. This is an equality on arbitrary complex tests. -/
theorem source_original_unfiltered_ideal_list_selected434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (hmu : (∑ p, mu p) = 1)
    (T : Finset (Fin M)) (K : List (Fin M))
    (f : (Fin M → P) → ℂ) :
    sourceOriginalHoeffdingList434 mu T K f =
    sourceOriginalHoeffdingSelected434 mu
      (Finset.univ.powerset.filter (fun S => ∀ i ∈ K, (i ∈ T ↔ i ∈ S))) f := by
  have hexp : f = (fun x => ∑ S ∈ (Finset.univ : Finset (Fin M)).powerset,
      sourceOriginalHoeffdingList434 mu S Finset.univ.toList f x) := by
    funext x
    simpa using (source_original_hoeffding_list_expansion434 mu
      (Finset.univ.toList) (Finset.nodup_toList _) f x).symm
  calc
    sourceOriginalHoeffdingList434 mu T K f =
        sourceOriginalHoeffdingList434 mu T K
          (fun x => ∑ S ∈ (Finset.univ : Finset (Fin M)).powerset,
            sourceOriginalHoeffdingList434 mu S Finset.univ.toList f x) :=
      congrArg (sourceOriginalHoeffdingList434 mu T K) hexp
    _ = _ := by
      rw [source_original_unfiltered_ideal_list_sum434]
      funext x
      simp only [source_original_unfiltered_ideal_list_eigen434 mu hmu]
      simp only [sourceOriginalHoeffdingSelected434, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S hS
      split_ifs <;> rfl

end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalUnfilteredIdealSurvivor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Concrete probe differences and tail means equal the existing selected
Hoeffding projector, on the original weighted coordinates. -/
theorem source_original_unfiltered_ideal_probe_tail434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (hmu : (∑ p, mu p) = 1)
    (probes trailing : Finset (Fin M)) (hd : Disjoint probes trailing)
    (f : (Fin M → P) → ℂ) :
    sourceOriginalHoeffdingList434 mu probes (probes ∪ trailing).toList f =
    sourceOriginalHoeffdingSelected434 mu
      (Finset.univ.powerset.filter
        (fun S => probes ⊆ S ∧ Disjoint S trailing)) f := by
  rw [source_original_unfiltered_ideal_list_selected434 mu hmu]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
    true_and, Finset.mem_toList]
  constructor
  · intro h
    constructor
    · intro i hi
      exact (h i (Finset.mem_union_left _ hi)).mp hi
    · apply Finset.disjoint_left.mpr
      intro i hi ht
      have hp := (h i (Finset.mem_union_right _ ht)).mpr hi
      exact Finset.disjoint_left.mp hd hp ht
  · rintro ⟨hp, ht⟩ i hi
    constructor
    · exact fun h => hp h
    · intro hs
      rcases Finset.mem_union.mp hi with h | h
      · exact h
      · exact (Finset.disjoint_left.mp ht hs h).elim

/-- Group operation defined using actual coordinate means and differences,
without selected-mode notation. The input can couple every group. -/
noncomputable def sourceOriginalUnfilteredIdealGroup434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ) (g : G)
    (probes trailing : Finset (Fin M))
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (x : SourceOriginalJointBigState434 BP M) : ℂ :=
  sourceOriginalHoeffdingList434 (fun p => (mu g p : ℂ))
    probes (probes ∪ trailing).toList
    (fun u => f (Function.update x g u)) (x g)

theorem source_original_unfiltered_ideal_group_survivor434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ)
    (hnorm : ∀ g, (∑ p, mu g p) = 1)
    (g : G) (probes trailing : Finset (Fin M)) (hd : Disjoint probes trailing)
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalUnfilteredIdealGroup434 BP mu g probes trailing f =
      sourceOriginalJointGroupSurvivorProjector434 BP mu g probes trailing f := by
  funext x
  unfold sourceOriginalUnfilteredIdealGroup434 sourceOriginalJointGroupSurvivorProjector434
  have hc : (∑ p : BP g, (mu g p : ℂ)) = 1 := by
    exact_mod_cast hnorm g
  rw [source_original_unfiltered_ideal_probe_tail434 _ hc _ _ hd]

/-- Iterate the literal coordinate operations across the named BIG groups. -/
noncomputable def sourceOriginalUnfilteredIdealGroups434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ)
    (probes trailing : G → Finset (Fin M)) :
    List G → (SourceOriginalJointBigState434 BP M → ℂ) →
      (SourceOriginalJointBigState434 BP M → ℂ)
  | [], f => f
  | g :: gs, f => sourceOriginalUnfilteredIdealGroups434 BP mu probes trailing gs
      (sourceOriginalUnfilteredIdealGroup434 BP mu g (probes g) (trailing g) f)

theorem source_original_unfiltered_ideal_groups_survivor434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    {M : ℕ} (mu : (g : G) → BP g → ℝ)
    (hnorm : ∀ g, (∑ p, mu g p) = 1)
    (probes trailing : G → Finset (Fin M))
    (hd : ∀ g, Disjoint (probes g) (trailing g))
    (gs : List G) (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalUnfilteredIdealGroups434 BP mu probes trailing gs f =
      sourceOriginalJointAllGroupSurvivor434 BP mu probes trailing gs f := by
  induction gs generalizing f with
  | nil => rfl
  | cons g gs ih =>
    change sourceOriginalUnfilteredIdealGroups434 BP mu probes trailing gs
        (sourceOriginalUnfilteredIdealGroup434 BP mu g (probes g) (trailing g) f) = _
    rw [source_original_unfiltered_ideal_group_survivor434 BP mu hnorm _ _ _ (hd g), ih]
    rfl

/-- Quantitative negative log-power for the concrete harmonic coordinate
operations, with symmetrization applied BEFORE same-group tail means.
This is the survivor adapter, not a claim about the frozen canonical kernel. -/
theorem source_original_unfiltered_ideal_coordinate_log_power434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (prime : (g : G) → BP g → ℕ) (V : G → ℝ)
    (hV : ∀ g, 0 < V g)
    (hEq : ∀ g, V g = ∑ p : BP g, 1/(prime g p:ℝ))
    {M : ℕ} (probes trailing : G → Finset (Fin M))
    (hd : ∀ g, Disjoint (probes g) (trailing g))
    (gs : List G) (hgs : gs.Nodup) (m ell : ℕ)
    (hcard : ∀ g ∈ gs, (probes g).card = m ∧ (trailing g).card = ell)
    (LL A c : ℝ) (hLL : 1 ≤ LL) (hc : 0 ≤ c)
    (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (hcount : c * Real.log LL ≤ (gs.length : ℝ))
    (hbudget : A ≤ c * Real.log ((m+1 : ℕ) : ℝ))
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalJointBigEnergy434 BP (sourceOriginalJointHarmonicMu434 BP prime V)
      (sourceOriginalUnfilteredIdealGroups434 BP (sourceOriginalJointHarmonicMu434 BP prime V)
        probes trailing gs (sourceOriginalJointAllSymmetrize434 BP gs f)) ≤
      LL^(-A) * sourceOriginalJointBigEnergy434 BP
        (sourceOriginalJointHarmonicMu434 BP prime V) f := by
  obtain ⟨hpos, hnorm⟩ := source_original_joint_harmonic_normalized434 BP prime V hV hEq
  rw [source_original_unfiltered_ideal_groups_survivor434 BP _ hnorm _ _ hd]
  have h := source_original_joint_unsymmetrized_harmonic_log_power434
    BP prime V hV hEq probes trailing hd gs hgs m ell hcard
    LL A c hLL hc hm hell hcount hbudget f
  have hpow : 0 < LL^A := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (le_trans (by norm_num) hLL)]
  calc
    _ ≤ sourceOriginalJointBigEnergy434 BP (sourceOriginalJointHarmonicMu434 BP prime V) f /
        LL^A := (le_div_iff₀ hpow).mpr h
    _ = _ := by ring

end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalVariableSelectedMarginal -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- TRUE original SOURCE03 ν-variable free-slot harmonic
probability law has the EXACT independent-coordinate marginal
over ANY collision-free selected index family. The selected
indices are actual pairs (BIG group g, unshared slot i_g),
and both the true dependent prime support BP_g and original
1/(p V_g) masses remain unchanged. Every OTHER physical
slot is fully integrated out; no independence requirement
on a general selected observable F, no uniform slot count
and no fake selected-prime measure. -/
theorem source_original_variable_BIG_selected_marginal434
    {G J : Type} [Fintype G] [DecidableEq G] [Fintype J]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    (t : G → ℕ)
    (mu : ∀ g, BP g → ℝ)
    (hmu : ∀ g, ∑ p : BP g, mu g p = 1)
    (e : J ↪ (Σ g : G, Fin (t g)))
    (F : (∀ j : J, BP (e j).1) → ℝ) :
    (∑ x : SourceOriginalVariableBIGState434 BP t,
      sourceOriginalVariableBIGMass434 BP t mu x *
        F (fun j => x (e j).1 (e j).2)) =
    (∑ a : (∀ j : J, BP (e j).1),
      (∏ j : J, mu (e j).1 (a j)) * F a) := by
  classical
  let I := (Σ g : G, Fin (t g))
  let B : I → Type := fun k => BP k.1
  let nu : (k : I) → B k → ℝ := fun k p => mu k.1 p
  let E : SourceOriginalVariableBIGState434 BP t ≃
    (∀ k : I, B k) := sourceOriginalVariableBIGFlattenEquiv434 BP t
  have hF (x : SourceOriginalVariableBIGState434 BP t) :
      F (fun j : J => x (e j).1 (e j).2) =
      F (fun j : J => E x (e j)) := by
    rfl
  have hWeight (x : SourceOriginalVariableBIGState434 BP t) :
      sourceOriginalVariableBIGMass434 BP t mu x =
        ∏ k : I, nu k (E x k) :=
    source_original_variable_BIG_flatten_mass434 BP t mu x
  have hEquiv := Fintype.sum_equiv E
    (fun x : SourceOriginalVariableBIGState434 BP t =>
      sourceOriginalVariableBIGMass434 BP t mu x *
      F (fun j => x (e j).1 (e j).2))
    (fun x : (∀ k : I, B k) =>
      (∏ k : I, nu k (x k)) *
      F (fun j => x (e j)))
    (by
      intro x
      rw [hWeight x,hF x])
  have hMarg := source_original_finite_injective_marginal_law434
    B e nu (fun k => hmu k.1) F
  exact hEquiv.trans hMarg
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalWeightedSourceCS -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Genuine finite weighted Cauchy–Schwarz for arbitrary complex
tuple tests, with a nonnegative SUB-probability law. Important
for passing the pointwise original major-rational comparison
to a bilinear estimate without replacing arbitrary tests by
supremum-one tests. -/
theorem source_original_finite_weighted_l1_l2_sq434
    {X : Type} [Fintype X]
    (w : X → ℝ) (f : X → ℂ)
    (hw : ∀ x, 0 ≤ w x)
    (hmass : (∑ x : X, w x) ≤ 1) :
    (∑ x : X, w x*‖f x‖)^2 ≤
      (∑ x : X, w x*‖f x‖^2) := by
  classical
  have hprod (x : X) :
      Real.sqrt (w x) * (Real.sqrt (w x)*‖f x‖) =
        w x*‖f x‖ := by
    rw [←mul_assoc,←pow_two,Real.sq_sqrt (hw x)]
  have hsq (x : X) :
      (Real.sqrt (w x)*‖f x‖)^2 = w x*‖f x‖^2 := by
    rw [mul_pow, Real.sq_sqrt (hw x)]
  have hsum (x : X) : 0 ≤ w x*‖f x‖^2 :=
    mul_nonneg (hw x) (sq_nonneg _)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset X)
    (fun x : X => Real.sqrt (w x))
    (fun x : X => Real.sqrt (w x)*‖f x‖)
  calc
    _ = (∑ x : X,
          Real.sqrt (w x)*(Real.sqrt (w x)*‖f x‖))^2 := by
        apply congrArg (fun t : ℝ => t^2)
        apply Finset.sum_congr rfl
        intro x hx
        exact (hprod x).symm
    _ ≤ (∑ x : X, (Real.sqrt (w x))^2) *
          (∑ x : X, (Real.sqrt (w x)*‖f x‖)^2) := hCS
    _ = (∑ x : X, w x) *
          (∑ x : X, w x*‖f x‖^2) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro x hx
          exact Real.sq_sqrt (hw x)
        · apply Finset.sum_congr rfl
          intro x hx
          exact hsq x
    _ ≤ 1 * (∑ x : X, w x*‖f x‖^2) := by
          exact mul_le_mul_of_nonneg_right hmass
            (Finset.sum_nonneg (fun x hx => hsum x))
    _ = _ := one_mul _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteRareEndpointL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Genuine source03 two-ENDPOINT independent L² error on an
unretained source event. Unlike a pointwise small-kernel
argument, the original residual phase may have modulus ONE
there: the saving is the true small event probability eta
times weighted energies, and source/target endpoint tests
are fully arbitrary complex functions (not bounded or constant).
The source/target measures need only be subprobabilities.
There is NO false claim that rare-event restriction is a
small L²→L² operator. -/
theorem source_original_finite_source_rare_endpoint_L2_sq434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x, 0 ≤ wX x) (hwY : ∀ y, 0 ≤ wY y)
    (hmY : (∑ y : Y, wY y) ≤ 1)
    (badX : X → Prop)
    (eta : ℝ) (heta : 0 ≤ eta)
    (hBad : (∑ x : X,
      wX x*(if badX x then (1:ℝ) else 0)) ≤ eta)
    (f : X → ℂ) (g : Y → ℂ) (H : X × Y → ℂ)
    (hH : ∀ q, ‖H q‖ ≤ 1) :
    ‖(∑ q : X × Y,
      ((wX q.1*wY q.2:ℝ):ℂ) *
        star (f q.1) * g q.2 *
        (if badX q.1 then H q else 0))‖^2 ≤
    eta * (∑ x : X, wX x*‖f x‖^2) *
      (∑ y : Y, wY y*‖g y‖^2) := by
  classical
  let AX : ℝ := ∑ x : X,
    wX x*(if badX x then ‖f x‖ else 0)
  let AY : ℝ := ∑ y : Y, wY y*‖g y‖
  let SX : ℝ := ∑ x : X, wX x*‖f x‖^2
  let SY : ℝ := ∑ y : Y, wY y*‖g y‖^2
  let BX : ℝ := ∑ x : X, wX x*(if badX x then 1 else 0)
  let z : X × Y → ℂ := fun q =>
    ((wX q.1*wY q.2:ℝ):ℂ) *
      star (f q.1) * g q.2 *
      (if badX q.1 then H q else 0)
  have hAXpos : 0 ≤ AX := by
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (hwX x) (by split_ifs <;> positivity)
  have hAYpos : 0 ≤ AY :=
    Finset.sum_nonneg (fun y hy =>
      mul_nonneg (hwY y) (norm_nonneg _))
  have hSXpos : 0 ≤ SX :=
    Finset.sum_nonneg (fun x hx =>
      mul_nonneg (hwX x) (sq_nonneg _))
  have hSYpos : 0 ≤ SY :=
    Finset.sum_nonneg (fun y hy =>
      mul_nonneg (hwY y) (sq_nonneg _))
  have hTerm (q : X × Y) :
      ‖z q‖ ≤
        (wX q.1*(if badX q.1 then ‖f q.1‖ else 0))*
        (wY q.2*‖g q.2‖) := by
    by_cases hbad : badX q.1
    · have hw : 0 ≤ wX q.1*wY q.2 :=
        mul_nonneg (hwX q.1) (hwY q.2)
      have hcoef :
          0 ≤ (wX q.1*wY q.2)*‖f q.1‖*‖g q.2‖ := by
        positivity
      have heq :
          ‖z q‖ = (wX q.1*wY q.2)*‖f q.1‖*
            ‖g q.2‖*‖H q‖ := by
        simp only [z,if_pos hbad,norm_mul,norm_star,
          Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (hwX q.1), abs_of_nonneg (hwY q.2)]
      rw [heq]
      calc
        _ ≤ (wX q.1*wY q.2)*‖f q.1‖*‖g q.2‖*1 :=
          mul_le_mul_of_nonneg_left (hH q) hcoef
        _ = _ := by simp only [if_pos hbad]; ring
    · simp [z,hbad]
  have hFactor :
      (∑ q : X × Y,
        (wX q.1*(if badX q.1 then ‖f q.1‖ else 0))*
        (wY q.2*‖g q.2‖)) = AX*AY := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ x : X,
          (wX x*(if badX x then ‖f x‖ else 0))*
          (∑ y : Y, wY y*‖g y‖) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
      _ = AX*AY := by
        dsimp [AX,AY]
        rw [Finset.sum_mul]
  have hNorm :
      ‖∑ q : X × Y, z q‖ ≤ AX*AY := by
    calc
      _ ≤ ∑ q : X × Y, ‖z q‖ := norm_sum_le _ _
      _ ≤ ∑ q : X × Y,
          (wX q.1*(if badX q.1 then ‖f q.1‖ else 0))*
          (wY q.2*‖g q.2‖) :=
        Finset.sum_le_sum (fun q hq => hTerm q)
      _ = AX*AY := hFactor
  have hAXsq : AX^2 ≤ BX*SX :=
    source_original_finite_rare_event_CS434 wX f badX hwX
  have hAYsq : AY^2 ≤ SY :=
    source_original_finite_weighted_l1_l2_sq434 wY g hwY hmY
  have hBX : BX ≤ eta := hBad
  have hAXbounded : AX^2 ≤ eta*SX := by
    calc
      _ ≤ BX*SX := hAXsq
      _ ≤ eta*SX := mul_le_mul_of_nonneg_right hBX hSXpos
  have hMul : AX^2*AY^2 ≤ (eta*SX)*SY :=
    mul_le_mul hAXbounded hAYsq (sq_nonneg AY)
      (mul_nonneg heta hSXpos)
  have hSq : ‖∑ q : X × Y, z q‖^2 ≤ (AX*AY)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  change ‖∑ q : X × Y, z q‖^2 ≤ eta*SX*SY
  calc
    _ ≤ (AX*AY)^2 := hSq
    _ = AX^2*AY^2 := by ring
    _ ≤ (eta*SX)*SY := hMul
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteTargetRareEndpointL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The TRUE rare-event error when the original TARGET endpoint
is discarded, obtained by transpose-conjugating the already
verified source-endpoint C136 theorem. Both physical tests are
arbitrary complex-valued, no supnorm or independence of H. -/
theorem source_original_finite_target_rare_endpoint_L2_sq434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x, 0 ≤ wX x) (hwY : ∀ y, 0 ≤ wY y)
    (hmX : (∑ x : X, wX x) ≤ 1)
    (badY : Y → Prop)
    (eta : ℝ) (heta : 0 ≤ eta)
    (hBad : (∑ y : Y,
      wY y*(if badY y then (1:ℝ) else 0)) ≤ eta)
    (f : X → ℂ) (g : Y → ℂ) (H : X × Y → ℂ)
    (hH : ∀ q, ‖H q‖ ≤ 1) :
    ‖(∑ q : X × Y,
      ((wX q.1*wY q.2:ℝ):ℂ) *
        star (f q.1) * g q.2 *
        (if badY q.2 then H q else 0))‖^2 ≤
    eta * (∑ x : X, wX x*‖f x‖^2) *
      (∑ y : Y, wY y*‖g y‖^2) := by
  classical
  let K : Y × X → ℂ := fun q => star (H (q.2,q.1))
  have hK (q : Y × X) : ‖K q‖ ≤ 1 := by
    simpa [K, norm_star] using hH (q.2,q.1)
  have hSource :=
    source_original_finite_source_rare_endpoint_L2_sq434
      wY wX hwY hwX hmX badY eta heta hBad g f K hK
  let z : X × Y → ℂ := fun q =>
    ((wX q.1*wY q.2:ℝ):ℂ) *
      star (f q.1) * g q.2 *
      (if badY q.2 then H q else 0)
  let zT : Y × X → ℂ := fun q =>
    ((wY q.1*wX q.2:ℝ):ℂ) *
      star (g q.1) * f q.2 *
      (if badY q.1 then K q else 0)
  have hPoint (y : Y) (x : X) :
      zT (y,x) = star (z (x,y)) := by
    by_cases hb : badY y
    · simp [z,zT,K,hb,star_mul] <;> ring
    · simp [z,zT,K,hb]
  have hTranspose :
      (∑ q : Y × X, zT q) =
      star (∑ q : X × Y, z q) := by
    calc
      _ = ∑ y : Y, ∑ x : X, zT (y,x) := by
        rw [Fintype.sum_prod_type]
      _ = ∑ x : X, ∑ y : Y, zT (y,x) := Finset.sum_comm
      _ = ∑ x : X, ∑ y : Y, star (z (x,y)) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact hPoint y x
      _ = star (∑ q : X × Y, z q) := by
        rw [star_sum, Fintype.sum_prod_type]
  have hNorm : ‖∑ q : X × Y, z q‖ =
      ‖∑ q : Y × X, zT q‖ := by
    rw [hTranspose,norm_star]
  change ‖∑ q : X × Y, z q‖^2 ≤ _
  rw [hNorm]
  calc
    _ ≤ eta*(∑ y : Y, wY y*‖g y‖^2)*
          (∑ x : X, wX x*‖f x‖^2) := hSource
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteUnionRareEndpointL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The ORIGINAL two-ended independent source03 probability
pair has a small bad-cell RAW contribution when E is the UNION
of a source rare event and a target rare event. Crucially the
complex tests may be arbitrary functions of their entire
physical endpoint states, and the phase H may depend on BOTH
endpoints but is pointwise unit-bounded. Bound:
  |E 1_(badX or badY) conj(f)gH|²
  ≤ 2(etaX+etaY) ||f||²||g||².
This is a true event-mass saving, not a false small
L²→L² restriction operator estimate. -/
theorem source_original_finite_union_rare_endpoint_L2_sq434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x, 0 ≤ wX x) (hwY : ∀ y, 0 ≤ wY y)
    (hmX : (∑ x : X, wX x) ≤ 1)
    (hmY : (∑ y : Y, wY y) ≤ 1)
    (badX : X → Prop) (badY : Y → Prop)
    (etaX etaY : ℝ) (hetaX : 0 ≤ etaX) (hetaY : 0 ≤ etaY)
    (hBadX : (∑ x : X,
      wX x*(if badX x then (1:ℝ) else 0)) ≤ etaX)
    (hBadY : (∑ y : Y,
      wY y*(if badY y then (1:ℝ) else 0)) ≤ etaY)
    (f : X → ℂ) (g : Y → ℂ) (H : X × Y → ℂ)
    (hH : ∀ q, ‖H q‖ ≤ 1) :
    ‖(∑ q : X × Y,
      ((wX q.1*wY q.2:ℝ):ℂ) *
        star (f q.1) * g q.2 *
        (if badX q.1 ∨ badY q.2 then H q else 0))‖^2 ≤
    2*(etaX+etaY) *
      (∑ x : X, wX x*‖f x‖^2) *
      (∑ y : Y, wY y*‖g y‖^2) := by
  classical
  let Htarget : X × Y → ℂ := fun q =>
    if badX q.1 then 0 else H q
  have hHtarget (q : X × Y) : ‖Htarget q‖ ≤ 1 := by
    by_cases hx : badX q.1
    · simp only [Htarget,if_pos hx,norm_zero]
      norm_num
    · simpa only [Htarget,if_neg hx] using hH q
  let zsrc : X × Y → ℂ := fun q =>
    ((wX q.1*wY q.2:ℝ):ℂ) *
      star (f q.1)*g q.2*
      (if badX q.1 then H q else 0)
  let ztgt : X × Y → ℂ := fun q =>
    ((wX q.1*wY q.2:ℝ):ℂ) *
      star (f q.1)*g q.2*
      (if badY q.2 then Htarget q else 0)
  let zall : X × Y → ℂ := fun q =>
    ((wX q.1*wY q.2:ℝ):ℂ) *
      star (f q.1)*g q.2*
      (if badX q.1 ∨ badY q.2 then H q else 0)
  have hSplit (q : X × Y) : zall q = zsrc q + ztgt q := by
    by_cases hx : badX q.1
    · simp [zall,zsrc,ztgt,Htarget,hx]
    · by_cases hy : badY q.2
      · simp [zall,zsrc,ztgt,Htarget,hx,hy]
      · simp [zall,zsrc,ztgt,Htarget,hx,hy]
  have hSum :
      (∑ q : X × Y, zall q) =
       (∑ q : X × Y, zsrc q) +
       (∑ q : X × Y, ztgt q) := by
    calc
      _ = ∑ q : X × Y, (zsrc q + ztgt q) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hSplit q
      _ = (∑ q : X × Y, zsrc q) +
          (∑ q : X × Y, ztgt q) := Finset.sum_add_distrib
  have hXSq :
      ‖∑ q : X × Y, zsrc q‖^2 ≤
      etaX * (∑ x : X, wX x*‖f x‖^2) *
         (∑ y : Y, wY y*‖g y‖^2) := by
    exact source_original_finite_source_rare_endpoint_L2_sq434
      wX wY hwX hwY hmY badX etaX hetaX hBadX f g H hH
  have hYSq :
      ‖∑ q : X × Y, ztgt q‖^2 ≤
      etaY * (∑ x : X, wX x*‖f x‖^2) *
         (∑ y : Y, wY y*‖g y‖^2) := by
    exact source_original_finite_target_rare_endpoint_L2_sq434
      wX wY hwX hwY hmX badY etaY hetaY hBadY
      f g Htarget hHtarget
  let SX : ℝ := ∑ x : X, wX x*‖f x‖^2
  let SY : ℝ := ∑ y : Y, wY y*‖g y‖^2
  let a : ℝ := ‖∑ q : X × Y, zsrc q‖
  let b : ℝ := ‖∑ q : X × Y, ztgt q‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hTri :
      ‖(∑ q : X × Y, zsrc q) +
         (∑ q : X × Y, ztgt q)‖ ≤ a+b :=
    norm_add_le _ _
  have hSq :
      ‖(∑ q : X × Y, zsrc q) +
         (∑ q : X × Y, ztgt q)‖^2 ≤ (a+b)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hTri 2
  have hTwo :
      (a+b)^2 ≤ 2*a^2+2*b^2 := by
    nlinarith [sq_nonneg (a-b)]
  change ‖∑ q : X × Y, zall q‖^2 ≤
    2*(etaX+etaY)*SX*SY
  rw [hSum]
  calc
    _ ≤ (a+b)^2 := hSq
    _ ≤ 2*a^2+2*b^2 := hTwo
    _ ≤ 2*(etaX*SX*SY)+2*(etaY*SX*SY) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hXSq (by norm_num))
        (mul_le_mul_of_nonneg_left hYSq (by norm_num))
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDyadDroppedL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Weighted two-ENDPOINT discarded-cell bilinear estimate
restricted to a chosen ORIGINAL pair of source/target product
dyads. The genuine physical endpoint law is nonnegative
and normalized, the bad-cell masks are arbitrary functions
of individual entire physical endpoint states, and H may
depend jointly on BOTH states. No fake operator smallness
on the rare event is claimed. Restricting arbitrary complex
endpoint tests to the dyads costs no L² energy. -/
theorem source_original_finite_dyad_masked_union_rare_L2_sq434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x, 0 ≤ wX x) (hwY : ∀ y, 0 ≤ wY y)
    (hmX : (∑ x : X, wX x) ≤ 1)
    (hmY : (∑ y : Y, wY y) ≤ 1)
    (dyadX : X → Prop) (dyadY : Y → Prop)
    (badX : X → Prop) (badY : Y → Prop)
    (etaX etaY : ℝ) (hetaX : 0 ≤ etaX) (hetaY : 0 ≤ etaY)
    (hBadX : (∑ x : X,
      wX x*(if badX x then (1:ℝ) else 0)) ≤ etaX)
    (hBadY : (∑ y : Y,
      wY y*(if badY y then (1:ℝ) else 0)) ≤ etaY)
    (f : X → ℂ) (g : Y → ℂ)
    (H : X × Y → ℂ) (hH : ∀ q, ‖H q‖ ≤ 1) :
    ‖(∑ q : X × Y,
      ((wX q.1*wY q.2:ℝ):ℂ)*
        star (f q.1)*g q.2*
        (if dyadX q.1 ∧ dyadY q.2 then
          (if badX q.1 ∨ badY q.2 then H q else 0)
         else 0))‖^2 ≤
    (2*(etaX+etaY)) *
      (∑ x : X, wX x*‖f x‖^2) *
      (∑ y : Y, wY y*‖g y‖^2) := by
  classical
  let f' : X → ℂ := fun x => if dyadX x then f x else 0
  let g' : Y → ℂ := fun y => if dyadY y then g y else 0
  let Hbad : X × Y → ℂ := fun q =>
    if badX q.1 ∨ badY q.2 then H q else 0
  have hRare := source_original_finite_union_rare_endpoint_L2_sq434
    wX wY hwX hwY hmX hmY badX badY
    etaX etaY hetaX hetaY hBadX hBadY f' g' H hH
  have hMask :=
    source_original_finite_two_ended_gate_mask_identity434
      wX wY f g dyadX dyadY Hbad
  let EX : ℝ := ∑ x : X, wX x*‖f x‖^2
  let EY : ℝ := ∑ y : Y, wY y*‖g y‖^2
  let EX' : ℝ := ∑ x : X, wX x*‖f' x‖^2
  let EY' : ℝ := ∑ y : Y, wY y*‖g' y‖^2
  have hEXle : EX' ≤ EX :=
    source_original_finite_gate_restricted_energy_le434
      wX hwX f dyadX
  have hEYle : EY' ≤ EY :=
    source_original_finite_gate_restricted_energy_le434
      wY hwY g dyadY
  have hEXnn : 0 ≤ EX := by
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (hwX x) (sq_nonneg _)
  have hEY'nn : 0 ≤ EY' := by
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (hwY y) (sq_nonneg _)
  have hEnergyBound : EX'*EY' ≤ EX*EY :=
    mul_le_mul hEXle hEYle hEY'nn hEXnn
  have hCoeff : 0 ≤ 2*(etaX+etaY) := by
    linarith
  have hBound :
      (2*(etaX+etaY))*EX'*EY' ≤
      (2*(etaX+etaY))*EX*EY := by
    calc
      _ = (2*(etaX+etaY))*(EX'*EY') := by ring
      _ ≤ (2*(etaX+etaY))*(EX*EY) :=
        mul_le_mul_of_nonneg_left hEnergyBound hCoeff
      _ = _ := by ring
  have hKernel (q : X × Y) :
      (if dyadX q.1 ∧ dyadY q.2 then
        (if badX q.1 ∨ badY q.2 then H q else 0)
       else 0) =
      (if dyadX q.1 ∧ dyadY q.2 then Hbad q else 0) := rfl
  have hWeighted :
      (∑ q : X × Y,
       ((wX q.1*wY q.2:ℝ):ℂ)*
         star (f' q.1)*g' q.2*
         (if badX q.1 ∨ badY q.2 then H q else 0)) =
      (∑ q : X × Y,
       ((wX q.1*wY q.2:ℝ):ℂ)*
         star (f q.1)*g q.2*
         (if dyadX q.1 ∧ dyadY q.2 then Hbad q else 0)) := by
    exact hMask
  have hEval :
      (∑ q : X × Y,
       ((wX q.1*wY q.2:ℝ):ℂ)*
         star (f q.1)*g q.2*
         (if dyadX q.1 ∧ dyadY q.2 then Hbad q else 0)) =
      (∑ q : X × Y,
       ((wX q.1*wY q.2:ℝ):ℂ)*
         star (f q.1)*g q.2*
         (if dyadX q.1 ∧ dyadY q.2 then
           (if badX q.1 ∨ badY q.2 then H q else 0)
          else 0)) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hKernel q]
  rw [←hEval,←hWeighted]
  exact (by change _ ≤ (2*(etaX+etaY))*EX'*EY' at hRare
            exact hRare.trans hBound)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteWeightedComplexKernelCS -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- True finite weighted complex Cauchy-Schwarz for an
arbitrarily coupled source/target auxiliary K0 multiplier.
Unlike a pointwise sup bound, this exposes the source-row
MEAN SQUARE of the actual signed K0 coefficient. -/
theorem source_original_finite_weighted_complex_kernel_CS434
    {T : Type} [Fintype T]
    (w : T → ℝ) (hw : ∀ t, 0 ≤ w t)
    (A F : T → ℂ) :
    ‖(∑ t : T, (w t:ℂ)*(A t*F t))‖^2 ≤
      (∑ t : T, w t*‖A t‖^2) *
      (∑ t : T, w t*‖F t‖^2) := by
  classical
  let u : T → ℝ := fun t => Real.sqrt (w t)*‖A t‖
  let v : T → ℝ := fun t => Real.sqrt (w t)*‖F t‖
  have hProd (t : T) :
      u t*v t = w t*(‖A t‖*‖F t‖) := by
    dsimp only [u,v]
    rw [mul_mul_mul_comm,←pow_two,Real.sq_sqrt (hw t)]
  have hSqU (t : T) :
      (u t)^2 = w t*‖A t‖^2 := by
    dsimp only [u]
    rw [mul_pow,Real.sq_sqrt (hw t)]
  have hSqV (t : T) :
      (v t)^2 = w t*‖F t‖^2 := by
    dsimp only [v]
    rw [mul_pow,Real.sq_sqrt (hw t)]
  have hTri :
      ‖(∑ t : T, (w t:ℂ)*(A t*F t))‖ ≤
        ∑ t : T, w t*(‖A t‖*‖F t‖) := by
    calc
      _ ≤ ∑ t : T, ‖(w t:ℂ)*(A t*F t)‖ :=
        norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [norm_mul,norm_mul,
          Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (hw t)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset T) u v
  calc
    _ ≤ (∑ t : T, w t*(‖A t‖*‖F t‖))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hTri 2
    _ = (∑ t : T, u t*v t)^2 := by
      apply congrArg (fun z : ℝ => z^2)
      apply Finset.sum_congr rfl
      intro t ht
      exact (hProd t).symm
    _ ≤ (∑ t : T, (u t)^2) *
          (∑ t : T, (v t)^2) := hCS
    _ = (∑ t : T, w t*‖A t‖^2) *
          (∑ t : T, w t*‖F t‖^2) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        exact hSqU t
      · apply Finset.sum_congr rfl
        intro t ht
        exact hSqV t
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteDensityKernelEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Finite density-kernel energy bound, including zero-mass fibres.
This is only the algebraic transfer lemma; physical row, column and
signed-compression premises are discharged in the original E wrapper. -/
theorem source_original_finite_density_kernel_energy434
    {X : Type} [DecidableEq X] (S : Finset X)
    (M : X → ℝ) (hM : ∀ x,0 ≤ M x)
    (A : X → X → ℝ) (hA : ∀ x y,0 ≤ A x y)
    (C D : ℝ) (hC : 0 ≤ C)
    (hr : ∀ x ∈ S,(∑ y ∈ S,A x y) ≤ C*M x)
    (hc : ∀ y ∈ S,(∑ x ∈ S,A x y) ≤ D*M y)
    (F T : X → ℂ)
    (ht : ∀ x ∈ S,M x*‖T x‖ ≤ ∑ y ∈ S,A x y*‖F y‖) :
    (∑ x ∈ S,M x*‖T x‖^2) ≤ C*D*∑ y ∈ S,M y*‖F y‖^2 := by
  have he (x) : 0 ≤ ∑ y ∈ S,A x y*‖F y‖^2 :=
    Finset.sum_nonneg (fun y _ => mul_nonneg (hA x y) (sq_nonneg _))
  have hx (x) (hxs : x ∈ S) :
      M x*‖T x‖^2 ≤ C*(∑ y ∈ S,A x y*‖F y‖^2) := by
    by_cases hz : M x=0
    · rw [hz,zero_mul]
      exact mul_nonneg hC (he x)
    · have hp : 0<M x := lt_of_le_of_ne (hM x) (Ne.symm hz)
      have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
        (s:=S) (r:=fun y => A x y*‖F y‖)
        (f:=fun y => A x y) (g:=fun y => A x y*‖F y‖^2)
        (fun y _ => hA x y) (fun y _ => mul_nonneg (hA x y) (sq_nonneg _))
        (fun y _ => by ring_nf;exact le_rfl)
      apply le_of_mul_le_mul_left (a:=M x) ?_ hp
      calc
        _ = (M x*‖T x‖)^2 := by ring
        _ ≤ (∑ y ∈ S,A x y*‖F y‖)^2 :=
          pow_le_pow_left₀ (mul_nonneg (hM x) (norm_nonneg _)) (ht x hxs) 2
        _ ≤ (∑ y ∈ S,A x y)*(∑ y ∈ S,A x y*‖F y‖^2) := hcs
        _ ≤ (C*M x)*(∑ y ∈ S,A x y*‖F y‖^2) :=
          mul_le_mul_of_nonneg_right (hr x hxs) (he x)
        _ = _ := by ring
  calc
    _ ≤ ∑ x ∈ S,C*(∑ y ∈ S,A x y*‖F y‖^2) :=
      Finset.sum_le_sum (fun x hx' => hx x hx')
    _ = C*(∑ y ∈ S,(∑ x ∈ S,A x y)*‖F y‖^2) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_mul]
    _ ≤ C*(∑ y ∈ S,(D*M y)*‖F y‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y hy =>
        mul_le_mul_of_nonneg_right (hc y hy) (sq_nonneg _))) hC
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBirthHistoryDensity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- A fresh batch remembers its unique predecessor, in numerical prime VALUES. -/
theorem source_original_birth_history_predecessor434
    (s t b : Finset ℕ) (hd : Disjoint s b) (hu : s ∪ b = t) :
    s = t \ b := by
  rw [← hu]
  ext p
  simp only [Finset.mem_sdiff,Finset.mem_union]
  have hn : p ∈ s → p ∉ b := fun hs hb => Finset.disjoint_left.mp hd hs hb
  tauto

def sourceOriginalBirthHistoryGate434 (births : List ℕ) (s t : Finset ℕ) : Prop :=
  births.Nodup ∧ Disjoint s births.toFinset ∧ s ∪ births.toFinset = t

theorem source_original_birth_history_row434
    (H : Finset (Finset ℕ)) (b : List ℕ) (s : Finset ℕ)
    (a : ℝ) (ha : 0 ≤ a) :
    (∑ t ∈ H, if sourceOriginalBirthHistoryGate434 b s t then a else 0) ≤ a := by
  classical
  calc
    _ ≤ ∑ t ∈ H, if s ∪ b.toFinset = t then a else 0 := by
      apply Finset.sum_le_sum
      intro t ht
      unfold sourceOriginalBirthHistoryGate434
      split_ifs <;> first | exact le_rfl | exact ha | tauto
    _ ≤ a := by
      by_cases hm : s ∪ b.toFinset ∈ H
      · rw [Finset.sum_eq_single (s ∪ b.toFinset)]
        · simp
        · intro t ht hne
          exact if_neg (Ne.symm hne)
        · exact fun hnot => False.elim (hnot hm)
      · have hz : (∑ t ∈ H,if s ∪ b.toFinset=t then a else 0)=0 := by
          apply Finset.sum_eq_zero
          intro t ht
          exact if_neg (fun (he : s ∪ b.toFinset = t) => hm (he.symm ▸ ht))
        rw [hz]
        exact ha

theorem source_original_birth_history_column434
    (H : Finset (Finset ℕ)) (b : List ℕ) (t : Finset ℕ)
    (a : ℝ) (ha : 0 ≤ a) :
    (∑ s ∈ H, if sourceOriginalBirthHistoryGate434 b s t then a else 0) ≤ a := by
  classical
  calc
    _ ≤ ∑ s ∈ H, if s = t \ b.toFinset then a else 0 := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases hg : sourceOriginalBirthHistoryGate434 b s t
      · rw [if_pos hg,if_pos
          (source_original_birth_history_predecessor434 s t b.toFinset hg.2.1 hg.2.2)]
      · rw [if_neg hg]
        split_ifs <;> first | exact ha | exact le_rfl
    _ ≤ a := by
      by_cases hm : t \ b.toFinset ∈ H
      · rw [Finset.sum_eq_single (t \ b.toFinset)]
        · simp
        · intro s hs hne
          exact if_neg hne
        · exact fun hnot => False.elim (hnot hm)
      · have hz : (∑ s ∈ H,if s=t \ b.toFinset then a else 0)=0 := by
          apply Finset.sum_eq_zero
          intro s hs
          exact if_neg (fun (he : s = t \ b.toFinset) => hm (he ▸ hs))
        rw [hz]
        exact ha

/-- The two marginal history bounds transfer an actual positive physical
kernel to counting measure on histories with NO history-cardinality loss. -/
theorem source_original_birth_history_density_energy434
    {α : Type} [DecidableEq α]
    (S : Finset α) (H : Finset (Finset ℕ))
    (M : α → ℝ) (hM : ∀ x,0 ≤ M x)
    (A : α → α → ℝ) (hA : ∀ x y,0 ≤ A x y)
    (B : α → Finset ℕ → α → Finset ℕ → ℝ)
    (hB : ∀ x s y t,0 ≤ B x s y t)
    (hbrow : ∀ x s y,(∑ t ∈ H,B x s y t) ≤ A x y)
    (hbcol : ∀ x y t,(∑ s ∈ H,B x s y t) ≤ A x y)
    (C D : ℝ) (hC : 0 ≤ C)
    (hr : ∀ x ∈ S,(∑ y ∈ S,A x y) ≤ C*M x)
    (hc : ∀ y ∈ S,(∑ x ∈ S,A x y) ≤ D*M y)
    (F T : α → Finset ℕ → ℂ)
    (ht : ∀ x ∈ S,∀ s ∈ H,
      M x*‖T x s‖ ≤ ∑ y ∈ S,∑ t ∈ H,B x s y t*‖F y t‖) :
    (∑ x ∈ S,∑ s ∈ H,M x*‖T x s‖^2) ≤
      C*D*(∑ y ∈ S,∑ t ∈ H,M y*‖F y t‖^2) := by
  let S' := S ×ˢ H
  let M' : α × Finset ℕ → ℝ := fun xs => M xs.1
  let A' : (α × Finset ℕ) → (α × Finset ℕ) → ℝ :=
    fun xs yt => B xs.1 xs.2 yt.1 yt.2
  have hr' : ∀ xs ∈ S',(∑ yt ∈ S',A' xs yt) ≤ C*M' xs := by
    intro xs hxs
    simp only [S',Finset.mem_product] at hxs
    simp only [S',A',Finset.sum_product]
    exact (Finset.sum_le_sum (fun y _ => hbrow xs.1 xs.2 y)).trans (hr xs.1 hxs.1)
  have hc' : ∀ yt ∈ S',(∑ xs ∈ S',A' xs yt) ≤ D*M' yt := by
    intro yt hyt
    simp only [S',Finset.mem_product] at hyt
    simp only [S',A',Finset.sum_product]
    exact (Finset.sum_le_sum (fun x _ => hbcol x yt.1 yt.2)).trans (hc yt.1 hyt.1)
  have ht' : ∀ xs ∈ S',M' xs*‖T xs.1 xs.2‖ ≤
      ∑ yt ∈ S',A' xs yt*‖F yt.1 yt.2‖ := by
    intro xs hxs
    simp only [S',Finset.mem_product] at hxs
    simpa only [S',A',M',Finset.sum_product] using ht xs.1 hxs.1 xs.2 hxs.2
  have hh := source_original_finite_density_kernel_energy434 S' M'
    (fun xs => hM xs.1) A' (fun xs yt => hB xs.1 xs.2 yt.1 yt.2)
    C D hC hr' hc' (fun yt => F yt.1 yt.2) (fun xs => T xs.1 xs.2) ht'
  simpa only [S',M',Finset.sum_product] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalIndependentL2Bilinear -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- A physically independent pair of actual labelled prime
probability laws transports a pointwise comparison error to a
weighted L2×L2 bilinear form for ARBITRARY complex tuple tests.
No restriction |f|≤1, no artificially factorized character
test, no cell count or number-of-prime-marks loss. The source
kernel error itself can depend arbitrarily on both target tuples. -/
theorem source_original_finite_independent_L2_error_bound434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (hwX : ∀ x, 0 ≤ wX x) (hwY : ∀ y, 0 ≤ wY y)
    (hmX : (∑ x : X, wX x) ≤ 1)
    (hmY : (∑ y : Y, wY y) ≤ 1)
    (f : X → ℂ) (g : Y → ℂ)
    (err : X × Y → ℂ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (herr : ∀ x : X, ∀ y : Y, ‖err (x,y)‖ ≤ eps) :
    ‖(∑ q : X × Y,
      ((wX q.1*wY q.2:ℝ):ℂ) *
        star (f q.1) * g q.2 * err q)‖^2 ≤
      eps^2 *
       (∑ x : X, wX x*‖f x‖^2) *
       (∑ y : Y, wY y*‖g y‖^2) := by
  classical
  let AX : ℝ := ∑ x : X, wX x*‖f x‖
  let AY : ℝ := ∑ y : Y, wY y*‖g y‖
  let SX : ℝ := ∑ x : X, wX x*‖f x‖^2
  let SY : ℝ := ∑ y : Y, wY y*‖g y‖^2
  let z : X × Y → ℂ := fun q =>
    ((wX q.1*wY q.2:ℝ):ℂ) *
      star (f q.1) * g q.2 * err q
  have hAXpos : 0 ≤ AX :=
    Finset.sum_nonneg (fun x hx =>
      mul_nonneg (hwX x) (norm_nonneg _))
  have hAYpos : 0 ≤ AY :=
    Finset.sum_nonneg (fun y hy =>
      mul_nonneg (hwY y) (norm_nonneg _))
  have hSXpos : 0 ≤ SX :=
    Finset.sum_nonneg (fun x hx =>
      mul_nonneg (hwX x) (sq_nonneg _))
  have hSYpos : 0 ≤ SY :=
    Finset.sum_nonneg (fun y hy =>
      mul_nonneg (hwY y) (sq_nonneg _))
  have hFactor :
      (∑ q : X × Y,
        (wX q.1*‖f q.1‖)*(wY q.2*‖g q.2‖)) = AX*AY := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ x : X, (wX x*‖f x‖) *
           (∑ y : Y, wY y*‖g y‖) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
      _ = AX*AY := by
        dsimp [AX,AY]
        rw [Finset.sum_mul]
  have hTerm (q : X × Y) :
      ‖z q‖ ≤ eps *
        ((wX q.1*‖f q.1‖)*(wY q.2*‖g q.2‖)) := by
    have hw : 0 ≤ wX q.1*wY q.2 :=
      mul_nonneg (hwX q.1) (hwY q.2)
    have hcoef :
        0 ≤ wX q.1*wY q.2*‖f q.1‖*‖g q.2‖ := by
      positivity
    have hNorm :
        ‖z q‖ = wX q.1*wY q.2*‖f q.1‖*‖g q.2‖*‖err q‖ := by
      simp only [z,norm_mul,norm_star,Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hwX q.1),
        abs_of_nonneg (hwY q.2)]
    rw [hNorm]
    calc
      _ ≤ wX q.1*wY q.2*‖f q.1‖*‖g q.2‖*eps :=
        mul_le_mul_of_nonneg_left (herr q.1 q.2) hcoef
      _ = _ := by ring
  have hNorm :
      ‖(∑ q : X × Y, z q)‖ ≤ eps*(AX*AY) := by
    calc
      _ ≤ ∑ q : X × Y, ‖z q‖ := norm_sum_le _ _
      _ ≤ ∑ q : X × Y,
          eps*((wX q.1*‖f q.1‖)*(wY q.2*‖g q.2‖)) :=
        Finset.sum_le_sum (fun q hq => hTerm q)
      _ = eps*(∑ q : X × Y,
          (wX q.1*‖f q.1‖)*(wY q.2*‖g q.2‖)) := by
        rw [Finset.mul_sum]
      _ = eps*(AX*AY) := by rw [hFactor]
  have hAX : AX^2 ≤ SX :=
    source_original_finite_weighted_l1_l2_sq434 wX f hwX hmX
  have hAY : AY^2 ≤ SY :=
    source_original_finite_weighted_l1_l2_sq434 wY g hwY hmY
  have hMassProduct : AX^2*AY^2 ≤ SX*SY :=
    mul_le_mul hAX hAY (sq_nonneg AY) hSXpos
  have hsq :
      ‖(∑ q : X × Y, z q)‖^2 ≤ (eps*(AX*AY))^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  change ‖(∑ q : X × Y, z q)‖^2 ≤ eps^2*SX*SY
  calc
    _ ≤ (eps*(AX*AY))^2 := hsq
    _ = eps^2*(AX^2*AY^2) := by ring
    _ ≤ eps^2*(SX*SY) :=
      mul_le_mul_of_nonneg_left hMassProduct (sq_nonneg _)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalVariableL2Error -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15500000

/-- TRUE SOURCE03 variable unshared-slot L² energy, with t_g
depending on the original ν-pattern and group; no artificial
fixed M or equality of different original prime supports. -/
noncomputable def sourceOriginalVariableBIGEnergy434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    (t : G → ℕ)
    (mu : (g : G) → BP g → ℝ)
    (f : SourceOriginalVariableBIGState434 BP t → ℂ) : ℝ :=
  ∑ x : SourceOriginalVariableBIGState434 BP t,
    sourceOriginalVariableBIGMass434 BP t mu x * Complex.normSq (f x)

/-- The SOURCE03 TRUE VARIABLE ν-pattern unshared source/target
physical state law lifts ANY pointwise signed-comparison error
to a bilinear weighted L² bound. Arbitrary complex endpoint
tests and arbitrary variable t_g are allowed. Positivity and
total mass follow from source physical 1/(pV_g) laws, without
new abstract probability axioms. Crucially, tests need not be
factorized across the BIG prime-group coordinates. -/
theorem source_original_true_variable_BIG_L2_error434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    (t : G → ℕ)
    (prime : (g : G) → BP g → ℕ) (V : G → ℝ)
    (hVpos : ∀ g, 0 < V g)
    (hVEq : ∀ g, V g = ∑ p : BP g, 1/(prime g p:ℝ))
    (f g : SourceOriginalVariableBIGState434 BP t → ℂ)
    (err : (SourceOriginalVariableBIGState434 BP t) ×
           (SourceOriginalVariableBIGState434 BP t) → ℂ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (herr : ∀ a b, ‖err (a,b)‖ ≤ eps) :
    ‖(∑ ab : (SourceOriginalVariableBIGState434 BP t) ×
                  (SourceOriginalVariableBIGState434 BP t),
        ((sourceOriginalVariableBIGMass434 BP t
          (sourceOriginalJointHarmonicMu434 BP prime V) ab.1 *
          sourceOriginalVariableBIGMass434 BP t
          (sourceOriginalJointHarmonicMu434 BP prime V) ab.2 : ℝ):ℂ) *
         star (f ab.1) * g ab.2 * err ab)‖^2 ≤
      eps^2 *
        sourceOriginalVariableBIGEnergy434 BP t
          (sourceOriginalJointHarmonicMu434 BP prime V) f *
        sourceOriginalVariableBIGEnergy434 BP t
          (sourceOriginalJointHarmonicMu434 BP prime V) g := by
  classical
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let w : SourceOriginalVariableBIGState434 BP t → ℝ :=
    sourceOriginalVariableBIGMass434 BP t mu
  obtain ⟨hmuPos,hmuTotal⟩ :=
    source_original_joint_harmonic_normalized434
      BP prime V hVpos hVEq
  have hw (a : SourceOriginalVariableBIGState434 BP t) : 0 ≤ w a :=
    source_original_variable_BIG_mass_nonneg434 BP t mu hmuPos a
  have hmass : (∑ a : SourceOriginalVariableBIGState434 BP t, w a) ≤ 1 :=
    le_of_eq (source_original_variable_BIG_law_total434 BP t mu hmuTotal)
  have hBound := source_original_finite_independent_L2_error_bound434
    w w hw hw hmass hmass f g err eps heps herr
  simpa only [w, mu, sourceOriginalVariableBIGEnergy434,
    Complex.normSq_eq_norm_sq] using hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalVariableRetainedL2Error -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Source03 signed comparison is only small on RETAINED pairs
of its two original GLOBAL product-log cells. This theorem
correctly zeroes the discarded pairs before applying the
TRUE ν-dependent physical variable-slot L² bound, rather than
falsely claiming a global pointwise error bound on dropped cells.
Both endpoint tests can be arbitrary complex functions of ALL
original group-dependent unshared slots. -/
theorem source_original_true_variable_BIG_retained_L2_error434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    (t : G → ℕ)
    (prime : (g : G) → BP g → ℕ) (V : G → ℝ)
    (hVpos : ∀ g, 0 < V g)
    (hVEq : ∀ g, V g = ∑ p : BP g, 1/(prime g p:ℝ))
    (sourceTest targetTest :
       SourceOriginalVariableBIGState434 BP t → ℂ)
    (gateSource gateTarget : SourceOriginalVariableBIGState434 BP t → Prop)
    (err : (SourceOriginalVariableBIGState434 BP t) ×
           (SourceOriginalVariableBIGState434 BP t) → ℂ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (herr : ∀ s t, gateSource s → gateTarget t →
      ‖err (s,t)‖ ≤ eps) :
    ‖(∑ ab : (SourceOriginalVariableBIGState434 BP t) ×
                  (SourceOriginalVariableBIGState434 BP t),
        ((sourceOriginalVariableBIGMass434 BP t
          (sourceOriginalJointHarmonicMu434 BP prime V) ab.1 *
          sourceOriginalVariableBIGMass434 BP t
          (sourceOriginalJointHarmonicMu434 BP prime V) ab.2 : ℝ):ℂ) *
          star (sourceTest ab.1) * targetTest ab.2 *
          (if gateSource ab.1 ∧ gateTarget ab.2 then err ab else 0))‖^2 ≤
      eps^2 *
        sourceOriginalVariableBIGEnergy434 BP t
          (sourceOriginalJointHarmonicMu434 BP prime V) sourceTest *
        sourceOriginalVariableBIGEnergy434 BP t
          (sourceOriginalJointHarmonicMu434 BP prime V) targetTest := by
  classical
  let masked : (SourceOriginalVariableBIGState434 BP t) ×
      (SourceOriginalVariableBIGState434 BP t) → ℂ := fun ab =>
    if gateSource ab.1 ∧ gateTarget ab.2 then err ab else 0
  have hMasked : ∀ a b, ‖masked (a,b)‖ ≤ eps := by
    intro a b
    by_cases hab : gateSource a ∧ gateTarget b
    · simpa only [masked, if_pos hab] using
        herr a b hab.1 hab.2
    · simp only [masked, if_neg hab, norm_zero]
      exact heps
  exact source_original_true_variable_BIG_L2_error434 BP t prime V
    hVpos hVEq sourceTest targetTest masked eps heps hMasked
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePhysicalEnergyNormBridge -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exactly the source03 ν-variable harmonic physical L2 energy
in its real-weighted complex norm form. No norm upgrade or
extra moment bound: Complex.normSq equals the actual squared norm
of the same full physical endpoint mark test. -/
theorem source_original_true_variable_BIG_energy_norm434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)]
    [∀ g, DecidableEq (BP g)]
    (t : G → ℕ)
    (mu : (g : G) → BP g → ℝ)
    (f : SourceOriginalVariableBIGState434 BP t → ℂ) :
    sourceOriginalVariableBIGEnergy434 BP t mu f =
      ∑ s : SourceOriginalVariableBIGState434 BP t,
        sourceOriginalVariableBIGMass434 BP t mu s * ‖f s‖^2 := by
  unfold sourceOriginalVariableBIGEnergy434
  simp only [Complex.normSq_eq_norm_sq]
end Green64Analytic.CorrelationSquare

end

