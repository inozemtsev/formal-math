module

public import Green64.Library.Sieve.Foundations.Part011
public import Green64.Library.Sieve.Foundations.Part010
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Green64.Library.Sieve.Foundations.Part009
public import Green64.Library.Weights.Part112
public import Green64.Library.Weights.Part107
public import Green64.Library.Weights.Part108

@[expose] public section

/-!
# Sieve / Foundations / Part012

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalSignedWindowHProduct -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The genuine original Parity (4.5) allocated selected-e window,
as a predicate on an INTEGER source e. Its lower endpoint is
E L^-88, no fictitious pointwise Fourier compact support. -/
def parityOriginalHistoricalEWindow434 (L E : ℝ) (e : ℕ) : Prop :=
  E*L^((-88:ℝ)) ≤ (e:ℝ) ∧ (e:ℝ) ≤ E

/-- ORIGINAL physically supported reserved-p + full Q Fourier
coefficient at integer u with the COMPLETE source Q-product gate
`p*prod(nonreserved labelled Q)=ordinaryPart(P,u)`. No other
coefficients or original factorials are modified. -/
def parityOriginalReservedFullQPhysicalWindowGate434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (σ : ℝ) (u : ℕ) : ℂ :=
  ∑ p ∈ sourceOriginalQActualBands 20 d L band,
    ∑ rest : ((i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length) →
      {q : ℕ // q ∈ sourceActualSortedQ 20 d L band slot i}),
      if parityOriginalHistoricalEWindow434 L E (paritySourceOrderedAllocatedE434 δ rest) ∧
          p*(∏ i, (rest i).val)=
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
theorem parity_original_reserved_fullQ_window_gate_eq_selected_H434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ)
    (u : ℕ) :
    parityOriginalReservedFullQPhysicalWindowGate434 d L E band slot δ ξ σ u =
      ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
        if parityOriginalHistoricalEWindow434 L E z.1 ∧ z.1*z.2 = sourceOriginalOrdinaryPart
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
    fun a => if parityOriginalHistoricalEWindow434 L E (g a).1 ∧ (g a).1*(g a).2=target then w a else 0
  have hFiber (z : ℕ×ℕ) :
      parityOriginalReservedTwoEndpointFibre434 S g wGate z =
      if parityOriginalHistoricalEWindow434 L E z.1 ∧ z.1*z.2=target then
        parityOriginalReservedTwoEndpointFibre434 S g w z else 0 := by
    unfold parityOriginalReservedTwoEndpointFibre434
    by_cases hg : parityOriginalHistoricalEWindow434 L E z.1 ∧ z.1*z.2=target
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
      parityOriginalReservedFullQPhysicalWindowGate434 d L E band slot δ ξ σ u := by
    unfold S parityOriginalReservedFullQPhysicalWindowGate434
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
      if parityOriginalHistoricalEWindow434 L E z.1 ∧ z.1*z.2=target then
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

/-! ## ActualFullQFourierL1Measure -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Equality of the FULL N-dimensional Lebesgue integral of the norm of
Parity's original history-dependent buffered Q-allocation Fourier
integrand, and the exact branch Fourier L1 variation.  The complex
phase depends on preceding delta and its actual prime tuple, but has
unit norm; no independence assumption is made about original residuals.
This is the actual measure-level content of the source Parity (4.6). -/
theorem parity_original_actual_fullQ_gate_integrand_L1_eq_branch434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ)
    (δ : Fin N → Bool) (p : Fin N → ℕ) :
    (∫ ξ : Fin N → ℝ,
      ‖parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ‖) =
      parityOriginalB590FourierBranchVariation434 δ := by
  simp_rw [parity_original_B590_all_gate_integrand_norm_exact434 E s]
  unfold parityOriginalB590FourierBranchVariation434
  exact MeasureTheory.integral_fin_nat_prod_volume_eq_prod
    (fun i : Fin N => fun t : ℝ =>
      ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) t‖)

/-- At the REAL source Q-band and reserved slot, the full Lebesgue
L1 mass across every original Boolean allocation branch is at most
L^Cf. This is a uniform bound even if the history-dependent prime
tuple p_delta is chosen separately for each delta. Neither K0 nor
requested spectral accuracy appears in Cf. It uses the actual
20-band gate Schwartz kernel and actual full-dimensional product
measure, not an abstract unweighted count of assignments. -/
theorem parity_eventually_original_actual_fullQ_fourier_L1_variation_measure_polylog434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ),
        let N := (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length
        let s := sourceActualSortedFrequencyScales 20
          (sourceOriginalLiteralDepth 20 L) L band slot
        ∀ p : (Fin N → Bool) → Fin N → ℕ,
          (∑ δ : Fin N → Bool,
            (∫ ξ : Fin N → ℝ,
              ‖parityOriginalB590AllGateFourierIntegrand434
                E s δ (p δ) ξ‖)) ≤
          L^parityOriginalB590FixedFourierPolynomialExponent434 := by
  filter_upwards [parity_eventually_original_B590_actual_full_fourier_variation_polylog434]
    with L hL
  intro band slot E
  dsimp only
  intro p
  let N : ℕ := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
    band slot).length
  let s := sourceActualSortedFrequencyScales 20
    (sourceOriginalLiteralDepth 20 L) L band slot
  calc
    (∑ δ : Fin N → Bool,
      (∫ ξ : Fin N → ℝ,
        ‖parityOriginalB590AllGateFourierIntegrand434 E s δ (p δ) ξ‖)) =
      ∑ δ : Fin N → Bool, parityOriginalB590FourierBranchVariation434 δ := by
        apply Finset.sum_congr rfl
        intro δ _
        exact parity_original_actual_fullQ_gate_integrand_L1_eq_branch434 E s δ (p δ)
    _ ≤ L^parityOriginalB590FixedFourierPolynomialExponent434 := hL band slot
end Green64Analytic.Parity

end

end

/-! ## ActualFullQWeightedIntegralBound -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- In the full N-dimensional actual source f0/f1 Fourier measure,
all signed physically weighted branch amplitudes can be integrated
without paying another 2^N factor. This is a direct bound on the
complex finite assignment / full real-frequency integral. The
hypotheses on F explicitly express measurability and a UNIFORM
pointwise spectral bound, not an assumed TypeII theorem. The
source gate is exactly Parity's history-dependent one. -/
theorem parity_original_actual_fullQ_weighted_integral_bound434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ)
    (p : (Fin N → Bool) → Fin N → ℕ)
    (F : (Fin N → Bool) → (Fin N → ℝ) → ℂ)
    (M : ℝ) (hM : 0≤M)
    (hMeas : ∀ δ, AEStronglyMeasurable (F δ))
    (hBound : ∀δ ξ, ‖F δ ξ‖≤M) :
    ‖∑ δ : Fin N → Bool,
        ∫ ξ : Fin N → ℝ,
          parityOriginalB590AllGateFourierIntegrand434 E s δ (p δ) ξ *
            F δ ξ‖ ≤
      M * (∑ δ : Fin N → Bool,
        ∫ ξ : Fin N → ℝ,
          ‖parityOriginalB590AllGateFourierIntegrand434 E s δ (p δ) ξ‖) := by
  classical
  let A : (Fin N → Bool) → (Fin N → ℝ) → ℂ := fun δ ξ =>
    parityOriginalB590AllGateFourierIntegrand434 E s δ (p δ) ξ
  have hAI : ∀δ,Integrable (A δ) := by
    intro δ
    exact parity_original_B590_all_gate_fourier_product_integrable434 E s δ (p δ)
  have hP : ∀δ ξ, ‖A δ ξ * F δ ξ‖≤M*‖A δ ξ‖ := by
    intro δ ξ
    rw [norm_mul]
    have hh := mul_le_mul_of_nonneg_left (hBound δ ξ)
      (norm_nonneg (A δ ξ))
    simpa only [mul_comm] using hh
  have hAF : ∀δ,Integrable (fun ξ => A δ ξ * F δ ξ) := by
    intro δ
    have hMeasProd : AEStronglyMeasurable (fun ξ => A δ ξ * F δ ξ) :=
      (hAI δ).aestronglyMeasurable.mul (hMeas δ)
    apply ((hAI δ).norm.const_mul M).mono hMeasProd
    filter_upwards [] with ξ
    have hp := hP δ ξ
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hM,
      abs_of_nonneg (norm_nonneg _)] using hp
  have hCell : ∀δ,
      ‖∫ ξ : Fin N → ℝ, A δ ξ*F δ ξ‖ ≤
        M * (∫ ξ : Fin N → ℝ, ‖A δ ξ‖) := by
    intro δ
    calc
      _ ≤ ∫ ξ : Fin N → ℝ, ‖A δ ξ*F δ ξ‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ ξ : Fin N → ℝ, M*‖A δ ξ‖ := by
        apply integral_mono (hAF δ).norm ((hAI δ).norm.const_mul M)
        intro ξ
        exact hP δ ξ
      _ = M*(∫ ξ : Fin N → ℝ,‖A δ ξ‖) := integral_const_mul _ _
  calc
    _ ≤ ∑ δ : Fin N → Bool,
        ‖∫ ξ : Fin N → ℝ, A δ ξ*F δ ξ‖ := norm_sum_le _ _
    _ ≤ ∑ δ : Fin N → Bool,
        M*(∫ ξ : Fin N → ℝ,‖A δ ξ‖) := by
      apply Finset.sum_le_sum
      intro δ _
      exact hCell δ
    _ = M*(∑ δ : Fin N → Bool,
        ∫ ξ : Fin N → ℝ,‖A δ ξ‖) := by rw [Finset.mul_sum]

/-- Original Parity §4.2 global source Fourier variation bound is
sufficient to absorb ALL actual N-dimensional allocation branches of
a signed, strongly measurable and uniformly bounded spectral family.
The source Q-band and slot, original N, full history-dependent
p_delta, and original fixed C_f are kept literal.  Application to
Bprime's actual ξ-dependent physical signal additionally requires a
proof of its measurability and its uniform on-box spectral range. -/
theorem parity_eventually_original_actual_fullQ_weighted_integral_polylog434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ),
        let N := (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length
        let s := sourceActualSortedFrequencyScales 20
          (sourceOriginalLiteralDepth 20 L) L band slot
        ∀ (p : (Fin N → Bool) → Fin N → ℕ)
          (F : (Fin N → Bool) → (Fin N → ℝ) → ℂ)
          (M : ℝ),
          0≤M →
          (∀δ, AEStronglyMeasurable (F δ)) →
          (∀δ ξ, ‖F δ ξ‖≤M) →
          ‖∑δ : Fin N → Bool,
              ∫ ξ : Fin N → ℝ,
                parityOriginalB590AllGateFourierIntegrand434
                  E s δ (p δ) ξ * F δ ξ‖ ≤
            M * L^parityOriginalB590FixedFourierPolynomialExponent434 := by
  filter_upwards [parity_eventually_original_actual_fullQ_fourier_L1_variation_measure_polylog434]
    with L hMass
  intro band slot E
  dsimp only
  intro p F M hM hMeas hBound
  let N : ℕ := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
    band slot).length
  let s := sourceActualSortedFrequencyScales 20
    (sourceOriginalLiteralDepth 20 L) L band slot
  have hActual := parity_original_actual_fullQ_weighted_integral_bound434
    E s p F M hM hMeas hBound
  have hVar := hMass band slot E p
  exact hActual.trans (mul_le_mul_of_nonneg_left hVar hM)
end Green64Analytic.Parity

end

end

/-! ## ActualFullQFourierBoxIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The finite SOURCE Q-frequency cube for Parity's true sorted N
allocation coordinates. It is a genuine measurable product box,
not a new hard cutoff on natural e,n,m,m',z. -/
def parityOriginalActualFullQFrequencyCube434 {N : ℕ} (T : ℝ) :
    Set (Fin N → ℝ) :=
  {ξ | ∀ i : Fin N, ξ i ∈ Set.Icc (-T) T}

theorem parity_original_actual_fullQ_frequency_cube_measurable434
    {N : ℕ} (T : ℝ) :
    MeasurableSet (parityOriginalActualFullQFrequencyCube434 (N:=N) T) := by
  have hEq : parityOriginalActualFullQFrequencyCube434 (N:=N) T =
      ⋂ i : Fin N, (fun ξ : Fin N → ℝ => ξ i) ⁻¹' (Set.Icc (-T) T) := by
    ext ξ
    simp [parityOriginalActualFullQFrequencyCube434]
  rw [hEq]
  exact MeasurableSet.iInter (fun i =>
    (measurable_pi_apply i) measurableSet_Icc)

/-- Literal N-dimensional original buffered-gate Fourier BOX: the
complex signed sum across every delta and the real truncated cube
has norm at most M times the FULL untruncated original source
Fourier gate L1 mass.  A bound on F is needed ONLY inside the cube;
no assertion about outside shifted spectral frequencies is required.
The complete character projector must be included in F before use. -/
theorem parity_original_actual_fullQ_weighted_box_integral_bound434
    {N : ℕ} (E T : ℝ) (s : Fin N → ℝ)
    (p : (Fin N → Bool) → Fin N → ℕ)
    (F : (Fin N → Bool) → (Fin N → ℝ) → ℂ)
    (M : ℝ) (hM : 0≤M)
    (hMeas : ∀δ, AEStronglyMeasurable (F δ))
    (hBound : ∀δ ξ,
      ξ ∈ parityOriginalActualFullQFrequencyCube434 T → ‖F δ ξ‖≤M) :
    ‖∑ δ : Fin N → Bool,
        ∫ ξ in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalB590AllGateFourierIntegrand434 E s δ (p δ) ξ *
            F δ ξ‖ ≤
      M * (∑ δ : Fin N → Bool,
        ∫ ξ : Fin N → ℝ,
          ‖parityOriginalB590AllGateFourierIntegrand434 E s δ (p δ) ξ‖) := by
  classical
  let S := parityOriginalActualFullQFrequencyCube434 (N:=N) T
  have hS : MeasurableSet S :=
    parity_original_actual_fullQ_frequency_cube_measurable434 T
  let G : (Fin N → Bool) → (Fin N → ℝ) → ℂ := fun δ =>
    S.indicator (F δ)
  have hGM : ∀δ, AEStronglyMeasurable (G δ) := by
    intro δ
    exact (hMeas δ).indicator hS
  have hGB : ∀δ ξ, ‖G δ ξ‖≤M := by
    intro δ ξ
    by_cases hξ : ξ∈S
    · simp only [G,Set.indicator_of_mem hξ]
      exact hBound δ ξ hξ
    · simp [G,Set.indicator,hξ,hM]
  have hFull := parity_original_actual_fullQ_weighted_integral_bound434
    E s p G M hM hGM hGB
  have hEq :
      (∑δ : Fin N → Bool,
          ∫ ξ in S,
            parityOriginalB590AllGateFourierIntegrand434 E s δ (p δ) ξ * F δ ξ) =
      ∑δ : Fin N → Bool,
          ∫ ξ : Fin N → ℝ,
            parityOriginalB590AllGateFourierIntegrand434 E s δ (p δ) ξ * G δ ξ := by
    apply Finset.sum_congr rfl
    intro δ _
    rw [←integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [] with ξ
    exact Set.indicator_mul_right S
      (parityOriginalB590AllGateFourierIntegrand434 E s δ (p δ)) (F δ)
  change ‖∑δ : Fin N → Bool,∫ξ in S,
    parityOriginalB590AllGateFourierIntegrand434 E s δ (p δ) ξ * F δ ξ‖ ≤ _
  rw [hEq]
  exact hFull
end Green64Analytic.Parity

end

end

/-! ## ActualQFourierBoxMeasureExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- EXACT equality of the historical Parity(4.7) original measured
N-dimensional Fourier BOX (product of the original ONE-DIMENSIONAL
restricted Lebesgue measures) and the source physical model's true
volume restricted to the original cube [-T,T]^N. No arbitrary product
normalization factor, determinant or complex-amplitude monotonicity
is inserted. This is needed when matching old source Mellin-Cauchy
Q integrals to the newer positive full-Q cube norm estimate. -/
theorem parity_original_Q_fourier_product_restrict_measure_eq_cube434
    {n : ℕ} (T : ℝ) :
    (Measure.pi (fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Icc (-T) T))) =
      (volume : Measure (Fin n → ℝ)).restrict
        (parityOriginalActualFullQFrequencyCube434 (N:=n) T) := by
  have hCube :
      parityOriginalActualFullQFrequencyCube434 (N:=n) T =
        Set.univ.pi (fun _ : Fin n => Set.Icc (-T) T) := by
    ext xi
    simp [parityOriginalActualFullQFrequencyCube434,Set.mem_pi,Pi.le_def,forall_and]
  rw [hCube]
  change (Measure.pi (fun _ : Fin n =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))) =
    (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ : Fin n => Set.Icc (-T) T))
  exact (Measure.restrict_pi_pi
    (μ := fun _ : Fin n => (volume : Measure ℝ))
    (fun _ : Fin n => Set.Icc (-T) T)).symm

/-- The EXACT historical Parity finite-Q Fourier integral against the
original real N-dimensional product restricted Lebesgue measure is
the same complex number as the SOURCE volume-integral over its
literal full Q cube. This is a measure identity, not a positivity
or an analytic TypeII statement. -/
theorem parity_original_Q_fourier_product_box_integral_eq_cube434
    {n : ℕ} (T : ℝ) (F : (Fin n → ℝ) → ℂ) :
    (∫ xi : Fin n → ℝ, F xi
      ∂(Measure.pi (fun _ : Fin n =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T)))) =
      ∫ xi in parityOriginalActualFullQFrequencyCube434 (N:=n) T, F xi := by
  rw [parity_original_Q_fourier_product_restrict_measure_eq_cube434 T]
end Green64Analytic.Parity

end

end

/-! ## SelectedQFourierKernel -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The CORRECT ORIGINAL Parity §4.2 exterior Fourier kernel after
QSkip physical residual has been moved inside B509/B633: all genuine
Schwartz f0/f1 transforms, the common log(E) character, and only the
selected-e Q slot phase. The omitted skipped-Q phase is already
inside `sourceNativePrimeCore.residual`, and must NOT be multiplied
a second time when applying the original Fourier L1 budget. -/
def parityOriginalActualSelectedQFourierKernel434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (E : ℝ) (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q∈Q i}) : ℂ :=
  (∏ i : Fin n,
    (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
  ((Real.fourierChar (Real.log E * (∑ i : Fin n, ξ i / s i)) : Circle) : ℂ) *
  paritySourceAllocatedSlotFourierPhase434 s ξ δ p

/-- The complete source Fourier phase and ONLY one QSkip phase
reassemble to the literal original B590 (4.6) complex kernel.
It is an exact equality for every original repeated labelled prime
tuple and every history-dependent δ/ξ, not an approximate
cancellation or a pointwise χ-vanishing statement. -/
theorem parity_original_actual_selected_kernel_times_skip_eq_full434
    {n : ℕ} {Q : Fin n → Finset ℕ} (E : ℝ)
    (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q∈Q i}) :
    parityOriginalActualSelectedQFourierKernel434 E s ξ δ p *
      orderedSkipPhase (δ:=δ) s ξ
        (fun i : {i : Fin n // ¬δ i=true} => p i.val) =
    parityOriginalB590AllGateFourierIntegrand434 E s δ (fun i => (p i).val) ξ := by
  simpa only [parityOriginalActualSelectedQFourierKernel434] using
    (parity_original_B590_all_gate_integrand_selected_skipped434 E s ξ δ p).symm

/-- Every genuine ordered-QSkip source prime phase has unit norm;
its multiplicity and source factorial weight belong in the B509
residual, but the frequency-phase modulus adds no analytic cost. -/
theorem parity_original_actual_ordered_skip_fourier_norm_one434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (a : OrderedQSkip n Q δ) :
    ‖orderedSkipPhase s ξ a‖=1 := by
  unfold orderedSkipPhase
  rw [norm_prod]
  simp

/-- The source-correct selected-only kernel has EXACTLY the same
pointwise L1 density as Parity(4.6) full Q kernel. Therefore the entire
Q Fourier L1 variation can be paid once even though the physical
QSkip prime coefficient is already inside Bprime. -/
theorem parity_original_actual_selected_kernel_norm_eq_full434
    {n : ℕ} {Q : Fin n → Finset ℕ} (E : ℝ)
    (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q∈Q i}) :
    ‖parityOriginalActualSelectedQFourierKernel434 E s ξ δ p‖ =
    ‖parityOriginalB590AllGateFourierIntegrand434 E s δ
       (fun i => (p i).val) ξ‖ := by
  have hSplit := parity_original_actual_selected_kernel_times_skip_eq_full434 E s ξ δ p
  have hSkip := parity_original_actual_ordered_skip_fourier_norm_one434
    s ξ δ (fun i : {i : Fin n // ¬δ i=true} => p i.val)
  rw [←hSplit,norm_mul,hSkip,mul_one]

/-- Explicitly retain the original f0/f1 gate Fourier densities:
there is no skipped-prime-count factor in the correct selected-only
kernel, and neither the real Mellin frequencies nor the r20 source
labels change the numerical Fourier norm. -/
theorem parity_original_actual_selected_kernel_norm_gate_product434
    {n : ℕ} {Q : Fin n → Finset ℕ} (E : ℝ)
    (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q∈Q i}) :
    ‖parityOriginalActualSelectedQFourierKernel434 E s ξ δ p‖ =
      ∏ i : Fin n,
        ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖ := by
  rw [parity_original_actual_selected_kernel_norm_eq_full434]
  exact parity_original_B590_all_gate_integrand_norm_exact434 E s ξ δ
    (fun i => (p i).val)
end Green64Analytic.Parity

end

end

/-! ## PostCauchyQGate -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The SOURCE-correct Fourier gate AFTER original Parity (4.10)
Cauchy has removed a_e, including its selected-Q prime phase:
the fixed Schwartz f0/f1 Fourier product and common log E phase.
The skipped-Q phase is already in sourceNativePrimeCore.residual.
Unlike the earlier selected-only gate, this does not carry an
extraneous chosen selected-e Q-prime tuple into the post-Cauchy
physical all-odd e correlation. An exact source A→Cauchy operator
identity remains a separate obligation. -/
def parityOriginalActualPostCauchyQGate434
    {n : ℕ} (E : ℝ) (s ξ : Fin n → ℝ) (δ : Fin n → Bool) : ℂ :=
  (∏ i : Fin n,
    (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
  ((Real.fourierChar
    (Real.log E * (∑ i : Fin n, ξ i / s i)) : Circle) : ℂ)

/-- The old selected-only exterior kernel is exactly the post-Cauchy
Fourier gate times the selected-e Q phase that belongs inside a_e
BEFORE Cauchy. Thus putting a selected-Q phase outside the already
enlarged full-odd off-diagonal is not the literal Parity (4.10) source
formula, even though it has the same analytic absolute norm. -/
theorem parity_original_actual_selected_gate_eq_post_cauchy_mul_selected_phase434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (E : ℝ) (s ξ : Fin n → ℝ) (δ : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q∈Q i}) :
    parityOriginalActualSelectedQFourierKernel434 E s ξ δ p =
      parityOriginalActualPostCauchyQGate434 E s ξ δ *
        paritySourceAllocatedSlotFourierPhase434 s ξ δ p := by
  rfl

/-- SOURCE: the post-Cauchy Q gate has exactly the original Schwartz
Fourier transform product as absolute density, for every literal
sorted Q label and Boolean allocation. The common Fourier character
is unitary. No original Q prime tuple is needed after Cauchy. -/
theorem parity_original_actual_post_cauchy_Q_gate_norm434
    {n : ℕ} (E : ℝ) (s ξ : Fin n → ℝ) (δ : Fin n → Bool) :
    ‖parityOriginalActualPostCauchyQGate434 E s ξ δ‖ =
      ∏ i : Fin n,
        ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖ := by
  unfold parityOriginalActualPostCauchyQGate434
  rw [norm_mul, Circle.norm_coe, mul_one, norm_prod]

/-- The genuine post-Cauchy gate remains jointly continuous in all
N real frequency variables, with exactly the source 2π Fourier
character and original f0/f1 smooth buffered profiles. -/
theorem parity_original_actual_post_cauchy_Q_gate_continuous434
    {n : ℕ} (E : ℝ) (s : Fin n → ℝ) (δ : Fin n → Bool) :
    Continuous (fun ξ : Fin n → ℝ =>
      parityOriginalActualPostCauchyQGate434 E s ξ δ) := by
  unfold parityOriginalActualPostCauchyQGate434
  fun_prop

/-- Actual finite-product Lebesgue integrability of the entire
phase-free Parity(4.10) external Fourier gate (NOT a bounded-box-only
assumption). Its scalar factors are the real source Schwartz Fourier
transforms, so no prime tuple or residual smallness hypothesis enters. -/
theorem parity_original_actual_post_cauchy_Q_gate_integrable434
    {n : ℕ} (E : ℝ) (s : Fin n → ℝ) (δ : Fin n → Bool) :
    Integrable (fun ξ : Fin n → ℝ => parityOriginalActualPostCauchyQGate434 E s ξ δ) := by
  let G : Fin n → 𝓢(ℝ,ℂ) := fun i =>
    (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ))
  have hProd : Integrable (fun ξ : Fin n → ℝ =>
      ∏ i : Fin n,G i (ξ i)) :=
    Integrable.fin_nat_prod (fun i => (G i).integrable)
  have hCont := parity_original_actual_post_cauchy_Q_gate_continuous434 E s δ
  apply hProd.mono hCont.aestronglyMeasurable
  filter_upwards [] with ξ
  rw [parity_original_actual_post_cauchy_Q_gate_norm434 E s]
  simp only [G, norm_prod, le_refl]

/-- Genuine full real ℝ^N Fourier L1 variation of the post-Cauchy
phase-free gate is EXACTLY the original one-branch Parity(4.6)
Schwartz Fourier variation. In particular it already accounts for
all Boolean branches at once, without summing over an artificial
selected-e prime tuple. -/
theorem parity_original_actual_post_cauchy_Q_gate_L1_branch_exact434
    {n : ℕ} (E : ℝ) (s : Fin n → ℝ) (δ : Fin n → Bool) :
    (∫ ξ : Fin n → ℝ,
      ‖parityOriginalActualPostCauchyQGate434 E s ξ δ‖) =
      parityOriginalB590FourierBranchVariation434 δ := by
  simp_rw [parity_original_actual_post_cauchy_Q_gate_norm434 E s]
  unfold parityOriginalB590FourierBranchVariation434
  exact MeasureTheory.integral_fin_nat_prod_volume_eq_prod
    (fun i : Fin n => fun t : ℝ =>
      ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) t‖)

/-- All original Q bands and reserved slots at the TRUE r0=20 source
have a polynomial measured Fourier L1 variation after Cauchy, with
fixed exponent C_f independent of requested TypeII precision K0.
This is Parity(4.6) mass without either selected or skipped phase. -/
theorem parity_eventually_original_actual_post_cauchy_Q_gate_L1_polylog434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ),
        let n := (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length
        let s := sourceActualSortedFrequencyScales 20
          (sourceOriginalLiteralDepth 20 L) L band slot
        (∑δ : Fin n → Bool,
          ∫ ξ : Fin n → ℝ,
            ‖parityOriginalActualPostCauchyQGate434 E s ξ δ‖) ≤
          L^parityOriginalB590FixedFourierPolynomialExponent434 := by
  filter_upwards [parity_eventually_original_B590_actual_full_fourier_variation_polylog434]
    with L hMass
  intro band slot E
  dsimp only
  calc
    _ = ∑δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → Bool,
        parityOriginalB590FourierBranchVariation434 δ := by
          apply Finset.sum_congr rfl
          intro δ hδ
          exact parity_original_actual_post_cauchy_Q_gate_L1_branch_exact434
            E (sourceActualSortedFrequencyScales 20
              (sourceOriginalLiteralDepth 20 L) L band slot) δ
    _ ≤ _ := hMass band slot
end Green64Analytic.Parity

end

end

/-! ## PostCauchyQBoxBound -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The literal Parity(4.10) post-Cauchy Fourier operator with NO Q
prime-label tuple: all δ and all real Q allocation frequencies are
integrated against the true f0/f1 Fourier Schwartz gate. The selected
Q phase belonged to the removed a_e; the skipped phase is already
inside the physical source residual. Only the ACTUAL bounded Fδ(ξ)
is a premise here. This is the phase-correct analogue of the generic
Parity(4.6) L1 operator, without a duplicated prime phase. -/
theorem parity_original_actual_post_cauchy_Q_weighted_integral_bound434
    {n : ℕ} (E : ℝ) (s : Fin n → ℝ)
    (F : (Fin n → Bool) → (Fin n → ℝ) → ℂ)
    (M : ℝ) (hM : 0≤M)
    (hMeas : ∀δ, AEStronglyMeasurable (F δ))
    (hBound : ∀δ ξ, ‖F δ ξ‖≤M) :
    ‖∑δ : Fin n → Bool,
       ∫ ξ : Fin n → ℝ,
         parityOriginalActualPostCauchyQGate434 E s ξ δ * F δ ξ‖ ≤
      M*(∑δ : Fin n → Bool,
        ∫ ξ : Fin n → ℝ,
          ‖parityOriginalActualPostCauchyQGate434 E s ξ δ‖) := by
  classical
  let A : (Fin n → Bool) → (Fin n → ℝ) → ℂ := fun δ ξ =>
    parityOriginalActualPostCauchyQGate434 E s ξ δ
  have hAI : ∀δ,Integrable (A δ) := by
    intro δ
    exact parity_original_actual_post_cauchy_Q_gate_integrable434 E s δ
  have hPt : ∀δ ξ, ‖A δ ξ * F δ ξ‖≤M*‖A δ ξ‖ := by
    intro δ ξ
    rw [norm_mul]
    have hh := mul_le_mul_of_nonneg_left (hBound δ ξ)
      (norm_nonneg (A δ ξ))
    simpa only [mul_comm] using hh
  have hAF : ∀δ,Integrable (fun ξ => A δ ξ * F δ ξ) := by
    intro δ
    have hProdMeas : AEStronglyMeasurable (fun ξ => A δ ξ * F δ ξ) :=
      (hAI δ).aestronglyMeasurable.mul (hMeas δ)
    apply ((hAI δ).norm.const_mul M).mono hProdMeas
    filter_upwards [] with ξ
    have hh := hPt δ ξ
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hM,
      abs_of_nonneg (norm_nonneg _)] using hh
  have hEach (δ : Fin n → Bool) :
      ‖∫ ξ : Fin n → ℝ,A δ ξ*F δ ξ‖ ≤
        M*(∫ ξ : Fin n → ℝ, ‖A δ ξ‖) := by
    calc
      _ ≤ ∫ ξ : Fin n → ℝ, ‖A δ ξ*F δ ξ‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ ξ : Fin n → ℝ, M*‖A δ ξ‖ := by
        apply integral_mono (hAF δ).norm ((hAI δ).norm.const_mul M)
        intro ξ
        exact hPt δ ξ
      _ = M*(∫ ξ : Fin n → ℝ,‖A δ ξ‖) := integral_const_mul _ _
  calc
    _ ≤ ∑δ : Fin n → Bool, ‖∫ ξ : Fin n → ℝ,A δ ξ*F δ ξ‖ := norm_sum_le _ _
    _ ≤ ∑δ : Fin n → Bool, M*(∫ ξ : Fin n → ℝ,‖A δ ξ‖) := by
      apply Finset.sum_le_sum
      intro δ hδ
      exact hEach δ
    _ = M*(∑δ : Fin n → Bool,∫ ξ : Fin n → ℝ,‖A δ ξ‖) := by
      rw [Finset.mul_sum]

/-- Strongly measurable actual physical source Bprime F may be
bounded only on the TRUE N-dimensional source cube [-L,L]^N;
outside it we zero-extend the physical Fourier family, not its
natural e,n,m,m',z support. This is the legit original Parity(4.6)
truncation before the separately proven high-frequency source tail. -/
theorem parity_original_actual_post_cauchy_Q_weighted_box_bound434
    {n : ℕ} (E T : ℝ) (s : Fin n → ℝ)
    (F : (Fin n → Bool) → (Fin n → ℝ) → ℂ)
    (M : ℝ) (hM : 0≤M)
    (hMeas : ∀δ,AEStronglyMeasurable (F δ))
    (hBound : ∀δ ξ, ξ∈parityOriginalActualFullQFrequencyCube434 T → ‖F δ ξ‖≤M) :
    ‖∑δ : Fin n → Bool,
        ∫ ξ in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalActualPostCauchyQGate434 E s ξ δ * F δ ξ‖ ≤
      M*(∑δ : Fin n → Bool,
        ∫ ξ : Fin n → ℝ,‖parityOriginalActualPostCauchyQGate434 E s ξ δ‖) := by
  classical
  let S := parityOriginalActualFullQFrequencyCube434 (N:=n) T
  have hS : MeasurableSet S := parity_original_actual_fullQ_frequency_cube_measurable434 T
  let G : (Fin n → Bool) → (Fin n → ℝ) → ℂ := fun δ => S.indicator (F δ)
  have hGM : ∀δ,AEStronglyMeasurable (G δ) := by
    intro δ
    exact (hMeas δ).indicator hS
  have hGB : ∀δ ξ, ‖G δ ξ‖≤M := by
    intro δ ξ
    by_cases hξ : ξ∈S
    · simp only [G,Set.indicator_of_mem hξ]
      exact hBound δ ξ hξ
    · simp [G,Set.indicator,hξ,hM]
  have hAll := parity_original_actual_post_cauchy_Q_weighted_integral_bound434
    E s G M hM hGM hGB
  have hExact :
      (∑δ : Fin n → Bool,
         ∫ ξ in S, parityOriginalActualPostCauchyQGate434 E s ξ δ*F δ ξ) =
      (∑δ : Fin n → Bool,
         ∫ ξ : Fin n → ℝ, parityOriginalActualPostCauchyQGate434 E s ξ δ*G δ ξ) := by
    apply Finset.sum_congr rfl
    intro δ hδ
    rw [←integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [] with ξ
    exact Set.indicator_mul_right S
      (fun ξ => parityOriginalActualPostCauchyQGate434 E s ξ δ) (F δ)
  change ‖∑δ : Fin n → Bool,∫ξ in S,
      parityOriginalActualPostCauchyQGate434 E s ξ δ*F δ ξ‖ ≤ _
  rw [hExact]
  exact hAll

/-- The original full-Q Fourier variation fixed C_f pays all
allocation branches of the post-Cauchy source family. If F is
measurable and satisfies the ACTUAL spectral saving at arbitrary
precision target before L, then the whole box has saving goal.
No character, prime-tuple or selected-e phase factor is inserted. -/
theorem parity_eventually_original_actual_post_cauchy_Q_weighted_box_anylog434
    (goal target C : ℝ) (hC : 0≤C)
    (hPrecision : goal+parityOriginalB590FixedFourierPolynomialExponent434≤target) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ),
        let n := (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length
        let s := sourceActualSortedFrequencyScales 20
          (sourceOriginalLiteralDepth 20 L) L band slot
        ∀ (F : (Fin n → Bool) → (Fin n → ℝ) → ℂ),
          (∀δ,AEStronglyMeasurable (F δ)) →
          (∀δ ξ, ξ∈parityOriginalActualFullQFrequencyCube434 L →
            ‖F δ ξ‖≤C*Real.exp L*L^(-target)) →
          ‖∑δ : Fin n → Bool,
            ∫ ξ in parityOriginalActualFullQFrequencyCube434 L,
              parityOriginalActualPostCauchyQGate434 E s ξ δ*F δ ξ‖ ≤
            C*Real.exp L*L^(-goal) := by
  filter_upwards [parity_eventually_original_actual_post_cauchy_Q_gate_L1_polylog434,
    eventually_ge_atTop (1:ℝ)] with L hMass hL
  intro band slot E
  dsimp only
  intro F hMeas hBound
  let M : ℝ := C*Real.exp L*L^(-target)
  have hM : 0≤M := by dsimp [M]; positivity
  have hFirst := parity_original_actual_post_cauchy_Q_weighted_box_bound434
    E L (sourceActualSortedFrequencyScales 20
      (sourceOriginalLiteralDepth 20 L) L band slot)
    F M hM hMeas hBound
  have hVariation := hMass band slot E
  have hTotal := hFirst.trans (mul_le_mul_of_nonneg_left hVariation hM)
  have hLp : 0<L := by linarith
  have hPower : L^(-target)*L^parityOriginalB590FixedFourierPolynomialExponent434 =
      L^(parityOriginalB590FixedFourierPolynomialExponent434-target) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  have hExp : parityOriginalB590FixedFourierPolynomialExponent434-target≤-goal := by
    linarith
  have hRpow : L^(parityOriginalB590FixedFourierPolynomialExponent434-target)≤L^(-goal) :=
    Real.rpow_le_rpow_of_exponent_le hL hExp
  calc
    _ ≤ M*L^parityOriginalB590FixedFourierPolynomialExponent434 := hTotal
    _ = (C*Real.exp L)*L^(parityOriginalB590FixedFourierPolynomialExponent434-target) := by
      dsimp [M]
      calc
        _ = (C*Real.exp L)*(L^(-target)*
            L^parityOriginalB590FixedFourierPolynomialExponent434) := by ring
        _ = _ := by rw [hPower]
    _ ≤ (C*Real.exp L)*L^(-goal) :=
      mul_le_mul_of_nonneg_left hRpow (by positivity)
    _ = C*Real.exp L*L^(-goal) := by ring
end Green64Analytic.Parity

end

end

/-! ## PostCauchyPositiveL1Bound -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- The POSITIVE absolute-integral Parity(4.10) Fourier variation:
not merely a norm of the complex delta/xi integral. This bound is
what may legally be used after source Cauchy and outside triangle.
The true all-Q Fourier cube and original phase-FREE external Schwartz
gate are retained. Physical F can have arbitrary complex signs and
is bounded only WITHIN the real frequency cube. No reverse norm
inequality or fake monotonicity of complex subsums is used. -/
theorem parity_original_actual_post_cauchy_Q_positive_L1_box_bound434
    {n : ℕ} (E T : ℝ) (s : Fin n → ℝ)
    (F : (Fin n → Bool) → (Fin n → ℝ) → ℂ)
    (M : ℝ) (hM : 0≤M)
    (hMeas : ∀δ,AEStronglyMeasurable (F δ))
    (hBound : ∀δ ξ, ξ∈parityOriginalActualFullQFrequencyCube434 T → ‖F δ ξ‖≤M) :
    (∑δ : Fin n → Bool,
      ∫ ξ in parityOriginalActualFullQFrequencyCube434 T,
        ‖parityOriginalActualPostCauchyQGate434 E s ξ δ‖ * ‖F δ ξ‖) ≤
      M*(∑δ : Fin n → Bool,
        ∫ ξ : Fin n → ℝ, ‖parityOriginalActualPostCauchyQGate434 E s ξ δ‖) := by
  classical
  let S := parityOriginalActualFullQFrequencyCube434 (N:=n) T
  have hS : MeasurableSet S := parity_original_actual_fullQ_frequency_cube_measurable434 T
  let G : (Fin n → Bool) → (Fin n → ℝ) → ℂ := fun δ => S.indicator (F δ)
  have hGM : ∀δ,AEStronglyMeasurable (G δ) := by
    intro δ
    exact (hMeas δ).indicator hS
  have hGB : ∀δ ξ, ‖G δ ξ‖≤M := by
    intro δ ξ
    by_cases hξ : ξ∈S
    · simp only [G,Set.indicator_of_mem hξ]
      exact hBound δ ξ hξ
    · simp [G,hξ,hM]
  let A : (Fin n → Bool) → (Fin n → ℝ) → ℂ := fun δ ξ =>
    parityOriginalActualPostCauchyQGate434 E s ξ δ
  have hAI : ∀δ,Integrable (A δ) := by
    intro δ
    exact parity_original_actual_post_cauchy_Q_gate_integrable434 E s δ
  have hPt : ∀δ ξ, ‖A δ ξ*G δ ξ‖ ≤ M*‖A δ ξ‖ := by
    intro δ ξ
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_left (hGB δ ξ) (norm_nonneg (A δ ξ))
    simpa only [mul_comm] using h
  have hProdInt : ∀δ,Integrable (fun ξ => A δ ξ*G δ ξ) := by
    intro δ
    have hm : AEStronglyMeasurable (fun ξ => A δ ξ*G δ ξ) :=
      (hAI δ).aestronglyMeasurable.mul (hGM δ)
    apply ((hAI δ).norm.const_mul M).mono hm
    filter_upwards [] with ξ
    have h := hPt δ ξ
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hM,
      abs_of_nonneg (norm_nonneg _)] using h
  have hBranch (δ : Fin n → Bool) :
      (∫ ξ in S, ‖A δ ξ‖*‖F δ ξ‖) ≤
        M*(∫ ξ : Fin n → ℝ,‖A δ ξ‖) := by
    have hIdentity :
        (∫ ξ in S, ‖A δ ξ‖*‖F δ ξ‖) =
        (∫ ξ : Fin n → ℝ, ‖A δ ξ*G δ ξ‖) := by
      rw [←integral_indicator hS]
      apply integral_congr_ae
      filter_upwards [] with ξ
      by_cases hξ : ξ∈S
      · simp [G,Set.indicator_of_mem hξ,norm_mul]
      · simp [G,Set.indicator,hξ,norm_mul]
    rw [hIdentity]
    calc
      _ ≤ ∫ ξ : Fin n → ℝ, M*‖A δ ξ‖ := by
        apply integral_mono (hProdInt δ).norm ((hAI δ).norm.const_mul M)
        intro ξ
        exact hPt δ ξ
      _ = M*(∫ ξ : Fin n → ℝ,‖A δ ξ‖) := integral_const_mul _ _
  calc
    _ ≤ ∑δ : Fin n → Bool, M*(∫ ξ : Fin n → ℝ,‖A δ ξ‖) := by
      apply Finset.sum_le_sum
      intro δ hδ
      exact hBranch δ
    _ = M*(∑δ : Fin n → Bool,∫ ξ : Fin n → ℝ,‖A δ ξ‖) := by
      rw [Finset.mul_sum]

/-- The genuinely POSITIVE post-Cauchy Fourier mass costs at most the
original Q gate L1 exponent C_f and accepts arbitrary deep saving
chosen before L. Unlike the complex integral estimate, this can
safely enter the original Parity(4.10) Cauchy upper bound and norm
triangle, once all actual full-fine source identities are proved. -/
theorem parity_eventually_original_actual_post_cauchy_Q_positive_L1_box_anylog434
    (goal target C : ℝ) (hC : 0≤C)
    (hPrecision : goal+parityOriginalB590FixedFourierPolynomialExponent434≤target) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ),
        let n := (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length
        let s := sourceActualSortedFrequencyScales 20
          (sourceOriginalLiteralDepth 20 L) L band slot
        ∀ (F : (Fin n → Bool) → (Fin n → ℝ) → ℂ),
          (∀δ,AEStronglyMeasurable (F δ)) →
          (∀δ ξ, ξ∈parityOriginalActualFullQFrequencyCube434 L →
            ‖F δ ξ‖≤C*Real.exp L*L^(-target)) →
          (∑δ : Fin n → Bool,
            ∫ ξ in parityOriginalActualFullQFrequencyCube434 L,
              ‖parityOriginalActualPostCauchyQGate434 E s ξ δ‖*‖F δ ξ‖) ≤
            C*Real.exp L*L^(-goal) := by
  filter_upwards [parity_eventually_original_actual_post_cauchy_Q_gate_L1_polylog434,
    eventually_ge_atTop (1:ℝ)] with L hMass hL
  intro band slot E
  dsimp only
  intro F hMeas hBound
  let M : ℝ := C*Real.exp L*L^(-target)
  have hM : 0≤M := by dsimp [M]; positivity
  have hFirst := parity_original_actual_post_cauchy_Q_positive_L1_box_bound434
    E L (sourceActualSortedFrequencyScales 20
      (sourceOriginalLiteralDepth 20 L) L band slot)
    F M hM hMeas hBound
  have hVar := hMass band slot E
  have hUpper := hFirst.trans (mul_le_mul_of_nonneg_left hVar hM)
  have hLp : 0<L := by linarith
  have hRpow : L^(-target)*L^parityOriginalB590FixedFourierPolynomialExponent434 =
      L^(parityOriginalB590FixedFourierPolynomialExponent434-target) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  have hExp : parityOriginalB590FixedFourierPolynomialExponent434-target≤-goal := by
    linarith
  have hPowLe :
      L^(parityOriginalB590FixedFourierPolynomialExponent434-target)≤L^(-goal) :=
    Real.rpow_le_rpow_of_exponent_le hL hExp
  calc
    _ ≤ M*L^parityOriginalB590FixedFourierPolynomialExponent434 := hUpper
    _ = (C*Real.exp L)*L^(parityOriginalB590FixedFourierPolynomialExponent434-target) := by
      dsimp [M]
      calc
        _ = (C*Real.exp L)*(L^(-target)*
            L^parityOriginalB590FixedFourierPolynomialExponent434) := by ring
        _ = _ := by rw [hRpow]
    _ ≤ (C*Real.exp L)*L^(-goal) :=
      mul_le_mul_of_nonneg_left hPowLe (by positivity)
    _ = C*Real.exp L*L^(-goal) := by ring
end Green64Analytic.Parity

end

end

/-! ## BprimeFullQGateDominatedIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- POSITIVE Fourier variation of an actual post-Cauchy family B
whose norm is pointwise paid by the one and only source post-Cauchy
Schwartz Q-gate. There is NO repeated selected-Q prime phase,
and no complex integral cancellation is invoked. This is the exact
integral inequality needed to integrate the physical Bprime root. -/
theorem parity_original_actual_Bprime_fullQ_gate_dominated_positive_integral434
    {n : ℕ} (E L M : ℝ) (s : Fin n → ℝ) (hM : 0≤M)
    (B : (Fin n → Bool) → (Fin n → ℝ) → ℂ)
    (hMeas : ∀δ,AEStronglyMeasurable (B δ))
    (hBound : ∀δ ξ, ξ∈parityOriginalActualFullQFrequencyCube434 L →
      ‖B δ ξ‖ ≤ M * ‖parityOriginalActualPostCauchyQGate434 E s ξ δ‖) :
    (∑δ : Fin n → Bool,
      ∫ ξ in parityOriginalActualFullQFrequencyCube434 L, ‖B δ ξ‖) ≤
    M*(∑δ : Fin n → Bool,
      ∫ ξ : Fin n → ℝ, ‖parityOriginalActualPostCauchyQGate434 E s ξ δ‖) := by
  classical
  let S : Set (Fin n → ℝ) := parityOriginalActualFullQFrequencyCube434 L
  have hS : MeasurableSet S := parity_original_actual_fullQ_frequency_cube_measurable434 L
  let A : (Fin n → Bool) → (Fin n → ℝ) → ℂ := fun δ ξ =>
    parityOriginalActualPostCauchyQGate434 E s ξ δ
  have hAI : ∀δ,Integrable (fun ξ : Fin n → ℝ => ‖A δ ξ‖) := by
    intro δ
    exact (parity_original_actual_post_cauchy_Q_gate_integrable434 E s δ).norm
  let G : (Fin n → Bool) → (Fin n → ℝ) → ℂ := fun δ => S.indicator (B δ)
  have hGM : ∀δ,AEStronglyMeasurable (G δ) := by
    intro δ
    exact (hMeas δ).indicator hS
  have hGB : ∀δ ξ,‖G δ ξ‖≤M*‖A δ ξ‖ := by
    intro δ ξ
    by_cases hξ : ξ∈S
    · simp only [G,Set.indicator_of_mem hξ]
      exact hBound δ ξ hξ
    · simp only [G,Set.indicator_of_notMem hξ,norm_zero]
      positivity
  have hGI : ∀δ,Integrable (G δ) := by
    intro δ
    have hMajor : Integrable (fun ξ : Fin n → ℝ => M*‖A δ ξ‖) :=
      (hAI δ).const_mul M
    apply hMajor.mono (hGM δ)
    filter_upwards [] with ξ
    have h := hGB δ ξ
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hM (norm_nonneg _))]
      using h
  have hBranch (δ : Fin n → Bool) :
      (∫ ξ in S, ‖B δ ξ‖) ≤
        M*(∫ ξ : Fin n → ℝ, ‖A δ ξ‖) := by
    have hInd : (fun ξ : Fin n → ℝ => S.indicator (fun ξ => ‖B δ ξ‖) ξ) =
        (fun ξ => ‖G δ ξ‖) := by
      funext ξ
      by_cases hξ : ξ∈S
      · simp [G,Set.indicator_of_mem hξ]
      · simp [G,Set.indicator_of_notMem hξ]
    rw [←integral_indicator hS,hInd]
    calc
      _ ≤ ∫ ξ : Fin n → ℝ, M*‖A δ ξ‖ := by
        apply integral_mono (hGI δ).norm ((hAI δ).const_mul M)
        intro ξ
        exact hGB δ ξ
      _ = M*(∫ ξ : Fin n → ℝ, ‖A δ ξ‖) := integral_const_mul _ _
  calc
    _ ≤ ∑δ : Fin n → Bool,M*(∫ ξ : Fin n → ℝ, ‖A δ ξ‖) := by
      apply Finset.sum_le_sum
      intro δ hδ
      exact hBranch δ
    _ = M*(∑δ : Fin n → Bool, ∫ ξ : Fin n → ℝ,‖A δ ξ‖) := by
      rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## TruePsiQFourierCompactBasic -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem parity_original_true_full_Q_frequency_cube_compact434
    {n : ℕ} (T : ℝ) :
    IsCompact (parityOriginalActualFullQFrequencyCube434 (N:=n) T) := by
  have hSet : parityOriginalActualFullQFrequencyCube434 (N:=n) T =
      Set.univ.pi (fun _ : Fin n => Set.Icc (-T) T) := by
    ext xi
    simp [parityOriginalActualFullQFrequencyCube434,Set.mem_pi,Pi.le_def,forall_and]
  rw [hSet]
  exact isCompact_univ_pi fun _ => isCompact_Icc

/-- Exact compact Q×Mellin Fubini with the literal source product
Lebesgue measures, for EVERY continuous original physical
Fourier/Mellin integrand. The two frequency cutoffs are both
original real intervals; nothing is set to zero pointwise outside
its actual source. Unlike an arbitrary swap, this is justified
by compact product integrability and the actual original Q cube. -/
theorem parity_original_true_compact_Psi_Mellin_Q_Fubini434
    {n : ℕ} (R T : ℝ)
    (F : ℝ → (Fin n → ℝ) → ℂ)
    (hF : Continuous (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2)) :
    (∫xi in parityOriginalActualFullQFrequencyCube434 (N:=n) T,
      ∫s in Set.Icc (-R) R, F s xi) =
    (∫s in Set.Icc (-R) R,
      ∫xi in parityOriginalActualFullQFrequencyCube434 (N:=n) T,
        F s xi) := by
  let A : Set ℝ := Set.Icc (-R) R
  let B : Set (Fin n → ℝ) := parityOriginalActualFullQFrequencyCube434 T
  have hCompact : IsCompact (A ×ˢ B) :=
    isCompact_Icc.prod (parity_original_true_full_Q_frequency_cube_compact434 T)
  have hInt : Integrable (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2)
      ((volume : Measure ℝ).restrict A |>.prod ((volume : Measure (Fin n → ℝ)).restrict B)) := by
    rw [Measure.prod_restrict]
    exact hF.continuousOn.integrableOn_compact hCompact
  have hSwap := MeasureTheory.integral_integral_swap hInt
  exact hSwap.symm
end Green64Analytic.Parity

end

end

/-! ## HighMellinQFubiniDominated -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 950000

/-- Fubini on the ACTUAL unbounded real high-Mellin region
{|s|>=R} × the ORIGINAL compact N-dimensional real Q Fourier cube.
Unlike compact Fubini the first factor is UNBOUNDED: the source
integrand must have a separable integrable majorant |K(s)|M(xi).
No claim of integrability follows from continuity alone. -/
theorem parity_original_true_high_Mellin_Q_Fubini_dominated434
    {n : ℕ} (R T : ℝ)
    (K : ℝ → ℂ) (M : (Fin n → ℝ) → ℝ)
    (F : ℝ → (Fin n → ℝ) → ℂ)
    (hK : Integrable K)
    (hM : IntegrableOn M (parityOriginalActualFullQFrequencyCube434 T))
    (hMnonneg : ∀xi,0≤M xi)
    (hF : Continuous (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2))
    (hBound : ∀s xi,‖F s xi‖ ≤ ‖K s‖*M xi) :
    (∫xi in parityOriginalActualFullQFrequencyCube434 T,
       ∫s in {s : ℝ | R≤‖s‖},F s xi) =
    (∫s in {s : ℝ | R≤‖s‖},
       ∫xi in parityOriginalActualFullQFrequencyCube434 T,F s xi) := by
  let U : Set ℝ := {s : ℝ | R≤‖s‖}
  let V : Set (Fin n → ℝ) := parityOriginalActualFullQFrequencyCube434 T
  let μ : Measure ℝ := volume.restrict U
  let ν : Measure (Fin n → ℝ) := volume.restrict V
  have hSep : Integrable (fun p : ℝ × (Fin n → ℝ) => ‖K p.1‖ * M p.2)
      (μ.prod ν) := (hK.norm.integrableOn).mul_prod hM
  have hIntegrable : Integrable (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2)
      (μ.prod ν) := by
    apply hSep.mono hF.aestronglyMeasurable
    filter_upwards [] with p
    have hh := hBound p.1 p.2
    simpa only [Real.norm_eq_abs,abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (hMnonneg _))] using hh
  have hSwap := MeasureTheory.integral_integral_swap hIntegrable
  exact hSwap.symm
end Green64Analytic.Parity

end

end

/-! ## QIntegralContinuousMajorant -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- Genuine original multidimensional real Lebesgue Q cube:
if a complex source integrand and its REAL majorant are continuous,
then the Q-integrated complex NORM is bounded by the integral of
that positive majorant, even at the actual source N=0 branch.
This is a genuine compact integrability statement, not an invalid
complex signed-subsum inequality and no extra assumption about
Lebesgue integrability is inserted. -/
theorem parity_original_continuous_Q_cube_complex_integral_majorant434
    {n : ℕ} (T : ℝ)
    (F : (Fin n → ℝ) → ℂ) (G : (Fin n → ℝ) → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hPoint : ∀xi,‖F xi‖≤G xi) :
    ‖∫xi in parityOriginalActualFullQFrequencyCube434 (N:=n) T,F xi‖ ≤
      ∫xi in parityOriginalActualFullQFrequencyCube434 (N:=n) T,G xi := by
  let Q : Set (Fin n → ℝ) := parityOriginalActualFullQFrequencyCube434 T
  have hCompact : IsCompact Q := parity_original_true_full_Q_frequency_cube_compact434 T
  have hFI : IntegrableOn (fun xi => ‖F xi‖) Q :=
    hF.norm.continuousOn.integrableOn_compact hCompact
  have hGI : IntegrableOn G Q :=
    hG.continuousOn.integrableOn_compact hCompact
  calc
    _ ≤ ∫xi in Q,‖F xi‖ := norm_integral_le_integral_norm _
    _ ≤ ∫xi in Q,G xi := integral_mono hFI hGI hPoint
end Green64Analytic.Parity

end

end

/-! ## ParamOriginalASmoothRange -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 34000

/-- For EACH exact FULL Q tuple witnessing the original
`sourceOriginalOrdinaryCoefficient`, its true nonreserved Q product
satisfies E<=Q under the original Type II arbitrary-b_* physical gates.
The native ordinary times P-prime-part physical factorisation is proved
from the source witness and NOT assumed. -/
theorem parity_actual_original_full_Q_tuple_beta_E_source_mass434
    (beta : ℝ) (hbeta : 0 < beta)
    (d : ℕ) (L : ℝ) (hL : 0 ≤ L) (E : ℝ)
    (hE : E ≤ Real.exp ((1-beta)*L))
    (u : ℕ) (hu : u ≠ 0) (hLarge : Real.exp L ≤ (u:ℝ))
    (hPcap : sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
      sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (hf : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4)
    (slot : Fin 20) :
    E ≤ ((∏ i, (parityActualSourceRemainingFullQTuple434 d L band slot f i).val : ℕ) : ℝ) := by
  have hSplit := parity_actual_source_fullQ_split_reserved_sorted_exact434
    d L band slot f
  have hFactor : (f band slot).val *
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
  have hPhysical : Real.exp L ≤
      (((f band slot).val *
          (∏ i, (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) *
          sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u : ℕ) : ℝ) := by
    calc
      _ ≤ (u:ℝ) := hLarge
      _ = _ := by rw [hFactor]
  exact parity_original_beta_physical_E_le_full_Qmass434
    beta hbeta d L hL E hE band hBand slot (f band slot)
    (parityActualSourceRemainingFullQTuple434 d L band slot f)
    (sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    hPcap hPhysical

/-- The genuine nonzero ORIGINAL `sourceOriginalA` of Parity, with actual
r20 moving Q depth, a fixed reserved band j** chosen small enough for
ANY b_*>0, full physical u>=exp L and original P cap exp(b_*L/4),
proves complete Parity(4.5) e-range on every positively weighted B590
allocation branch of the witness. NO independent full Q mass hypothesis
and NO restriction b_*>=1/20. The reserved band is automatically in
the actual moving source depth eventually.
Historical a_e Fourier equality and full E4.1/TypeII still OPEN. -/
theorem parity_eventually_original_A_beta_smooth_e_range434
    (beta : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBandSmall : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      jQ ≤ sourceOriginalLiteralDepth 20 L ∧ 2 ≤ L ∧
      ∀ E : ℝ, 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ u : ℕ,
      sourceOriginalA 20
        (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
        (sourceOriginalPAllActualBands 20 L) u ≠ 0 →
      Real.exp L ≤ (u:ℝ) →
      sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
        sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊ →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
      ∀ (slot : Fin 20),
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
  filter_upwards [parity_eventually_actual_smooth_e_full_range_of_Q_mass434,
    parity_eventually_original_reserved_Q_band_in_moving_depth434 jQ]
    with L hRange hDepth
  refine ⟨hDepth,hRange.1,?_⟩
  intro E hE hEcap u hA hLarge hPcap band hband slot
  have hu : u ≠ 0 := by
    intro hZero
    apply hA
    simpa only [hZero] using (b640_original_A_zero434 20
      (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
      (sourceOriginalPAllActualBands 20 L))
  obtain ⟨f,hf⟩ := parity_original_A_nonzero_full_Q_slots_witness434
    20 (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
    (sourceOriginalPAllActualBands 20 L) u hA
  have hBandSmallL : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4 := by
    rw [hband]
    exact hBandSmall
  have hQmass := parity_actual_original_full_Q_tuple_beta_E_source_mass434
    beta hbeta (sourceOriginalLiteralDepth 20 L) L (by linarith [hRange.1])
    E hEcap u hu hLarge hPcap f hf band hBandSmallL slot
  let p := parityActualSourceRemainingFullQTuple434
    (sourceOriginalLiteralDepth 20 L) L band slot f
  refine ⟨f,hf,?_⟩
  intro δ
  dsimp only
  intro hWeight
  exact hRange.2 E hE band slot δ p hQmass hWeight
end Green64Analytic.Parity

end

end

/-! ## OriginalBetaRetainedAllocationMassOne -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- ORIGINAL Parity §4.1–§4.2 retained physical source: arbitrary beta>0,
reserved Q index satisfying its beta/4 band gate, all original P-prime
powers capped at exp(beta L/4), actual u>=exp L and the complete
all-Q factorial product gate. Under these SOURCE hypotheses the
FULL B590 sum over every original assignment is EXACTLY ONE.
No extra full-Q mass or B590 partition-of-unity assumption is introduced:
actual physical total-Q capacity follows from the existing genuine
source theorem `parity_actual_original_full_Q_tuple_beta_E_source_mass434`. -/
theorem parity_original_beta_retained_full_Q_tuple_B590_mass_one434
    (beta : ℝ) (hbeta : 0 < beta)
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hElo : 1 ≤ E) (hEhi : E ≤ Real.exp ((1-beta)*L))
    (u : ℕ) (hu : u ≠ 0) (hLarge : Real.exp L ≤ (u:ℝ))
    (hPcap : sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
      sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (hf : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4)
    (slot : Fin 20) :
    parityActualOriginalAFullTupleAllocationMass434 d L E band slot f = 1 := by
  have hMass := parity_actual_original_full_Q_tuple_beta_E_source_mass434
    beta hbeta d L (le_of_lt hL) E hEhi u hu hLarge
    hPcap f hf band hBand slot
  exact parity_original_actual_fullQ_B590_all_assignments_mass_one434
    d L E hL hElo band slot f hMass

/-- SOURCE retained factorial/orbit term exactly cancels its B590
allocation defect, not only after taking limits or averaging over Q
labellings. Both original W1 and parity projector are preserved. -/
theorem parity_original_beta_retained_full_Q_tuple_defect_zero434
    (beta : ℝ) (hbeta : 0 < beta)
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hElo : 1 ≤ E) (hEhi : E ≤ Real.exp ((1-beta)*L))
    (u : ℕ) (hu : u ≠ 0) (hLarge : Real.exp L ≤ (u:ℝ))
    (hPcap : sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
      sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4)
    (slot : Fin 20) :
    parityActualOriginalAFullTupleWeight434 d L u f *
      (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f) = 0 := by
  by_cases hf : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · rw [parity_original_beta_retained_full_Q_tuple_B590_mass_one434
      beta hbeta d L E hL hElo hEhi u hu hLarge hPcap f hf band hBand slot]
    ring
  · unfold parityActualOriginalAFullTupleWeight434
    simp only [if_neg hf, zero_mul]
end Green64Analytic.Parity

end

end

/-! ## OriginalBetaRetainedXADefect -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The complete actual original XA factorial-labelled allocation
defect vanishes at EVERY source integer u on the physically retained
Parity §4.1 beta-dependent P part and original x>=exp L carrier.
The original Q product gate is handled term by term; nothing assumes
that all factorial-labelled assignments contribute. -/
theorem parity_original_beta_retained_XA_at_u_defect_zero434
    (beta : ℝ) (hbeta : 0 < beta)
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hElo : 1 ≤ E) (hEhi : E ≤ Real.exp ((1-beta)*L))
    (u : ℕ) (hLarge : Real.exp L ≤ (u:ℝ))
    (hPcap : parityOriginalPhysicalPcapBeta434 beta L u)
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4)
    (slot : Fin 20) :
    (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
      parityActualOriginalAFullTupleWeight434 d L u f *
        (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)) = 0 := by
  have hu : u ≠ 0 := by
    intro hz
    subst u
    have hp := Real.exp_pos L
    norm_num at hLarge
    linarith
  have hMem : sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
        sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊ :=
    (parity_actual_original_beta_Pcap_mem434 beta L u).2 hPcap
  apply Finset.sum_eq_zero
  intro f hf
  exact parity_original_beta_retained_full_Q_tuple_defect_zero434
    beta hbeta d L E hL hElo hEhi u hu hLarge hMem
    f band hBand slot
end Green64Analytic.Parity

end

end

/-! ## OriginalXAOnlyPcapDefect -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 34000

/-- The HISTORICAL original source XA buffered allocation defect at
x=exp L is supported ONLY on the actual Parity §4.1 beta/4 discarded
P-prime-power part. The original Ψ support [1,2] guarantees u>=exp L;
retained original Q factorial labels have complete B590 mass 1
proven by the true causal f0/f1 source normalizer.
This is an EXACT equality of the original source error, not an
unproved asymptotic saving or a proxy P-part. It is the precise
input for the pinned original Parity (4.3) discarded-P mass estimate. -/
theorem parity_original_XA_B590_allocation_defect_only_beta_Pcap_fail434
    (beta : ℝ) (hbeta : 0 < beta)
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hElo : 1 ≤ E) (hEhi : E ≤ Real.exp ((1-beta)*L))
    (Psi : ℝ → ℝ)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4)
    (slot : Fin 20) :
    parityActualOriginalXAAllocationDefect434 d L E (Real.exp L) Psi band slot =
    ∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
      if parityOriginalPhysicalPcapBeta434 beta L u then 0 else
        (∑ f : ((j : Fin (d+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
          parityActualOriginalAFullTupleWeight434 d L u f *
            (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)) *
          Psi ((u:ℝ)/(Real.exp L)) := by
  unfold parityActualOriginalXAAllocationDefect434
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hCap : parityOriginalPhysicalPcapBeta434 beta L u
  · simp only [if_pos hCap]
    by_cases hPsi0 : Psi ((u:ℝ)/(Real.exp L)) = 0
    · rw [hPsi0]
      ring
    · have hPsiMem : ((u:ℝ)/(Real.exp L)) ∈ Set.Icc (1:ℝ) 2 :=
        hSupport (by simpa [Function.mem_support] using hPsi0)
      have hLarge : Real.exp L ≤ (u:ℝ) := by
        have hp : 0 < Real.exp L := Real.exp_pos L
        have hm := (le_div_iff₀ hp).mp hPsiMem.1
        simpa only [one_mul] using hm
      have hZero := parity_original_beta_retained_XA_at_u_defect_zero434
        beta hbeta d L E hL hElo hEhi u hLarge hCap band hBand slot
      rw [hZero]
      ring
  · simp only [if_neg hCap]
end Green64Analytic.Parity

end

end

/-! ## OriginalXAActualBufferDomination -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Pointwise original Parity A is dominated by the ORIGINAL W1(P,u),
using the actual normalized factorial/orbit Q coefficient ≤1 and the
native multiplicity-counted parity projector 0/1. No support or
truncation assumption. -/
theorem parity_original_actual_A_le_true_W1434
    (d : ℕ) (L : ℝ) (u : ℕ) :
    sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u ≤
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
  have hParity := (source_original_parity_pointwise 20
    (sourceOriginalQActualBands 20 d L)
    (sourceOriginalPAllActualBands 20 L) u).2
  have hOrd := source_original_ordinary_le_one 20
    (sourceOriginalQActualBands 20 d L)
    (sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
  have hW := source_original_W1_nonneg (sourceOriginalPAllActualBands 20 L) u
  calc
    sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
        (sourceOriginalPAllActualBands 20 L) u ≤
      sourceOriginalA0 20 (sourceOriginalQActualBands 20 d L)
        (sourceOriginalPAllActualBands 20 L) u := hParity
    _ = sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        sourceOriginalOrdinaryCoefficient 20
          (sourceOriginalQActualBands 20 d L)
          (sourceOriginalOrdinaryPart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) := rfl
    _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u :=
      mul_le_of_le_one_right hW hOrd

/-- The FULL literal original Q factorial-labelled allocation defect,
not just a heuristic parity or product bound, is a nonnegative mass
NO LARGER than the genuine original W1(P,u). This uses the true
history-dependent all-δ subprobability and original Q orbit identity. -/
theorem parity_original_actual_A_buffer_defect_le_W1434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (u : ℕ) (band : Fin (d+1)) (slot : Fin 20) :
    0 ≤ (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
      parityActualOriginalAFullTupleWeight434 d L u f *
        (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)) ∧
    (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
      parityActualOriginalAFullTupleWeight434 d L u f *
        (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)) ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
  have hSource := parity_actual_original_A_all_Q_labelled_exact434 d L hL u
  have hCoef :
      (∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        parityActualOriginalAFullTupleWeight434 d L u f) =
      sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
        (sourceOriginalPAllActualBands 20 L) u := by
    simpa only [parityActualOriginalAFullTupleWeight434] using hSource.symm
  constructor
  · apply Finset.sum_nonneg
    intro f hf
    exact mul_nonneg (parity_actual_original_A_full_tuple_weight_nonneg434 d L u f)
      (parity_actual_original_A_full_tuple_buffer_defect_nonneg434 d L E band slot f)
  · calc
      (∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        parityActualOriginalAFullTupleWeight434 d L u f *
          (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)) ≤
        ∑ f : ((j : Fin (d+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
          parityActualOriginalAFullTupleWeight434 d L u f := by
            apply Finset.sum_le_sum
            intro f hf
            have hw := parity_actual_original_A_full_tuple_weight_nonneg434 d L u f
            have hm := (parity_actual_original_A_full_tuple_allocation_mass_le_one434
              d L E band slot f).1
            nlinarith [mul_nonneg hw hm]
      _ = sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
          (sourceOriginalPAllActualBands 20 L) u := hCoef
      _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u :=
        parity_original_actual_A_le_true_W1434 d L u
end Green64Analytic.Parity

end

end

/-! ## OriginalB590BoxArithmetic -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- True ORIGINAL source r0=20 factorial-labelled Q/P-arithmetic
B590 physical sum at χ=0, after integrating the original gates over
the finite Fourier box [-T,T]^N. Every full Q tuple is weighted by its
original nonnegative W1/P-parity/factorial coefficient, with the
reserved source Q prime and all 2^N δ assignments still present. -/
def parityOriginalB590BoxPhysicalAAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) : ℂ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    ((parityActualOriginalAFullTupleWeight434 d L u f : ℝ):ℂ) *
      (∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        parityOriginalB590AllGateFourierBox434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot f i).val) T)

/-- Original physical SOURCE A at B509 χ=0 before Fourier truncation,
written with its original all-Q factorial summands and full B590
allocation mass, not substituted with unsmoothed A or a proxy gate. -/
def parityOriginalB590FullPhysicalAAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) : ℂ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    ((parityActualOriginalAFullTupleWeight434 d L u f : ℝ):ℂ) *
      ((parityActualOriginalAFullTupleAllocationMass434 d L E band slot f : ℝ):ℂ)

/-- Exact original B590/B509 full-branch A sum equals the genuine
W1/P-parity full-Q coefficient times full all-δ B590 source mass.
This is the previously kernel-checked zero-frequency source identity,
not an unsupported sourceOriginalA normalisation. -/
theorem parity_original_B590_full_physical_A_is_source_zero_freq434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) :
    parityOriginalB590FullPhysicalAAtU434 d L E u band slot =
      ∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
        parityActualOriginalAFullBranchWeight434 d L E u band slot (fun _ => 0) z := by
  unfold parityOriginalB590FullPhysicalAAtU434
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  rw [parity_actual_original_A_zero_freq_assignment_sum434]
  push_cast
  rfl

/-- Exactly one source-u full original B590 Fourier cutoff error,
including the whole 20! factorial Q-prime family and all f0/f1 paths,
is bounded by original W1(P,u) times the real all-δ one-coordinate
source Fourier tail union. No combinatorial 2^N is paid twice. -/
theorem parity_original_B590_full_physical_A_minus_box_le_W1_tail434
    (d : ℕ) (L E : ℝ) (hL : 0 < L) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    ‖parityOriginalB590FullPhysicalAAtU434 d L E u band slot -
      parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        (∑ δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∑ i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length,
            parityOriginalB590OneCoordinateFourierTail434 δ i T) := by
  let F := ((j : Fin (d+1)) → Fin 20 →
    {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
  let N := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let t : ℝ := ∑ δ : Fin N → Bool, ∑ i : Fin N,
    parityOriginalB590OneCoordinateFourierTail434 δ i T
  have hTailNonneg : 0 ≤ t := by
    apply Finset.sum_nonneg
    intro δ hδ
    apply Finset.sum_nonneg
    intro i hi
    unfold parityOriginalB590OneCoordinateFourierTail434
    exact mul_nonneg (setIntegral_nonneg measurableSet_Icc.compl
      (fun ξ _ => norm_nonneg _))
      (Finset.prod_nonneg (by intro j hj; exact integral_nonneg (fun ξ => norm_nonneg _)))
  have hWeight (f : F) : 0 ≤ parityActualOriginalAFullTupleWeight434 d L u f :=
    parity_actual_original_A_full_tuple_weight_nonneg434 d L u f
  have hTerm (f : F) :
    ‖((parityActualOriginalAFullTupleWeight434 d L u f : ℝ):ℂ) *
      (((parityActualOriginalAFullTupleAllocationMass434 d L E band slot f : ℝ):ℂ) -
        ∑ δ : Fin N → Bool,
          parityOriginalB590AllGateFourierBox434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) δ
            (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) T)‖ ≤
      parityActualOriginalAFullTupleWeight434 d L u f * t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hWeight f)]
    exact mul_le_mul_of_nonneg_left
      (parity_original_actual_fullQ_B590_mass_minus_fourier_box_le_union434
        d L E band slot f T) (hWeight f)
  have hA :
      (∑ f : F, parityActualOriginalAFullTupleWeight434 d L u f) ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
    have hSource := parity_actual_original_A_all_Q_labelled_exact434 d L hL u
    have hCoef :
        (∑ f : F, parityActualOriginalAFullTupleWeight434 d L u f) =
        sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
          (sourceOriginalPAllActualBands 20 L) u := by
      simpa only [parityActualOriginalAFullTupleWeight434] using hSource.symm
    rw [hCoef]
    exact parity_original_actual_A_le_true_W1434 d L u
  have hDiff :
      parityOriginalB590FullPhysicalAAtU434 d L E u band slot -
        parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T =
      ∑ f : F, ((parityActualOriginalAFullTupleWeight434 d L u f : ℝ):ℂ) *
        (((parityActualOriginalAFullTupleAllocationMass434 d L E band slot f : ℝ):ℂ) -
          ∑ δ : Fin N → Bool,
            parityOriginalB590AllGateFourierBox434 E
              (sourceActualSortedFrequencyScales 20 d L band slot) δ
              (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) T) := by
    unfold parityOriginalB590FullPhysicalAAtU434
      parityOriginalB590BoxPhysicalAAtU434
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro f hf
    ring
  rw [hDiff]
  calc
    _ ≤ ∑ f : F, ‖((parityActualOriginalAFullTupleWeight434 d L u f : ℝ):ℂ) *
        (((parityActualOriginalAFullTupleAllocationMass434 d L E band slot f : ℝ):ℂ) -
          ∑ δ : Fin N → Bool,
            parityOriginalB590AllGateFourierBox434 E
              (sourceActualSortedFrequencyScales 20 d L band slot) δ
              (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) T)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ f : F, parityActualOriginalAFullTupleWeight434 d L u f * t := by
      apply Finset.sum_le_sum
      intro f hf
      exact hTerm f
    _ = (∑ f : F, parityActualOriginalAFullTupleWeight434 d L u f)*t := by
      rw [Finset.sum_mul]
    _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u * t :=
      mul_le_mul_of_nonneg_right hA hTailNonneg
end Green64Analytic.Parity

end

end

/-! ## OriginalB590EWindowRetainedPhysical -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17500000

/-- Actual full original `u`-carrier Fourier BOX contribution with
selected integer e OUTSIDE Parity's historical [E L^-88,E] source interval.
Every original Q tuple with its product gate, factorial normalisation,
W1(P,u) and multiplicity-counted parity is retained, as is the real
original frequency box with all f0/f1 Boolean assignment histories. -/
def parityOriginalB590BoxPhysicalOutsideEAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) : ℂ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    ((parityActualOriginalAFullTupleWeight434 d L u f : ℝ):ℂ) *
      (∑ δ ∈ parityOriginalB590OutsideEWindowAssignments434
        d L E band slot f,
        parityOriginalB590AllGateFourierBox434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot f i).val) T)

/-- On the source-original physically retained beta/4 Ppart carrier,
with the literal `u>=exp L` and reserved Q-band `jQ` condition,
all out-of-[E L^-88,E] selected-e Fourier BOX contributions have
complex norm <= W1(P,u)*L^-A, uniformly in EVERY original source u,
full labelled Q tuple and reserved slot. False Q product gates carry
exactly ZERO original factorial weight; supported tuples have the
true original nonreserved Q capacity, and the all-delta Fourier
source tail proves the bound. No pointwise Fourier cut is assumed. -/
theorem parity_eventually_original_B590_retained_Ppart_outside_e_box_le_W1_all_log434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ <= beta/4) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (u : ℕ), Real.exp L ≤ (u:ℝ) →
        sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
          sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊ →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (slot : Fin 20),
      ‖parityOriginalB590BoxPhysicalOutsideEAtU434
         (sourceOriginalLiteralDepth 20 L) L E u band slot L‖ ≤
         sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u * L^(-A) := by
  filter_upwards [parity_eventually_original_B590_fullQ_outside_e_fourier_box_all_log434 A,
    parity_eventually_original_reserved_Q_band_in_moving_depth434 jQ]
    with L hWin hDepth
  refine ⟨hWin.1,hDepth,?_⟩
  intro E hE hEcap u hLarge hPcap band hb slot
  let d := sourceOriginalLiteralDepth 20 L
  let F := ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
  let w : F → ℝ := fun f => parityActualOriginalAFullTupleWeight434 d L u f
  let S : F → ℂ := fun f =>
      ∑ δ ∈ parityOriginalB590OutsideEWindowAssignments434 d L E band slot f,
        parityOriginalB590AllGateFourierBox434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) L
  have hLp : 0 < L := by linarith [hWin.1]
  have hu : u ≠ 0 := by
    intro he
    subst u
    norm_num at hLarge
    linarith [Real.exp_pos L]
  have hBandSmall : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4 := by
    rw [hb]
    exact hBand
  have hNonneg (f : F) : 0 ≤ w f :=
    parity_actual_original_A_full_tuple_weight_nonneg434 d L u f
  have hTerm (f : F) : ‖((w f:ℝ):ℂ)*S f‖ ≤ w f * L^(-A) := by
    by_cases hFull : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
        sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
    · have hMass := parity_actual_original_full_Q_tuple_beta_E_source_mass434
        beta hbeta d L hLp.le E hEcap u hu hLarge hPcap
        f hFull band hBandSmall slot
      have hC := hWin.2 E hE band slot f hMass
      dsimp only [S]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hNonneg f)]
      exact mul_le_mul_of_nonneg_left hC (hNonneg f)
    · have hz : w f=0 := by
        unfold w parityActualOriginalAFullTupleWeight434
        simp only [if_neg hFull]
      rw [hz]
      simp
  have hBound : (∑ f : F, w f) ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
    have hSource := parity_actual_original_A_all_Q_labelled_exact434 d L hLp u
    have hCoef : (∑ f : F, w f) =
        sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
          (sourceOriginalPAllActualBands 20 L) u := by
      simpa only [w,parityActualOriginalAFullTupleWeight434] using hSource.symm
    rw [hCoef]
    exact parity_original_actual_A_le_true_W1434 d L u
  have hPow : 0 ≤ L^(-A) := Real.rpow_nonneg hLp.le _
  unfold parityOriginalB590BoxPhysicalOutsideEAtU434
  change ‖∑ f : F, ((w f:ℝ):ℂ)*S f‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u * L^(-A)
  calc
    _ ≤ ∑ f : F, ‖((w f:ℝ):ℂ)*S f‖ := norm_sum_le _ _
    _ ≤ ∑ f : F, w f * L^(-A) := by
      apply Finset.sum_le_sum
      intro f hf
      exact hTerm f
    _ = (∑ f : F, w f)*L^(-A) := by rw [Finset.sum_mul]
    _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u * L^(-A) :=
      mul_le_mul_of_nonneg_right hBound hPow
end Green64Analytic.Parity

end

end

/-! ## OriginalB590EWindowAbsoluteMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The actual original 20-slot B590 N-dimensional Fourier BOX
for ONE history-dependent δ and Q-prime tuple has complex norm no
larger than the complete product of genuine source Schwartz Fourier
L1 gate masses. No pointwise e-window or beta/4 Ppart hypothesis. -/
theorem parity_original_B590_single_assignment_fourier_box_norm_le_L1_product434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ) (δ : Fin N → Bool)
    (p : Fin N → ℕ) (T : ℝ) :
    ‖parityOriginalB590AllGateFourierBox434 E s δ p T‖ ≤
      parityOriginalB590FourierBranchVariation434 δ := by
  rw [parity_original_B590_all_gate_fourier_box_eq_product434]
  rw [norm_prod]
  unfold parityOriginalB590FourierBranchVariation434
  apply Finset.prod_le_prod₀
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    exact parity_original_B590_single_gate_fourier_box_norm_le_L1434 E s δ p i T

/-- The genuine source outside-e Fourier BOX leakage per full-Q tuple
is bounded ABSOLUTELY by its true full 2^N f0/f1 Fourier variation,
without assuming true real B590 gates are nonzero or that the original
Ppart is beta-retained. This uniform bound is the input for the
ORIGINAL Rankin estimate on discarded Ppart configurations. -/
theorem parity_original_B590_fullQ_outside_e_fourier_box_norm_le_variation434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (T : ℝ) :
    ‖∑ δ ∈ parityOriginalB590OutsideEWindowAssignments434 d L E band slot f,
        parityOriginalB590AllGateFourierBox434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot f i).val) T‖ ≤
      ∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        parityOriginalB590FourierBranchVariation434 δ := by
  let N : ℕ := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let outside := parityOriginalB590OutsideEWindowAssignments434 d L E band slot f
  let p := fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  have hVarNonneg (δ : Fin N → Bool) :
      0 ≤ parityOriginalB590FourierBranchVariation434 δ := by
    unfold parityOriginalB590FourierBranchVariation434
    exact Finset.prod_nonneg (by intro i hi; exact integral_nonneg (fun ξ => norm_nonneg _))
  calc
    _ ≤ ∑ δ ∈ outside, ‖parityOriginalB590AllGateFourierBox434 E s δ p T‖ :=
        norm_sum_le _ _
    _ ≤ ∑ δ ∈ outside, parityOriginalB590FourierBranchVariation434 δ := by
        apply Finset.sum_le_sum
        intro δ hδ
        exact parity_original_B590_single_assignment_fourier_box_norm_le_L1_product434 E s δ p T
    _ ≤ ∑ δ : Fin N → Bool, parityOriginalB590FourierBranchVariation434 δ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ outside)
        intro δ hδ hn
        exact hVarNonneg δ

/-- The ORIGINAL source 20! factorial/W1/parity mass of outside-e
Fourier BOX contributions, WITHOUT any Pcap or Q capacity restriction,
is bounded by the literal source W1(P,u) times true total Fourier
variation. This keeps the retained and discarded Ppart terms separate
until the original beta/4 Rankin estimate is applied. -/
theorem parity_original_B590_outside_e_A_box_norm_le_W1_variation434
    (d : ℕ) (L E : ℝ) (hL : 0 < L) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    ‖parityOriginalB590BoxPhysicalOutsideEAtU434 d L E u band slot T‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      (∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        parityOriginalB590FourierBranchVariation434 δ) := by
  let F := ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
  let V : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → Bool,
    parityOriginalB590FourierBranchVariation434 δ
  have hV : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro δ hδ
    unfold parityOriginalB590FourierBranchVariation434
    exact Finset.prod_nonneg (by intro i hi; exact integral_nonneg (fun ξ => norm_nonneg _))
  have hw (f : F) : 0 ≤ parityActualOriginalAFullTupleWeight434 d L u f :=
    parity_actual_original_A_full_tuple_weight_nonneg434 d L u f
  have hTerm (f : F) :
      ‖((parityActualOriginalAFullTupleWeight434 d L u f:ℝ):ℂ) *
        (∑ δ ∈ parityOriginalB590OutsideEWindowAssignments434 d L E band slot f,
          parityOriginalB590AllGateFourierBox434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) δ
            (fun i => (parityActualSourceRemainingFullQTuple434
              d L band slot f i).val) T)‖ ≤
      parityActualOriginalAFullTupleWeight434 d L u f * V := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw f)]
    exact mul_le_mul_of_nonneg_left
      (parity_original_B590_fullQ_outside_e_fourier_box_norm_le_variation434
        d L E band slot f T) (hw f)
  have hSum : (∑ f : F, parityActualOriginalAFullTupleWeight434 d L u f) ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
    have hSource := parity_actual_original_A_all_Q_labelled_exact434 d L hL u
    have hEq : (∑ f : F, parityActualOriginalAFullTupleWeight434 d L u f) =
        sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
          (sourceOriginalPAllActualBands 20 L) u := by
      simpa only [parityActualOriginalAFullTupleWeight434] using hSource.symm
    rw [hEq]
    exact parity_original_actual_A_le_true_W1434 d L u
  unfold parityOriginalB590BoxPhysicalOutsideEAtU434
  calc
    _ ≤ ∑ f : F, ‖((parityActualOriginalAFullTupleWeight434 d L u f:ℝ):ℂ) *
        (∑ δ ∈ parityOriginalB590OutsideEWindowAssignments434 d L E band slot f,
          parityOriginalB590AllGateFourierBox434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) δ
            (fun i => (parityActualSourceRemainingFullQTuple434
              d L band slot f i).val) T)‖ := norm_sum_le _ _
    _ ≤ ∑ f : F, parityActualOriginalAFullTupleWeight434 d L u f * V := by
      apply Finset.sum_le_sum
      intro f hf
      exact hTerm f
    _ = (∑ f : F, parityActualOriginalAFullTupleWeight434 d L u f)*V := by
      rw [Finset.sum_mul]
    _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u * V :=
      mul_le_mul_of_nonneg_right hSum hV
end Green64Analytic.Parity

end

end

/-! ## OriginalB590EWindowPsiPointwise -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- TRUE original Parity(4.5) Fourier-box e-window truncation loss at a
single SOURCE integer u, with real Ψ supported [1,2], 0<=Ψ<=1.
The retained beta/4 Ppart receives arbitrary L^-A saving; the
DISCARDED Ppart receives only its honest total Fourier variation.
One must not assume e-support at each fixed Fourier ξ or impose
Q-product capacity on discarded Pparts. This is the literal pointwise
bridge required before summing the complete alpha_m beta_n bilinear
source over mn=u+2. -/
theorem parity_eventually_original_B590_outside_e_Psi_pointwise_bound434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (u : ℕ)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (slot : Fin 20),
      ‖parityOriginalB590BoxPhysicalOutsideEAtU434
          (sourceOriginalLiteralDepth 20 L) L E u band slot L *
          (Psi ((u:ℝ)/Real.exp L) : ℂ)‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        (L^(-A) +
          if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ) else
            ∑ δ : Fin (sourceOrderedLabels 20
              (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
              band slot).length → Bool,
              parityOriginalB590FourierBranchVariation434 δ) := by
  filter_upwards [parity_eventually_original_B590_retained_Ppart_outside_e_box_le_W1_all_log434
      beta A hbeta jQ hBand] with L hRetained
  refine ⟨hRetained.1,hRetained.2.1,?_⟩
  intro E hE hEcap Psi hSupport hPsi0 hPsi1 u band hb slot
  let d := sourceOriginalLiteralDepth 20 L
  let W := sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u
  let D := parityOriginalB590BoxPhysicalOutsideEAtU434 d L E u band slot L
  let V : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      parityOriginalB590FourierBranchVariation434 δ
  let psi := Psi ((u:ℝ)/Real.exp L)
  have hLp : 0 < L := by linarith [hRetained.1]
  have hW : 0 ≤ W := source_original_W1_nonneg _ _
  have hA : 0 ≤ L^(-A) := Real.rpow_nonneg hLp.le _
  have hV : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro δ hδ
    unfold parityOriginalB590FourierBranchVariation434
    exact Finset.prod_nonneg (by intro i hi; exact integral_nonneg (fun ξ => norm_nonneg _))
  have hPsiPos : 0 ≤ psi := hPsi0 _
  have hPsiUp : psi ≤ 1 := hPsi1 _
  have hScalar : ‖(psi:ℂ)‖ = psi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hPsiPos]
  have hPos : 0 ≤ W*(L^(-A)+(if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ) else V)) := by
    apply mul_nonneg hW
    by_cases hc : parityOriginalPhysicalPcapBeta434 beta L u
    · simpa [hc] using hA
    · simpa [hc] using add_nonneg hA hV
  by_cases hZero : psi=0
  · rw [norm_mul,hScalar,hZero,mul_zero]
    exact hPos
  · have hMem : ((u:ℝ)/Real.exp L) ∈ Set.Icc (1:ℝ) 2 :=
      hSupport (by simpa [Function.mem_support,psi] using hZero)
    have hLarge : Real.exp L ≤ (u:ℝ) := by
      have hp := Real.exp_pos L
      have h := (le_div_iff₀ hp).mp hMem.1
      simpa only [one_mul] using h
    by_cases hc : parityOriginalPhysicalPcapBeta434 beta L u
    · have hPcap : sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
          sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊ :=
        (parity_actual_original_beta_Pcap_mem434 beta L u).2 hc
      have hD := hRetained.2.2 E hE hEcap u hLarge hPcap band hb slot
      rw [norm_mul,hScalar]
      have hBound : ‖D‖*psi ≤ W*L^(-A) :=
        (mul_le_mul_of_nonneg_right hD hPsiPos).trans
          (mul_le_of_le_one_right (mul_nonneg hW hA) hPsiUp)
      simpa only [if_pos hc, add_zero] using hBound
    · have hD := parity_original_B590_outside_e_A_box_norm_le_W1_variation434
        d L E hLp u band slot L
      rw [norm_mul,hScalar]
      have hBound : ‖D‖*psi ≤ W*V :=
        (mul_le_mul_of_nonneg_right hD hPsiPos).trans
          (mul_le_of_le_one_right (mul_nonneg hW hV) hPsiUp)
      have hMon : W*V ≤ W*(L^(-A)+V) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA) hW
      simpa only [if_neg hc] using hBound.trans hMon
end Green64Analytic.Parity

end

end

/-! ## OriginalXAPcapWeightedBound -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Original Parity source f0/f1 buffer defect is bounded by W1 with
ORIGINAL parity and factorial normalization on the precise u carrier.
The full x=exp L XA defect is supported only on the beta/4 Ppart
failure; with the actual smooth 0<=Psi<=1 the remaining loss is no
larger than the original W1 mass of exactly these discarded u. -/
theorem parity_original_XA_beta_buffer_defect_le_discarded_W1_range434
    (beta : ℝ) (hbeta : 0 < beta)
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hElo : 1 ≤ E) (hEhi : E ≤ Real.exp ((1-beta)*L))
    (Psi : ℝ → ℝ)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsi0 : ∀ t, 0 ≤ Psi t) (hPsi1 : ∀ t, Psi t ≤ 1)
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4)
    (slot : Fin 20) :
    0 ≤ parityActualOriginalXAAllocationDefect434 d L E (Real.exp L) Psi band slot ∧
    parityActualOriginalXAAllocationDefect434 d L E (Real.exp L) Psi band slot ≤
      ∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
  have hPos := parity_actual_original_XA_allocation_defect_nonneg434
    d L E (Real.exp L) Psi hPsi0 band slot
  constructor
  · exact hPos
  · rw [parity_original_XA_B590_allocation_defect_only_beta_Pcap_fail434
      beta hbeta d L E hL hElo hEhi Psi hSupport band hBand slot]
    apply Finset.sum_le_sum
    intro u hu
    by_cases hCap : parityOriginalPhysicalPcapBeta434 beta L u
    · simp only [if_pos hCap]
      exact le_refl _
    · simp only [if_neg hCap]
      have hBound := parity_original_actual_A_buffer_defect_le_W1434
        d L E hL u band slot
      have hPsi := hPsi0 ((u:ℝ)/Real.exp L)
      have hPsiHi := hPsi1 ((u:ℝ)/Real.exp L)
      exact (mul_le_mul_of_nonneg_right hBound.2 hPsi).trans
        (mul_le_of_le_one_right (source_original_W1_nonneg _ _) hPsiHi)
end Green64Analytic.Parity

end

end

/-! ## OriginalXABufferRankin -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The initial u=0 term in the real original source Ppart cap is
retained, not discarded: the empty prime-product is one. -/
theorem parity_original_beta_Ppart_cap_at_zero434
    (beta L : ℝ) (hbeta : 0 < beta) (hL : 0 ≤ L) :
    parityOriginalPhysicalPcapBeta434 beta L 0 := by
  unfold parityOriginalPhysicalPcapBeta434
  simp [sourceOriginalPPrimePart]
  nlinarith [mul_nonneg (le_of_lt hbeta) hL]

/-- Exact algebraic boundary conversion from the XA carrier range
[0,Y] to original source Parity(4.3) Rankin carrier (0,Y], provided
the zero contribution is proven to vanish. -/
theorem parity_original_Pcap_discard_range_eq_Ioc434
    (beta L : ℝ) (hbeta : 0 < beta) (hL : 0 ≤ L) (Y : ℕ) :
    (∑ u ∈ Finset.range (Y+1),
      if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
      else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) =
    ∑ u ∈ Finset.Ioc 0 Y,
      if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
      else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
  let f : ℕ → ℝ := fun u =>
    if parityOriginalPhysicalPcapBeta434 beta L u then 0
    else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u
  have hZero : f 0 = 0 := by
    simp [f, parity_original_beta_Ppart_cap_at_zero434 beta L hbeta hL]
  change (∑ u ∈ Finset.range (Y+1), f u) = ∑ u ∈ Finset.Ioc 0 Y, f u
  induction Y with
  | zero => simp [hZero]
  | succ Y ih =>
      rw [Finset.sum_range_succ]
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le Y)]
      rw [ih]

/-- SOURCE-EXACT complete XA B590 discarded-buffer error inherits
Parity(4.3) arbitrary inverse-log accuracy, with no factor 2^N or missing
factorials: actual source 0≤Ψ≤1, original Ppart cap exp(beta L/4),
original r0=20 Q labels and fixed reserved Q band. This is the full
physical ORIGINAL source discrepancy estimate, not Type II (4.2). -/
theorem parity_eventually_original_XA_B590_buffer_defect_all_log434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20),
      0 ≤ parityActualOriginalXAAllocationDefect434
        (sourceOriginalLiteralDepth 20 L) L E (Real.exp L) Psi band slot ∧
      parityActualOriginalXAAllocationDefect434
        (sourceOriginalLiteralDepth 20 L) L E (Real.exp L) Psi band slot ≤
          (2*Real.exp L)*L^(-A) := by
  filter_upwards [parity_eventually_original_reserved_Q_band_in_moving_depth434 jQ,
    parity_eventually_original_beta_physical_Pcap_discard_all_log434 beta A hbeta,
    eventually_ge_atTop (2:ℝ)] with L hDepth hRankin hL
  refine ⟨hL,hDepth,?_⟩
  intro band hBandEq E hElo hEhi Psi hSupport hPsi0 hPsi1 slot
  let d := sourceOriginalLiteralDepth 20 L
  have hLarge : 0 < L := by linarith
  have hBandSmall : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4 := by
    rw [hBandEq]
    exact hBand
  have hBound := parity_original_XA_beta_buffer_defect_le_discarded_W1_range434
    beta hbeta d L E hLarge hElo hEhi Psi hSupport hPsi0 hPsi1
    band hBandSmall slot
  have hEq := parity_original_Pcap_discard_range_eq_Ioc434 beta L hbeta
    (le_of_lt hLarge) (⌊2*Real.exp L⌋₊)
  rw [hEq] at hBound
  have hRankinY := hRankin (⌊2*Real.exp L⌋₊)
  have hFloor : (⌊2*Real.exp L⌋₊:ℝ) ≤ 2*Real.exp L :=
    Nat.floor_le (by positivity)
  have hPow : 0 ≤ L^(-A) := Real.rpow_nonneg (le_of_lt hLarge) _
  constructor
  · exact hBound.1
  · exact hBound.2.trans
      (hRankinY.trans (mul_le_mul_of_nonneg_right hFloor hPow))
end Green64Analytic.Parity

end

end

/-! ## OriginalXAPhysicalAllLog -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 34000

/-- Parity §4.2 exact historical XA to physical B590/B509 zero-frequency
selected-e/v transfer WITH actual arbitrary inverse-log source loss.
All original 20! orbit normalisations, r0=20 Q/P labels, P-parity,
reserved Q band jQ, real original Psi and the full u carrier survive.
This is not a historical post-Mellin a_e(4.7) identification and does
not assert the signed Type II (4.2) distribution. -/
theorem parity_eventually_original_XA_physical_selected_e_v_all_log434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20),
      ‖((sourceOriginalXA 20
         (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
         (sourceOriginalPAllActualBands 20 L) (Real.exp L) Psi : ℝ) : ℂ) -
        (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
          (∑ e ∈ ((Finset.univ : Finset
            (parityActualOriginalAFullBranchCarrier434
              (sourceOriginalLiteralDepth 20 L) L band slot)).image
                (parityActualOriginalAFullBranchE434
                  (sourceOriginalLiteralDepth 20 L) L band slot)),
            sourceEndpointFibre
              (Finset.univ : Finset
                (parityActualOriginalAFullBranchCarrier434
                  (sourceOriginalLiteralDepth 20 L) L band slot))
              (parityActualOriginalAFullBranchE434
                (sourceOriginalLiteralDepth 20 L) L band slot)
              (parityActualOriginalAFullBranchVWeight434
                (sourceOriginalLiteralDepth 20 L) L E u band slot
                (fun _ => 0)) e) *
          (Psi ((u:ℝ)/(Real.exp L)) : ℂ))‖ ≤
        (2*Real.exp L)*L^(-A) := by
  filter_upwards [parity_eventually_original_XA_B590_buffer_defect_all_log434
    beta A hbeta jQ hBand] with L hBound
  refine ⟨hBound.1, hBound.2.1, ?_⟩
  intro band hBandEq E hElo hEhi Psi hSupport hPsi0 hPsi1 slot
  have hDefect := hBound.2.2 band hBandEq E hElo hEhi
    Psi hSupport hPsi0 hPsi1 slot
  have hL : 0 < L := by linarith [hBound.1]
  have hPsiAtZero := parity_original_Psi_support_zero434 Psi hSupport
  have hXA := parity_actual_original_XA_physical_e_fibre_all_u_plus_defect434
    (sourceOriginalLiteralDepth 20 L) L E (Real.exp L) hL rfl
    Psi hPsiAtZero band slot
  rw [hXA]
  simp only [add_sub_cancel_left]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hDefect.1]
  exact hDefect.2
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearPairDivisor -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact original Parity shifted `a=1,b=2` ordered bilinear fibre:
positive m,n only, no replacements by an unshifted convolution or
independent index sequences. -/
def parityOriginalShiftTwoPositivePairFibre434
    (K J : Finset ℕ) (u : ℕ) : Finset (ℕ × ℕ) :=
  (K.product J).filter (fun z => 0 < z.1 ∧ 0 < z.2 ∧ z.1*z.2=u+2)

/-- Full original `mn=u+2` fibre has at most the ACTUAL divisor count
of `u+2`, with exact shift and no multiplicity loss. Each admissible
pair is injectively determined by its positive first coordinate. -/
theorem parity_original_shift_two_positive_pair_card_le_tau434
    (K J : Finset ℕ) (u : ℕ) :
    (parityOriginalShiftTwoPositivePairFibre434 K J u).card ≤
      (u+2).divisors.card := by
  let S := parityOriginalShiftTwoPositivePairFibre434 K J u
  apply Finset.card_le_card_of_injOn (fun z : ℕ × ℕ => z.1)
  · intro z hz
    have hh := (Finset.mem_filter.mp hz).2
    exact Nat.mem_divisors.mpr ⟨by use z.2; exact hh.2.2.symm,
      by omega⟩
  · intro a ha b hb hEq
    have hA := (Finset.mem_filter.mp ha).2
    have hB := (Finset.mem_filter.mp hb).2
    change a.1 = b.1 at hEq
    apply Prod.ext
    · exact hEq
    · have heq : a.1*a.2 = a.1*b.2 := by
        calc
          a.1*a.2 = u+2 := hA.2.2
          _ = b.1*b.2 := hB.2.2.symm
          _ = a.1*b.2 := by rw [hEq]
      exact Nat.mul_left_cancel hA.1 heq

/-- The original shifted fibre cardinal bound also handles a complete
complex bilinear expression without losing alpha or beta restrictions.
Only the actual finite K,J supports enter the bound. -/
theorem parity_original_shift_two_bilinear_fibre_norm_le_tau434
    (K J : Finset ℕ) (u : ℕ)
    (α β : ℕ → ℂ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hα : ∀ m ∈ K, ‖α m‖ ≤ A)
    (hβ : ∀ n ∈ J, ‖β n‖ ≤ B) :
    ‖∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
      α z.1 * β z.2‖ ≤
      ((u+2).divisors.card:ℝ)*A*B := by
  let S := parityOriginalShiftTwoPositivePairFibre434 K J u
  have hMain := norm_sum_le S (fun z => α z.1 * β z.2)
  have hBound (z : ℕ × ℕ) (hz : z ∈ S) :
      ‖α z.1 * β z.2‖ ≤ A*B := by
    have hmem := (Finset.mem_filter.mp hz).1
    have hp := Finset.mem_product.mp hmem
    rw [norm_mul]
    exact mul_le_mul (hα z.1 hp.1) (hβ z.2 hp.2)
      (norm_nonneg _) hA
  calc
    _ ≤ ∑ z ∈ S, ‖α z.1*β z.2‖ := hMain
    _ ≤ (S.card:ℝ)*(A*B) := by
      simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul S
        (fun z => ‖α z.1*β z.2‖) (A*B) hBound
    _ ≤ ((u+2).divisors.card:ℝ)*(A*B) := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast parity_original_shift_two_positive_pair_card_le_tau434 K J u)
        (mul_nonneg hA hB)
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearBufferPreCauchy -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The full ORIGINAL SOURCE Q-factored B590 buffer defect at an actual
integer u, preserving every 20! label, P parity and W1 valuation. -/
def parityOriginalFullQBufferDefectAtU434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (u : ℕ) : ℝ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    parityActualOriginalAFullTupleWeight434 d L u f *
      (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)

/-- An exact pre-Cauchy error on the ORIGINAL Parity h=-2 bilinear source
`mn=u+2`. Its coefficient is the genuine P/Q/factorial/parity B590
allocation defect (no fictitious endpoint, multiplicity or alpha class)
and the original real Ψ(u/x), rather than scalar XA alone. -/
def parityOriginalShiftTwoBilinearBufferError434
    (d : ℕ) (L E : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ)
    (α β : ℕ → ℂ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    ((parityOriginalFullQBufferDefectAtU434 d L E band slot u *
      Psi ((u:ℝ)/Real.exp L) : ℝ) : ℂ) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1 * β z.2)

/-- Full ORIGINAL Parity h=-2 absolute-error bridge before Cauchy:
The old scalar XA buffer mass is promoted into the exact bilinear
`mn=u+2` source, with REAL alpha/beta support retained, and only
an honest shifted divisor τ(u+2) envelope introduced. On the true
beta/4-retained Ppart and Ψ-support the error is identically zero.
There is no unstated pointwise τ≤polylog assumption. -/
theorem parity_original_shift_two_bilinear_buffer_pre_cauchy_tau434
    (betaP : ℝ) (hbetaP : 0 < betaP)
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hElo : 1 ≤ E) (hEhi : E ≤ Real.exp ((1-betaP)*L))
    (Psi : ℝ → ℝ)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsi0 : ∀ t, 0 ≤ Psi t) (hPsi1 : ∀ t, Psi t ≤ 1)
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ betaP/4)
    (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hα : ∀ m ∈ K, ‖α m‖ ≤ A)
    (hβ : ∀ n ∈ J, ‖β n‖ ≤ B) :
    ‖parityOriginalShiftTwoBilinearBufferError434
      d L E band slot Psi K J α β (⌊2*Real.exp L⌋₊)‖ ≤
      A*B*(∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) := by
  classical
  let Y := ⌊2*Real.exp L⌋₊
  let D := parityOriginalFullQBufferDefectAtU434 d L E band slot
  let C := fun u => ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
    α z.1 * β z.2
  have hD (u : ℕ) : 0 ≤ D u ∧
      D u ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u :=
    parity_original_actual_A_buffer_defect_le_W1434 d L E hL u band slot
  have hRetained (u : ℕ) (hLarge : Real.exp L ≤ (u:ℝ))
      (hCap : parityOriginalPhysicalPcapBeta434 betaP L u) : D u = 0 :=
    parity_original_beta_retained_XA_at_u_defect_zero434
      betaP hbetaP d L E hL hElo hEhi u hLarge hCap band hBand slot
  have hTerm (u : ℕ) (hu : u ∈ Finset.range (Y+1)) :
      ‖((D u * Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) * C u‖ ≤
      A*B*(if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) := by
    have hC := parity_original_shift_two_bilinear_fibre_norm_le_tau434
      K J u α β A B hA hB hα hβ
    have hD0 := (hD u).1
    have hDhi := (hD u).2
    have hPsiPos := hPsi0 ((u:ℝ)/Real.exp L)
    have hPsiHi := hPsi1 ((u:ℝ)/Real.exp L)
    by_cases hCap : parityOriginalPhysicalPcapBeta434 betaP L u
    · by_cases hPsiZero : Psi ((u:ℝ)/Real.exp L)=0
      · simp [hCap,hPsiZero]
      · have hS : ((u:ℝ)/Real.exp L) ∈ Set.Icc (1:ℝ) 2 :=
          hSupport (by simpa [Function.mem_support] using hPsiZero)
        have huLarge : Real.exp L ≤ (u:ℝ) := by
          have hExp : 0 < Real.exp L := Real.exp_pos _
          have h := (le_div_iff₀ hExp).mp hS.1
          simpa only [one_mul] using h
        have hZero := hRetained u huLarge hCap
        simp [hCap,hZero]
    · simp only [if_neg hCap]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hD0 hPsiPos)]
      have hProd : D u * Psi ((u:ℝ)/Real.exp L) ≤
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
        calc
          _ ≤ D u := mul_le_of_le_one_right hD0 hPsiHi
          _ ≤ _ := hDhi
      have hTauNonneg : 0 ≤ ((u+2).divisors.card:ℝ) := Nat.cast_nonneg _
      have hAB : 0 ≤ A*B := mul_nonneg hA hB
      calc
        _ ≤ (D u * Psi ((u:ℝ)/Real.exp L)) *
            (((u+2).divisors.card:ℝ)*A*B) :=
              mul_le_mul_of_nonneg_left hC (mul_nonneg hD0 hPsiPos)
        _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
            (((u+2).divisors.card:ℝ)*A*B) :=
              mul_le_mul_of_nonneg_right hProd
                (by positivity)
        _ = A*B*(sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
            ((u+2).divisors.card:ℝ)) := by ring
  unfold parityOriginalShiftTwoBilinearBufferError434
  dsimp only [parityOriginalFullQBufferDefectAtU434]
  have hTri := norm_sum_le (Finset.range (Y+1))
    (fun u => ((D u*Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)*C u)
  calc
    _ ≤ ∑ u ∈ Finset.range (Y+1),
        ‖((D u*Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)*C u‖ := hTri
    _ ≤ ∑ u ∈ Finset.range (Y+1),
        A*B*(if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
          else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) := Finset.sum_le_sum hTerm
    _ = _ := by rw [←Finset.mul_sum]
end Green64Analytic.Parity

end

end

