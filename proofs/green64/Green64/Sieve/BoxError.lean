module

public import Green64.Sieve.BoxRemainder
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# The rectangle remainder is smaller than the main term

Turn the explicit exponential remainder bound into a little-o estimate.
The estimate is uniform in the parity sign and the permitted roughness
cutoff, so it can be used before summing the dyadic rectangles.
-/

section

set_option maxHeartbeats 1800000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

noncomputable def boxErrorDecay (L : ℝ) : ℝ :=
  L ^ 6 * (Real.exp (-(9 / 25 : ℝ) * L) + Real.exp (-(4 / 5 : ℝ) * L))

theorem box_error_decay_tendsto :
    Tendsto boxErrorDecay atTop (𝓝 0) := by
  unfold boxErrorDecay
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (6 : ℝ) (9 / 25 : ℝ) (by norm_num)
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (6 : ℝ) (4 / 5 : ℝ) (by norm_num)
  simpa only [Real.rpow_natCast, Real.rpow_ofNat, zero_add, boxErrorDecay, mul_add]
    using h1.add h2

theorem box_error_scale_identity (L : ℝ) (hL : 0 < L) :
    L ^ 3 * (Real.exp ((16 / 25 : ℝ) * L) + Real.exp ((1 / 5 : ℝ) * L)) =
      boxErrorDecay L * (Real.exp L / L ^ 3) := by
  have h1 : Real.exp (-(9 / 25 : ℝ) * L) * Real.exp L =
      Real.exp ((16 / 25 : ℝ) * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-(4 / 5 : ℝ) * L) * Real.exp L =
      Real.exp ((1 / 5 : ℝ) * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold boxErrorDecay
  calc
    _ = (L ^ 6 / L ^ 3) * (Real.exp ((16 / 25 : ℝ) * L) + Real.exp ((1 / 5 : ℝ) * L)) := by
      field_simp [ne_of_gt hL] <;> ring
    _ = (L ^ 6 / L ^ 3) *
        (Real.exp (-(9 / 25 : ℝ) * L) * Real.exp L +
          Real.exp (-(4 / 5 : ℝ) * L) * Real.exp L) := by rw [h1, h2]
    _ = _ := by ring

/-- The total finite assignment/CRT error is uniformly little-o
of the Xrho*V(W)^2 scale, for both parity signs and every
admissible physical side sum. The denominator lower bound is proved,
not assumed. -/
theorem box_error_uniform_little_o
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t)
    (Cside : ℝ) (hCside : 0 < Cside) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ L : ℝ in atTop,
        ∀ (flag : Bool) (W T : ℝ),
        W ≤ Real.exp (parityOriginalAssignmentTheta434 * L) →
        0 ≤ T → T ≤ Cside * Real.exp ((27 / 50 : ℝ) * L) →
        boxFiniteError L T ≤
          epsilon * (localizedMass Psi (parityOriginalParitySign434 flag) L *
            (sourceNaturalEuler ⌊W⌋₊) ^ 2) := by
  obtain ⟨cden, hcden, hden⟩ := box_denominator_lower_eventually
    Psi hCont hSupport hNonneg hInterior
  intro epsilon hepsilon
  have hlim : Tendsto
      (fun L : ℝ => boxErrorConstant Cside * boxErrorDecay L)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul box_error_decay_tendsto
  have hsmall : ∀ᶠ L : ℝ in atTop,
      boxErrorConstant Cside * boxErrorDecay L <
        epsilon * cden :=
    hlim.eventually (gt_mem_nhds (mul_pos hepsilon hcden))
  filter_upwards [hsmall, hden, eventually_ge_atTop (1 : ℝ)] with L hs hd hL1
  intro flag W T hW hT0 hT
  have hL : 0 < L := hd.1
  have hQ := box_HQ_nonneg 20 (sourceOriginalLiteralDepth 20 L) L
  have hscale : 0 ≤ (Real.exp L / L ^ 3) *
      sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L :=
    mul_nonneg (div_nonneg (Real.exp_pos _).le (pow_nonneg hL.le 3)) hQ
  have hh := mul_le_mul_of_nonneg_right hs.le hscale
  calc
    _ ≤ boxErrorConstant Cside *
        sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L *
        L ^ 3 * (Real.exp ((16 / 25 : ℝ) * L) + Real.exp ((1 / 5 : ℝ) * L)) :=
      box_finite_error_exp_bound Cside L T hCside hL1 hT0 hT
    _ = boxErrorConstant Cside *
        sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L *
        (L ^ 3 * (Real.exp ((16 / 25 : ℝ) * L) + Real.exp ((1 / 5 : ℝ) * L))) := by ring
    _ = (boxErrorConstant Cside * boxErrorDecay L) *
        ((Real.exp L / L ^ 3) * sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L) := by
      rw [box_error_scale_identity L hL]
      ring
    _ ≤ (epsilon * cden) *
        ((Real.exp L / L ^ 3) * sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L) := hh
    _ = epsilon * (cden * Real.exp L / L ^ 3 *
        sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hd.2 flag W hW) hepsilon.le

end Green64Analytic.Parity

end
