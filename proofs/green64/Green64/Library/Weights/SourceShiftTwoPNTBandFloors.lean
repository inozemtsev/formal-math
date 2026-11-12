module

public import Green64.Library.Sieve.Foundation.Lemma9.Part005
public import Green64.Library.Weights.Part006
public import Mathlib
public import Green64.Library.Analysis.Estimates.Part002

@[expose] public section

/-!
# Weights / SourceShiftTwoPNTBandFloors

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceShiftTwoPNTBandFloors -/

section

set_option maxHeartbeats 4000000
open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

private theorem pntBandError_tendsto_zero (a M C : ℝ) (ha : 0 < a) :
    Tendsto (fun L : ℝ =>
      C*(2+(M-a)*L)/(a*L)^2+(a*L)⁻¹) atTop (𝓝 0) := by
  have hInv : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have h1 : Tendsto (fun L : ℝ =>
      (2*C/a^2)*(L⁻¹)^2) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul (hInv.pow 2) using 1 <;> simp
  have h2 : Tendsto (fun L : ℝ =>
      (C*(M-a)/a^2 + 1/a)*L⁻¹) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hInv using 1 <;> simp
  have hPoly : Tendsto (fun L : ℝ =>
      (2*C/a^2)*(L⁻¹)^2 +
      (C*(M-a)/a^2 + 1/a)*L⁻¹) atTop (𝓝 0) := by
    convert h1.add h2 using 1 <;> simp
  apply hPoly.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have hL0 : L ≠ 0 := ne_of_gt hL
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp
  <;> ring

/-- The source [exp(uL), exp(vL)] macro band has positive reciprocal
prime mass, unconditionally from the separately kernel-checked PNT2.
The half-open cell is a subset of the source closed interval. -/
theorem source_prime_log_band_floor_unconditional
    (a M u v : ℝ) (ha : 0 < a)
    (hau : a ≤ u) (huv : u ≤ v) (hvM : v ≤ M)
    (hratio : (6/5:ℝ)*u ≤ v) :
    ∀ᶠ L : ℝ in atTop,
      Real.log (6/5:ℝ)/2 ≤
        ∑ p ∈ sourcePrimeLogBand L u v, (p:ℝ)⁻¹ := by
  have hlog : 0 < Real.log (6/5:ℝ)/2 := by
    have : (1:ℝ) < 6/5 := by norm_num
    have := Real.log_pos this
    linarith
  obtain ⟨C,hC,hPNT⟩ :=
    Green64Analytic.SourcePNT2.source_pnt2_unconditional a ha
  have hErr : Tendsto (fun L : ℝ =>
      C*(2+(M-a)*L)/(a*L)^2+(a*L)⁻¹) atTop (𝓝 0) :=
    pntBandError_tendsto_zero a M C ha
  have hSmall : ∀ᶠ L : ℝ in atTop,
      C*(2+(M-a)*L)/(a*L)^2+(a*L)⁻¹ <
        Real.log (6/5:ℝ)/2 :=
    hErr.eventually (eventually_lt_nhds hlog)
  have hReady : ∀ᶠ L : ℝ in atTop, 1 ≤ a*L := by
    filter_upwards [eventually_ge_atTop (1/a)] with L hL
    have : 0 < a := ha
    have := (mul_le_mul_of_nonneg_left hL ha.le)
    have ha0 : a ≠ 0 := ne_of_gt ha
    field_simp at this
    nlinarith
  have hu0 : 0 < u := ha.trans_le hau
  have hratio' : (6/5:ℝ) ≤ v/u :=
    (le_div_iff₀ hu0).2 hratio
  have hlogRatio : Real.log (6/5:ℝ) ≤ Real.log (v/u) :=
    Real.log_le_log (by norm_num) hratio'
  filter_upwards [hPNT,hSmall,hReady] with L hp hs hr
  have hMass := Green64Analytic.ReciprocalPrimeGrid.uniform_prime_reciprocal_log_error
    a M L C ha hr hC hp u v hau huv hvM
  have hMass' :
      |(∑ p ∈ sourcePrimeLogBand L u v, (p:ℝ)⁻¹) -
        Real.log (v/u)| ≤
          C*(2+(M-a)*L)/(a*L)^2+(a*L)⁻¹ := by
    simpa only [sourcePrimeLogBand, Finset.sum_filter] using hMass
  have hLeft := (abs_le.mp hMass').1
  linarith

end Green64Analytic.SourceBlockSieve

end

