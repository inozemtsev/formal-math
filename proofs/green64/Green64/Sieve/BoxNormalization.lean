module

public import Green64.Sieve.EulerProduct
public import Green64.Library.Sieve.Foundations.Part050

@[expose] public section

/-!
# Normalize rectangle estimates by the localized mass

Compare the Euler-product main term of the rectangle sieve with the
localized mass. The harmonic lower bounds for the selected prime bands
provide a common positive normalization.
-/

section

set_option maxHeartbeats 1800000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

theorem box_HQ_nonneg (r d : ℕ) (L : ℝ) :
    0 ≤ sourceOriginalQActualHQ r d L := by
  unfold sourceOriginalQActualHQ
  apply Finset.prod_nonneg
  intro j hj
  apply div_nonneg
  · apply pow_nonneg
    exact Finset.sum_nonneg (fun p hp => inv_nonneg.mpr (Nat.cast_nonneg p))
  · exact Nat.cast_nonneg _

/-- The already proved strong mass, with a single constant
and a common threshold for both parity flags. -/
theorem box_strong_mass_shared
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ᶠ L : ℝ in atTop,
      0 < L ∧
      1 ≤ sourceLiteralHP (sourceOriginalPAllActualBands 20 L) ∧
      ∀ flag : Bool,
        c0 * (Real.exp L / L) *
          (sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L *
            sourceLiteralHP (sourceOriginalPAllActualBands 20 L)) ≤
        localizedMass Psi (parityOriginalParitySign434 flag) L := by
  have hPsi0 : Psi 0 = 0 := by
    by_contra h
    have hh := hSupport (show (0 : ℝ) ∈ Function.support Psi from h)
    norm_num at hh
  obtain ⟨a, b, c, ha, hab, hb, hc, hPsi⟩ :=
    b635_original_cutoff_positive_interval434 Psi hCont hInterior
  have hF := parity_original_XA_literal_depth_lower_eventually_parity434
    false 20 (by norm_num) a b c Psi hPsi0 ha hab hb hc hNonneg hPsi
  have hT := parity_original_XA_literal_depth_lower_eventually_parity434
    true 20 (by norm_num) a b c Psi hPsi0 ha hab hb hc hNonneg hPsi
  refine ⟨sourceOriginalXAFixedConstant 20 a b c,
    source_original_XA_fixed_constant_pos 20 (by norm_num) a b c ha hab hc, ?_⟩
  filter_upwards [hF, hT, b635_actual_HP_one_le434 20,
    eventually_gt_atTop (0 : ℝ)] with L hF hT hHP hL
  refine ⟨hL, hHP, ?_⟩
  intro flag
  cases flag
  · simpa only [parity_original_parity_XA_eq_Xrho434] using hF
  · simpa only [parity_original_parity_XA_eq_Xrho434] using hT

noncomputable def boxMainConstant : ℝ :=
  (200 : ℝ) ^ 400 * Real.exp (parityOriginalShiftTwoSieveRho434 2) *
    Real.exp (1 / 2 : ℝ) * 8 * Real.exp 1

theorem box_main_constant_pos :
    0 < boxMainConstant := by
  unfold boxMainConstant
  positivity

theorem box_main_exact (d : ℕ) (L W : ℝ) (A B C E : ℕ) :
    parityOriginalNormalizedBoxMainBound434 d L W A B C E =
      boxMainConstant *
        (((B - A : ℕ) : ℝ) * ((E - C : ℕ) : ℝ)) *
        sourceOriginalQActualHQ 20 d L *
        sourceLiteralHP (sourceOriginalPAllActualBands 20 L) *
        (sourceNaturalEuler ⌊W⌋₊) ^ 2 *
        sourceNaturalEuler ⌊Real.exp (parityOriginalAssignmentTheta434 * L)⌋₊ := by
  unfold parityOriginalNormalizedBoxMainBound434 boxMainConstant
  ring

/-- The entire normalized main term is bounded on the
Xrho*V(W)^2 scale, uniformly in W and both source signs. -/
theorem box_main_Xrho_eventually
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t)
    (Carea : ℝ) (hCarea : 0 < Carea) :
    ∃ Cmain : ℝ, 0 < Cmain ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (flag : Bool) (W : ℝ) (A B C E : ℕ),
      (((B - A : ℕ) : ℝ) * ((E - C : ℕ) : ℝ)) ≤ Carea * Real.exp L →
      parityOriginalNormalizedBoxMainBound434
        (sourceOriginalLiteralDepth 20 L) L W A B C E ≤
      Cmain * localizedMass Psi (parityOriginalParitySign434 flag) L *
        (sourceNaturalEuler ⌊W⌋₊) ^ 2 := by
  obtain ⟨c0, hc0, hmass⟩ :=
    box_strong_mass_shared Psi hCont hSupport hNonneg hInterior
  obtain ⟨lo, hi, hlo, hhi, hEuler⟩ := box_euler_bounds
    parityOriginalAssignmentTheta434 (by norm_num [parityOriginalAssignmentTheta434])
  let K := boxMainConstant
  have hK : 0 < K := box_main_constant_pos
  let Cmain := K * Carea * hi / c0
  have hCmain : 0 < Cmain := by dsimp [Cmain]; positivity
  refine ⟨Cmain, hCmain, ?_⟩
  filter_upwards [hmass, hEuler] with L hm he
  intro flag W A B C E harea
  let area : ℝ := ((B - A : ℕ) : ℝ) * ((E - C : ℕ) : ℝ)
  let HQ := sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L
  let HP := sourceLiteralHP (sourceOriginalPAllActualBands 20 L)
  let V := sourceNaturalEuler ⌊W⌋₊
  let Ez := sourceNaturalEuler ⌊Real.exp (parityOriginalAssignmentTheta434 * L)⌋₊
  have hQ : 0 ≤ HQ := box_HQ_nonneg _ _ _
  have hP : 0 ≤ HP := le_trans (by norm_num) hm.2.1
  have hV : 0 ≤ V ^ 2 := sq_nonneg _
  have hz : 0 ≤ Ez := box_euler_nonneg _
  have hlocal : K * area * Ez ≤ K * (Carea * Real.exp L) * (hi / L) :=
    mul_le_mul (mul_le_mul_of_nonneg_left harea hK.le) he.2.1 hz
      (mul_nonneg hK.le (mul_nonneg hCarea.le (Real.exp_pos _).le))
  have hscalar : K * (Carea * Real.exp L) * (hi / L) =
      Cmain * (c0 * (Real.exp L / L)) := by
    dsimp [Cmain]
    field_simp [ne_of_gt hc0]
  have hmain : K * area * Ez ≤ Cmain * (c0 * (Real.exp L / L)) := by
    rw [← hscalar]
    exact hlocal
  have hmul := mul_le_mul_of_nonneg_right hmain
    (mul_nonneg (mul_nonneg hQ hP) hV)
  rw [box_main_exact]
  calc
    _ = (K * area * Ez) * (HQ * HP * V ^ 2) := by dsimp [K, area, Ez, HQ, HP, V]; ring
    _ ≤ (Cmain * (c0 * (Real.exp L / L))) * (HQ * HP * V ^ 2) := hmul
    _ = Cmain * (c0 * (Real.exp L / L) * (HQ * HP)) * V ^ 2 := by ring
    _ ≤ Cmain * localizedMass Psi (parityOriginalParitySign434 flag) L * V ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hm.2.2 flag) hCmain.le) hV

/-- A positive uniform denominator for the source error:
no cancellation of H_Q and no assumed lower bound for Xrho. -/
theorem box_denominator_lower_eventually
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∃ cden : ℝ, 0 < cden ∧ ∀ᶠ L : ℝ in atTop,
      0 < L ∧ ∀ (flag : Bool) (W : ℝ),
      W ≤ Real.exp (parityOriginalAssignmentTheta434 * L) →
      cden * Real.exp L / L ^ 3 *
        sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L ≤
      localizedMass Psi (parityOriginalParitySign434 flag) L *
        (sourceNaturalEuler ⌊W⌋₊) ^ 2 := by
  obtain ⟨c0, hc0, hmass⟩ :=
    box_strong_mass_shared Psi hCont hSupport hNonneg hInterior
  obtain ⟨lo, hi, hlo, hhi, hEuler⟩ := box_euler_bounds
    parityOriginalAssignmentTheta434 (by norm_num [parityOriginalAssignmentTheta434])
  refine ⟨c0 * lo ^ 2, by positivity, ?_⟩
  filter_upwards [hmass, hEuler] with L hm he
  refine ⟨hm.1, ?_⟩
  intro flag W hW
  have hL : 0 < L := hm.1
  let HQ := sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L
  let HP := sourceLiteralHP (sourceOriginalPAllActualBands 20 L)
  let X := localizedMass Psi (parityOriginalParitySign434 flag) L
  let V := sourceNaturalEuler ⌊W⌋₊
  have hQ : 0 ≤ HQ := box_HQ_nonneg _ _ _
  have hscale : 0 ≤ c0 * (Real.exp L / L) := by positivity
  have hraw : c0 * (Real.exp L / L) * HQ ≤ X := by
    calc
      _ ≤ c0 * (Real.exp L / L) * (HQ * HP) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hm.2.1 hQ) hscale
      _ ≤ X := hm.2.2 flag
  have hX : 0 ≤ X := (mul_nonneg hscale hQ).trans hraw
  have hv : lo / L ≤ V := he.2.2 W hW
  have hsq : (lo / L) ^ 2 ≤ V ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hlo.le hm.1.le) hv 2
  have hprod := mul_le_mul hraw hsq (sq_nonneg (lo / L)) hX
  calc
    _ = (c0 * (Real.exp L / L) * HQ) * (lo / L) ^ 2 := by
      dsimp [HQ]
      field_simp [ne_of_gt hL]
 <;> ring
    _ ≤ X * V ^ 2 := hprod

end Green64Analytic.Parity

end
