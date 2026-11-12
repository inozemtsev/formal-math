module

public import Green64.Library.Correlation.Part032
public import Green64.Library.Weights.SourceShiftTwoPNTBandFloors

@[expose] public section

/-!
# Correlation / SourcePhysicalUniformGroupMass

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourcePhysicalUniformGroupMass -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve

/-- Positive fixed floor on the original CLOSED P band, derived from native PNT2. -/
theorem source_closed_P_band_mass_floor :
    ∀ᶠ t : ℝ in atTop,
      Real.log (6/5:ℝ)/2 ≤ ∑ p ∈ sourceOriginalClosedPGroup t, (p:ℝ)⁻¹ := by
  have hband := source_prime_log_band_floor_unconditional 1 (6/5) 1 (6/5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hband,eventually_ge_atTop (0:ℝ)] with t ht ht0
  apply ht.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (source_original_P_short_band_subset t 1 (6/5) ht0
      (by norm_num) (by norm_num) (by norm_num))
  intro p hp hp'
  exact inv_nonneg.mpr (Nat.cast_nonneg p)

/-- Uniform lower AND upper masses in ALL original moving source P groups.
There is no new prime-band/PNT hypothesis. -/
theorem source_actual_P_uniform_mass_bounds (r : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ g : sourceOriginalPAllGroupType r L,
        Real.log (6/5:ℝ)/2 ≤
          ∑ p ∈ sourceOriginalPAllActualBands r L g, (p:ℝ)⁻¹ ∧
        (∑ p ∈ sourceOriginalPAllActualBands r L g, (p:ℝ)⁻¹) ≤ 4 := by
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp source_closed_P_band_mass_floor
  have hpow : Tendsto (fun L : ℝ => L^(1/10:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hlarge := hpow.eventually (eventually_ge_atTop T)
  filter_upwards [hlarge,eventually_ge_atTop (1:ℝ),
    source_original_P_all_actual_reciprocal_le_four434 r] with L hlarge hL hlocal
  intro g
  constructor
  · apply hT
    exact hlarge.trans (source_original_P_all_actual_band_lower r L hL g)
  · exact hlocal g

theorem source_actual_P_uniform_mass_floor_positive :
    0 < Real.log (6/5:ℝ)/2 := by
  have h := Real.log_pos (by norm_num : (1:ℝ)<6/5)
  linarith

end Green64Analytic.ShiftTwoTerminal

end

