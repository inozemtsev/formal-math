module

public import Green64.Library.Correlation.SourcePhysicalUniformGroupMass
public import Green64.Library.Correlation.Part032

@[expose] public section

/-!
# Weights / OriginalGroupMasses

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceNativeOriginalGroupMasses -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The genuine reciprocal-prime mass of the minimum original SMALL band. -/
def sourceNativeOriginalVs434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) : ℝ :=
  ∑ p ∈ sourceNativeOriginalS434 r L hS, (p : ℝ)⁻¹

/-- The genuine reciprocal-prime mass of every remaining original SMALL band. -/
def sourceNativeOriginalVsmall434 (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (i : sourceNativeOriginalTsType434 r L hS) : ℝ :=
  ∑ p ∈ sourceNativeOriginalTs434 r L hS i, (p : ℝ)⁻¹

/-- The genuine reciprocal-prime mass of every original BIG band, indexed
independently of SMALL. -/
def sourceNativeOriginalVbig434 (r : ℕ) (L : ℝ)
    (g : sourceNativeOriginalBigType434 r L) : ℝ :=
  ∑ p ∈ sourceNativeOriginalTb434 r L g, (p : ℝ)⁻¹

private theorem reciprocal_band_nonempty_of_floor434 (P : Finset ℕ)
    (hP : Real.log (6/5:ℝ)/2 ≤ ∑ p ∈ P, (p : ℝ)⁻¹) : P.Nonempty := by
  by_contra hEmpty
  have hEq : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
  have hPositive := ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
  simp only [hEq, Finset.sum_empty] at hP
  linarith

/-- One threshold, depending only on the fixed original r, supplies the true
S/Ts/Tb reciprocal-mass fields and actual prime-band nonemptiness. All groups
are the certified literal full original family; no later comparison parameter
or analytic hypothesis occurs in this statement. -/
theorem eventually_source_native_original_group_masses434
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ L : ℝ in atTop,
      1 < L ∧ (sourceNativeOriginalSmallIndices434 r L).Nonempty ∧
      ∀ hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty,
        (Real.log (6/5:ℝ)/2 ≤ sourceNativeOriginalVs434 r L hS ∧
          sourceNativeOriginalVs434 r L hS ≤ 4 ∧
          (sourceNativeOriginalS434 r L hS).Nonempty) ∧
        (∀ i : sourceNativeOriginalTsType434 r L hS,
          Real.log (6/5:ℝ)/2 ≤ sourceNativeOriginalVsmall434 r L hS i ∧
          sourceNativeOriginalVsmall434 r L hS i ≤ 4 ∧
          (sourceNativeOriginalTs434 r L hS i).Nonempty) ∧
        (∀ g : sourceNativeOriginalBigType434 r L,
          Real.log (6/5:ℝ)/2 ≤ sourceNativeOriginalVbig434 r L g ∧
          sourceNativeOriginalVbig434 r L g ≤ 4 ∧
          (sourceNativeOriginalTb434 r L g).Nonempty) := by
  filter_upwards [ShiftTwoTerminal.source_actual_P_uniform_mass_bounds r,
    eventually_source_native_original_small_counts434 r hr] with L hMass hSmall
  refine ⟨hSmall.1, hSmall.2.1, ?_⟩
  intro hS
  have hSBounds := hMass (sourceNativeOriginalSGroup434 r L hS)
  refine ⟨⟨hSBounds.1, hSBounds.2, ?_⟩, ?_, ?_⟩
  · exact reciprocal_band_nonempty_of_floor434 _ hSBounds.1
  · intro i
    have hi := hMass (sourceNativeOriginalTsGroup434 r L hS i)
    exact ⟨hi.1, hi.2, reciprocal_band_nonempty_of_floor434 _ hi.1⟩
  · intro g
    have hg := hMass (sourceNativeOriginalBigToAll434 r L g)
    exact ⟨hg.1, hg.2, reciprocal_band_nonempty_of_floor434 _ hg.1⟩
end Green64Analytic.SourceBlockSieve

end

end

