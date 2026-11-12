module

public import Green64.Library.Sieve.Foundations.Part057
public import Green64.Library.Sieve.Foundations.Part055

@[expose] public section

/-!
# Euler product estimates for the sieve cutoff

Collect Euler-product estimates for the finite rectangle sieve. These
bounds control the roughness factor and the normalizing prime-band
products used in the weighted box argument.
-/

section

set_option maxHeartbeats 1200000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

theorem box_euler_nonneg (n : ℕ) :
    0 ≤ sourceNaturalEuler n := by
  unfold sourceNaturalEuler
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by
    exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le
  have hi := inv_anti₀ (show (0 : ℝ) < 1 by norm_num) hp1
  norm_num at hi
  exact sub_nonneg.mpr hi

theorem box_euler_antitone {m n : ℕ} (h : m ≤ n) :
    sourceNaturalEuler n ≤ sourceNaturalEuler m := by
  unfold sourceNaturalEuler
  apply Finset.prod_le_prod_of_subset_of_le_one₀
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.add_le_add_right h 1), hp.2⟩
  · intro p hp
    have hp1 : (1 : ℝ) ≤ p := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le
    have hi := inv_anti₀ (show (0 : ℝ) < 1 by norm_num) hp1
    norm_num at hi
    exact sub_nonneg.mpr hi
  · intro p hp hnot
    exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg p))

/-- The fixed positive-power ordinary Euler limit, with the exact
natural closed cutoff used by the box theorem. -/
theorem box_euler_mertens (theta : ℝ) (hTheta : 0 < theta) :
    Tendsto (fun L : ℝ =>
      L * sourceNaturalEuler ⌊Real.exp (theta * L)⌋₊)
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant) / theta)) := by
  have hM : Tendsto (fun L : ℝ =>
      L * Green64Analytic.SmallB.roughEuler ((Real.exp L) ^ theta))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant) / theta)) := by
    simpa only [Function.comp_def, Real.log_exp] using
      (Green64Analytic.SmallB.real_roughEuler_mertens theta hTheta).comp
        Real.tendsto_exp_atTop
  convert hM using 1
  funext L
  rw [parity_original_rough_euler_natural434, ← Real.exp_mul, mul_comm theta L]

/-- One fixed lower and upper constant works for the moving source
cutoff and the lower bound is uniform over every smaller W. -/
theorem box_euler_bounds (theta : ℝ) (hTheta : 0 < theta) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ᶠ L : ℝ in atTop,
        0 < L ∧
        sourceNaturalEuler ⌊Real.exp (theta * L)⌋₊ ≤ hi / L ∧
        ∀ W : ℝ, W ≤ Real.exp (theta * L) →
          lo / L ≤ sourceNaturalEuler ⌊W⌋₊ := by
  let M := Real.exp (-Real.eulerMascheroniConstant) / theta
  have hMpos : 0 < M := div_pos (Real.exp_pos _) hTheta
  have hM := box_euler_mertens theta hTheta
  have hev : ∀ᶠ L : ℝ in atTop,
      M / 2 < L * sourceNaturalEuler ⌊Real.exp (theta * L)⌋₊ ∧
      L * sourceNaturalEuler ⌊Real.exp (theta * L)⌋₊ < 2 * M :=
    hM.eventually (Ioo_mem_nhds (by dsimp [M]; linarith)
      (by dsimp [M]; linarith))
  refine ⟨M / 2, 2 * M, by positivity, by positivity, ?_⟩
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with L hv hL
  refine ⟨hL, ?_, ?_⟩
  · apply (le_div_iff₀ hL).2
    nlinarith [hv.2]
  · intro W hW
    have hl : (M / 2) / L ≤ sourceNaturalEuler ⌊Real.exp (theta * L)⌋₊ := by
      apply (div_le_iff₀ hL).2
      nlinarith [hv.1]
    exact hl.trans (box_euler_antitone (Nat.floor_mono hW))

/-- The subpower roughness level is eventually in the
uniform fixed-power box range. -/
theorem box_subpower_cutoff_eventually :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ Real.exp (Real.sqrt L) ∧
      Real.exp (Real.sqrt L) ≤ Real.exp (parityOriginalAssignmentTheta434 * L) := by
  have hTheta : 0 < parityOriginalAssignmentTheta434 := by
    norm_num [parityOriginalAssignmentTheta434]
  filter_upwards [parity_original_conditioned_subpower_level434
    parityOriginalAssignmentTheta434 0 1 0 hTheta (by norm_num)] with L h
  refine ⟨h.1, ?_⟩
  simpa only [← Real.exp_mul, mul_comm L parityOriginalAssignmentTheta434] using h.2.1.le

end Green64Analytic.Parity

end
