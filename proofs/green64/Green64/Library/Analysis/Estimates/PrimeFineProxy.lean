module

public import Green64.Library.Analysis.Estimates.Part005

@[expose] public section

/-!
# Analysis / Estimates / PrimeFineProxy

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualPrimeFineProxy -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The literal prime test is normalized on the full logarithmic cell. -/
def b627PrimeFullProxy434 (mesh W : ℝ) (n : ℕ) : ℝ :=
  let C := sourceD20LogCell mesh (sourceD20CellIndex mesh n)
  if sourceD20Rough W n then
    ((C.filter Nat.Prime).card : ℝ) / ((C.filter (sourceD20Rough W)).card : ℝ)
  else 0

def b627PrimeFullDelta434 (mesh W : ℝ) (n : ℕ) : ℝ :=
  (if n.Prime then 1 else 0) - b627PrimeFullProxy434 mesh W n

private theorem b627_prime_test_iff_rough
    (y : ℝ) (n : ℕ) (hy : 0 ≤ y) (hn : 2 ≤ n)
    (hlo : y < (n : ℝ)) (hhi : (n : ℝ) ≤ y ^ 2) :
    sourceD20Rough y n ↔ n.Prime := by
  constructor
  · intro hr
    by_contra hnp
    have hs : (n.minFac : ℝ) ^ 2 ≤ (n : ℝ) := by
      exact_mod_cast Nat.minFac_sq_le_self (by omega : 0 < n) hnp
    have hmin := hr.2
    nlinarith
  · intro hp
    exact ⟨hn, by simpa only [hp.minFac_eq] using hlo⟩

/-- Entire cells meeting a positive dyad stay in a prime-only window for
the auxiliary cutoff 2 sqrt(a). This identifies both the numerator and
the full-cell normalizer, including the two cut endpoint cells. -/
theorem b627_prime_full_delta_eq_actual_rough434
    (mesh W : ℝ) (hmesh : 0 < mesh) (hexp : Real.exp mesh ≤ 2)
    (a b n : ℕ) (ha : 16 ≤ a) (hba : b ≤ 2 * a)
    (hn : n ∈ Finset.Icc a b) :
    b627PrimeFullDelta434 mesh W n =
      sourceD20FullDelta mesh W (2 * Real.sqrt (a : ℝ)) n := by
  let C := sourceD20LogCell mesh (sourceD20CellIndex mesh n)
  let Y := Real.exp ((sourceD20CellIndex mesh n : ℝ) * mesh)
  let y := 2 * Real.sqrt (a : ℝ)
  have hn2 : 2 ≤ n := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  have hnC : n ∈ C := sourceD20_index_mem hmesh n hn2
  have hscale :
      Real.exp (((sourceD20CellIndex mesh n : ℝ) + 1) * mesh) =
      Y * Real.exp mesh := by
    dsimp [Y]
    rw [← Real.exp_add]
    congr 1
    ring
  have hnbounds := (sourceD20_mem_cell mesh _ n).mp hnC
  rw [hscale] at hnbounds
  have hY0 : 0 < Y := Real.exp_pos _
  have han : (a : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hna : (n : ℝ) ≤ 2 * (a : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hn).2.trans hba
  have hY2 : (a : ℝ) / 2 ≤ Y := by
    have hh := mul_le_mul_of_nonneg_left hexp hY0.le
    linarith
  have ha16 : (16 : ℝ) ≤ a := by exact_mod_cast ha
  have hs0 := Real.sqrt_nonneg (a : ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg a)
  have hs4 : 4 ≤ Real.sqrt (a : ℝ) := by nlinarith
  have hyhalf : y ≤ (a : ℝ) / 2 := by
    dsimp [y]
    nlinarith
  have hy2 : y ^ 2 = 4 * (a : ℝ) := by
    dsimp [y]
    nlinarith
  have hiff : ∀ m ∈ C, sourceD20Rough y m ↔ m.Prime := by
    intro m hm
    have hm2 := sourceD20_cell_ge_two hmesh hm
    have hmbounds := (sourceD20_mem_cell mesh _ m).mp hm
    rw [hscale] at hmbounds
    have hlo : y < (m : ℝ) := (hyhalf.trans hY2).trans_lt hmbounds.1
    have hhi : (m : ℝ) ≤ y ^ 2 := by
      rw [hy2]
      have hYn : Y ≤ (n : ℝ) := hnbounds.1.le
      have hm2Y : (m : ℝ) ≤ 2 * Y :=
        hmbounds.2.trans (by nlinarith [mul_le_mul_of_nonneg_left hexp hY0.le])
      linarith
    exact b627_prime_test_iff_rough y m (by dsimp [y]; positivity) hm2 hlo hhi
  have hfilter : C.filter Nat.Prime = C.filter (sourceD20Rough y) := by
    ext m
    simp only [Finset.mem_filter]
    exact and_congr_right (fun hm => (hiff m hm).symm)
  have htest : (if n.Prime then (1 : ℝ) else 0) = sourceD19RoughTest y n := by
    have hi := (hiff n hnC).symm
    simp only [sourceD20Rough, hn2, true_and] at hi
    simp only [sourceD19RoughTest, hn2, true_and, hi]
  change (if n.Prime then (1 : ℝ) else 0) -
      (if sourceD20Rough W n then
        ((C.filter Nat.Prime).card : ℝ) / ((C.filter (sourceD20Rough W)).card : ℝ)
      else 0) =
    sourceD19RoughTest y n -
      (if sourceD20Rough W n then
        ((C.filter (sourceD20Rough y)).card : ℝ) /
          ((C.filter (sourceD20Rough W)).card : ℝ)
      else 0)
  rw [hfilter, htest]

/-- Uniformity in the genuine rough cutoff is proved from the actual
principal Mellin estimate and the unconditional nonprincipal SW bound. -/
theorem b627_actual_fine_rough_all_character_saving434
    (B S β : ℝ) (hB : 0 < B) (hS : 2 * B < S) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (a b q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (y t : ℝ),
      2 ≤ a → a ≤ b → b ≤ 2 * a →
      Real.exp (β * L) ≤ (a : ℝ) → (b : ℝ) ≤ Real.exp (2 * L) →
      Real.exp (Real.sqrt L) ≤ y → (q : ℝ) ≤ L ^ B → |t| ≤ L ^ B →
      ‖∑ n ∈ Finset.Icc a b,
        (sourceD20FullDelta (L ^ (-S)) (Real.exp (Real.sqrt L)) y n : ℂ) *
          χ n * sourceD20Mellin t n‖ ≤ L ^ (-B) := by
  filter_upwards [sourceD21_full_nonprincipal_saving B S hB (by linarith),
    sourceD20_mesh_scalar B S β hB hS hβ, sourceD20_log_moduli_below_W B hB,
    eventually_gt_atTop (0 : ℝ)] with L hnon hscalar hmod hL
  intro a b q inst χ y t ha hab hba hsize hb hy hq ht
  by_cases hχ : χ = 1
  · subst χ
    exact (sourceD20_principal_interval_bound
      (Real.rpow_pos_of_pos hL _) hy a b q ha hab hba
      (Nat.pos_of_ne_zero (NeZero.ne q)) (hq.trans hmod) t).trans
      (hscalar a t hsize ht)
  · exact hnon a b q χ y t ha hab hba hb hy hχ hq ht

private theorem b627_actual_prime_window
    (S β : ℝ) (hS : 0 < S) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop, ∀ a : ℕ,
      Real.exp (β * L) ≤ (a : ℝ) →
      16 ≤ a ∧ Real.exp (L ^ (-S)) ≤ 2 ∧
        Real.exp (Real.sqrt L) ≤ 2 * Real.sqrt (a : ℝ) := by
  have hmesh := (tendsto_rpow_neg_atTop hS).eventually_le_const
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hW := Real.tendsto_exp_atTop.eventually
    (source_presieve_real_le_power (β / 2) (by linarith))
  filter_upwards [hmesh, hW, eventually_ge_atTop (16 / β),
    eventually_gt_atTop (0 : ℝ)] with L hm hWy hlarge hL
  intro a hsize
  have hβL : (16 : ℝ) ≤ β * L := by
    have := (div_le_iff₀ hβ).mp hlarge
    nlinarith
  have ha16 : (16 : ℝ) ≤ a := by
    have he := Real.add_one_le_exp (β * L)
    linarith
  refine ⟨by exact_mod_cast ha16, ?_, ?_⟩
  · calc
      Real.exp (L ^ (-S)) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hm
      _ = 2 := Real.exp_log (by norm_num)
  · have hWexp : Real.exp (Real.sqrt L) ≤ Real.exp (β * L / 2) := by
      have hh : Real.exp (Real.sqrt L) ≤ Real.exp (L * (β / 2)) := by
        simpa only [sourcePresieveReal, Real.log_exp, Real.rpow_def_of_pos
          (Real.exp_pos L)] using hWy
      convert hh using 1
      congr 1
      ring
    have he2 : (Real.exp (β * L / 2)) ^ 2 = Real.exp (β * L) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hs2 := Real.sq_sqrt (Nat.cast_nonneg a)
    have hs0 := Real.sqrt_nonneg (a : ℝ)
    have he0 := Real.exp_pos (β * L / 2)
    have heS : Real.exp (β * L / 2) ≤ Real.sqrt (a : ℝ) := by
      nlinarith
    linarith

/-- The literal prime-minus-full-cell-proxy sequence has arbitrary fixed
all-character/Mellin discrepancy. No candidate weight or shift is used. -/
theorem b627_actual_prime_fine_all_character_saving434
    (B S β : ℝ) (hB : 0 < B) (hS : 2 * B < S) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (a b q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      2 ≤ a → a ≤ b → b ≤ 2 * a →
      Real.exp (β * L) ≤ (a : ℝ) → (b : ℝ) ≤ Real.exp (2 * L) →
      (q : ℝ) ≤ L ^ B → |t| ≤ L ^ B →
      ‖∑ n ∈ Finset.Icc a b,
        (b627PrimeFullDelta434 (L ^ (-S)) (Real.exp (Real.sqrt L)) n : ℂ) *
          χ n * sourceD20Mellin t n‖ ≤ L ^ (-B) := by
  filter_upwards [b627_actual_fine_rough_all_character_saving434 B S β hB hS hβ,
    b627_actual_prime_window S β (by linarith) hβ,
    eventually_gt_atTop (0 : ℝ)] with L hrough hwindow hL
  intro a b q inst χ t ha hab hba hsize hb hq ht
  obtain ⟨ha16, hexp, hWy⟩ := hwindow a hsize
  have he :
      (∑ n ∈ Finset.Icc a b,
        (b627PrimeFullDelta434 (L ^ (-S)) (Real.exp (Real.sqrt L)) n : ℂ) *
          χ n * sourceD20Mellin t n) =
      ∑ n ∈ Finset.Icc a b,
        (sourceD20FullDelta (L ^ (-S)) (Real.exp (Real.sqrt L))
          (2 * Real.sqrt (a : ℝ)) n : ℂ) * χ n * sourceD20Mellin t n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [b627_prime_full_delta_eq_actual_rough434 _ _
      (Real.rpow_pos_of_pos hL _) hexp a b n ha16 hba hn]
  rw [he]
  exact hrough a b q χ _ t ha hab hba hsize hb hWy hq ht

/-- The final source test interval and the actual dyadic interval are both
retained. Their intersection is applied after full-cell normalization. -/
theorem b627_actual_prime_restricted_all_character_saving434
    (B S β : ℝ) (hB : 0 < B) (hS : 2 * B < S) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (l u a b q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
      2 ≤ l → u ≤ 2 * l →
      Real.exp (β * L) ≤ (l : ℝ) → (u : ℝ) ≤ Real.exp (2 * L) →
      (q : ℝ) ≤ L ^ B → |t| ≤ L ^ B →
      ‖∑ n ∈ Finset.Icc a b,
        (if n ∈ Finset.Icc l u then
          (b627PrimeFullDelta434 (L ^ (-S)) (Real.exp (Real.sqrt L)) n : ℂ)
         else 0) * χ n * sourceD20Mellin t n‖ ≤ L ^ (-B) := by
  filter_upwards [b627_actual_prime_fine_all_character_saving434 B S β hB hS hβ,
    eventually_gt_atTop (0 : ℝ)] with L hs hL
  intro l u a b q inst χ t hl hu hsize hub hq ht
  let f := fun n => (b627PrimeFullDelta434 (L ^ (-S))
    (Real.exp (Real.sqrt L)) n : ℂ) * χ n * sourceD20Mellin t n
  have he :
      (∑ n ∈ Finset.Icc a b,
        (if n ∈ Finset.Icc l u then
          (b627PrimeFullDelta434 (L ^ (-S)) (Real.exp (Real.sqrt L)) n : ℂ)
         else 0) * χ n * sourceD20Mellin t n) =
      ∑ n ∈ Finset.Icc (max l a) (min u b), f n := by
    simp only [ite_mul, zero_mul, ← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff, le_min_iff]
    tauto
  rw [he]
  by_cases hab : max l a ≤ min u b
  · exact hs (max l a) (min u b) q χ t (hl.trans (le_max_left _ _)) hab
      (by omega) (hsize.trans (Nat.cast_le.mpr (le_max_left _ _)))
      ((Nat.cast_le.mpr (min_le_left _ _)).trans hub) hq ht
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hab), Finset.sum_empty, norm_zero]
    exact Real.rpow_nonneg hL.le _

/-- The source coefficient bound and rough support are independent of the
fine precision. They follow for the actual prime proxy, not an abstract test. -/
theorem b627_actual_prime_fine_coefficient_bound434
    (S β : ℝ) (hS : 0 < S) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ,
      Real.exp (β * L) ≤ (n : ℝ) →
      |b627PrimeFullDelta434 (L ^ (-S)) (Real.exp (Real.sqrt L)) n| ≤ 1 ∧
      (¬ sourceD20Rough (Real.exp (Real.sqrt L)) n →
        b627PrimeFullDelta434 (L ^ (-S)) (Real.exp (Real.sqrt L)) n = 0) := by
  filter_upwards [b627_actual_prime_window S β hS hβ,
    eventually_gt_atTop (0 : ℝ)] with L hwindow hL
  intro n hn
  obtain ⟨hn16, hexp, hWy⟩ := hwindow n hn
  rw [b627_prime_full_delta_eq_actual_rough434 _ _
    (Real.rpow_pos_of_pos hL _) hexp n n n hn16 (by omega) (by simp)]
  exact ⟨sourceD20_delta_bound _ hWy n,
    fun hnot => sourceD20_delta_support _ hWy n hnot⟩
end Green64Analytic.SourceBlockSieve

end

end

