module

public import Green64.Sieve.DyadicGeometry

@[expose] public section

/-!
# Count compatible dyadic rectangles

Count compatible binary dyad labels. The product window restricts the
sum of the two labels, while the balance window restricts their difference.
-/

section

set_option maxHeartbeats 2200000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

theorem nat_finset_card_span (T : Finset ℕ) (hT : T.Nonempty) :
    (T.card : ℝ) ≤ (T.max' hT : ℝ) + 1 - (T.min' hT : ℝ) := by
  have hsub : T ⊆ Finset.Icc (T.min' hT) (T.max' hT) := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨T.min'_le k hk, T.le_max' k hk⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have horder : T.min' hT ≤ T.max' hT := T.min'_le _ (T.max'_mem hT)
  have hr : (T.card : ℝ) ≤ ((T.max' hT + 1 - T.min' hT : ℕ) : ℝ) := by
    exact_mod_cast hc
  rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at hr
  exact hr

/-- The number of attained first-factor labels is linear in kappa*L.
The closed source endpoints are retained; no global square is counted. -/
theorem first_dyad_labels_card
    (L kappa : ℝ) (hL : 0 ≤ L) (hkappa : 0 ≤ kappa) (T : Finset ℕ)
    (hT : ∀ k ∈ T,
      Real.exp (((1 / 2 : ℝ) - 2 * kappa) * L) < (2 : ℝ) ^ (k + 1) ∧
      (2 : ℝ) ^ k ≤ Real.exp (((1 / 2 : ℝ) + 2 * kappa) * L)) :
    (T.card : ℝ) ≤ 4 * kappa * L / Real.log 2 + 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hlo := Real.log_lt_log (Real.exp_pos _)
      (hT (T.min' hne) (T.min'_mem hne)).1
    have hhi := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _)
      (hT (T.max' hne) (T.max'_mem hne)).2
    rw [Real.log_exp, Real.log_pow, Nat.cast_add, Nat.cast_one] at hlo
    rw [Real.log_pow, Real.log_exp] at hhi
    have hspan : ((T.max' hne : ℝ) + 1 - (T.min' hne : ℝ) - 2) * Real.log 2 ≤
        4 * kappa * L := by nlinarith
    have hd := (le_div_iff₀ hlog).2 hspan
    have hc := nat_finset_card_span T hne
    linarith

/-- A ratio-sixteen product window allows at most five second-factor
binary labels once the first scale is fixed. -/
theorem compatible_second_labels_card
    (T : Finset ℕ) (U x : ℝ) (hU : 0 < U)
    (hT : ∀ j ∈ T, x / 4 < U * (2 : ℝ) ^ j ∧ U * (2 : ℝ) ^ j ≤ 4 * x) :
    T.card ≤ 5 := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hlo := (hT (T.min' hne) (T.min'_mem hne)).1
    have hhi := (hT (T.max' hne) (T.max'_mem hne)).2
    have hmul : U * (2 : ℝ) ^ (T.max' hne) ≤ U * (16 * (2 : ℝ) ^ (T.min' hne)) := by
      nlinarith
    have hp := (mul_le_mul_iff_right₀ hU).mp hmul
    have he : (2 : ℝ) ^ (T.min' hne + 4) = 16 * (2 : ℝ) ^ (T.min' hne) := by
      rw [pow_add]
      norm_num
      ring
    have hidx : T.max' hne ≤ T.min' hne + 4 :=
      (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hp.trans_eq he.symm)
    have hsub : T ⊆ Finset.Icc (T.min' hne) (T.max' hne) := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨T.min'_le j hj, T.le_max' j hj⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    omega

noncomputable def balancedDyadCountConstant : ℝ :=
  5 * (4 / Real.log 2 + 2)

theorem balanced_dyad_count_constant_pos :
    0 < balancedDyadCountConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold balancedDyadCountConstant
  positivity

/-- Finite compatible pairs, not the Cartesian product of all labels. -/
theorem compatible_dyad_labels_card
    (L kappa : ℝ) (hL : 0 ≤ L) (hkappa : 0 ≤ kappa)
    (S : Finset (ℕ × ℕ))
    (hWindow : ∀ s ∈ S,
      Real.exp L / 4 < (2 : ℝ) ^ s.1 * (2 : ℝ) ^ s.2 ∧
      (2 : ℝ) ^ s.1 * (2 : ℝ) ^ s.2 ≤ 4 * Real.exp L)
    (hFirst : ∀ s ∈ S,
      Real.exp (((1 / 2 : ℝ) - 2 * kappa) * L) < (2 : ℝ) ^ (s.1 + 1) ∧
      (2 : ℝ) ^ s.1 ≤ Real.exp (((1 / 2 : ℝ) + 2 * kappa) * L)) :
    (S.card : ℝ) ≤ balancedDyadCountConstant * (kappa * L + 1) := by
  have hfib : ∀ k ∈ S.image Prod.fst, (S.filter (fun s => s.1 = k)).card ≤ 5 := by
    intro k hk
    let F := S.filter (fun s => s.1 = k)
    let T := F.image Prod.snd
    have hw : ∀ j ∈ T, Real.exp L / 4 < (2 : ℝ) ^ k * (2 : ℝ) ^ j ∧
        (2 : ℝ) ^ k * (2 : ℝ) ^ j ≤ 4 * Real.exp L := by
      intro j hj
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
      have hh := Finset.mem_filter.mp hs
      simpa only [hh.2] using hWindow s hh.1
    have hc := compatible_second_labels_card T
      ((2 : ℝ) ^ k) (Real.exp L) (pow_pos (by norm_num) _) hw
    have heq : T.card = F.card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      apply Prod.ext
      · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
      · exact hab
    rw [heq] at hc
    exact hc
  have hn := Finset.card_le_mul_card_image (f := Prod.fst) S 5 hfib
  have hc : (S.card : ℝ) ≤ 5 * ((S.image Prod.fst).card : ℝ) := by exact_mod_cast hn
  have hf : ∀ k ∈ S.image Prod.fst,
      Real.exp (((1 / 2 : ℝ) - 2 * kappa) * L) < (2 : ℝ) ^ (k + 1) ∧
      (2 : ℝ) ^ k ≤ Real.exp (((1 / 2 : ℝ) + 2 * kappa) * L) := by
    intro k hk
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
    exact hFirst s hs
  have hfirst := first_dyad_labels_card L kappa hL hkappa _ hf
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkl : 0 ≤ kappa * L := mul_nonneg hkappa hL
  calc
    _ ≤ 5 * ((S.image Prod.fst).card : ℝ) := hc
    _ ≤ 5 * (4 * kappa * L / Real.log 2 + 2) := mul_le_mul_of_nonneg_left hfirst (by norm_num)
    _ ≤ balancedDyadCountConstant * (kappa * L + 1) := by
      unfold balancedDyadCountConstant
      have hinv : 0 ≤ 4 / Real.log 2 := div_nonneg (by norm_num) hlog.le
      have he : 4 * kappa * L / Real.log 2 = (4 / Real.log 2) * (kappa * L) := by ring
      rw [he]
      nlinarith

/-- Psi-active balanced source labels have linear cardinality.
All source factors and the product window are discharged. -/
theorem active_balanced_dyads_card
    (L kappa : ℝ) (hL : 0 ≤ L) (hkappa : 0 ≤ kappa)
    (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (K N : Finset ℕ) (Y : ℕ)
    (hK : ∀ m ∈ K, balancedFactor L kappa m)
    (hN : ∀ n ∈ N, balancedFactor L kappa n) :
    ((psiActiveDyadLabels L Psi K N Y).card : ℝ) ≤
      balancedDyadCountConstant * (kappa * L + 1) := by
  apply compatible_dyad_labels_card L kappa hL hkappa
  · intro s hs
    exact active_dyad_product_window L hL Psi hSupport K N Y s hs
  · intro s hs
    exact (active_dyad_balanced_ranges L kappa Psi K N Y hK hN s hs).1

end Green64Analytic.Parity

end
