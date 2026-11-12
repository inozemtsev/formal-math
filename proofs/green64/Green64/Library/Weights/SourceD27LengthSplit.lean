module

public import Green64.Library.Weights.Part036

@[expose] public section

/-!
# Weights / SourceD27LengthSplit

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceD27LengthSplit -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

theorem sourceD27_empty_tuple_cell (Y Δ y : ℝ) (hY : 1≤Y) :
    sourceD24OrderedCellTuples 0 Y Δ y = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨l,hl⟩
  obtain ⟨hall,hprodY⟩ := Finset.mem_filter.mp hl
  have hlen := (Green64Analytic.OrderedPrimeRough.mem_allPrimeTuples_iff
    0 y (Real.exp Δ*Y) (mul_nonneg (Real.exp_pos _).le
      (by linarith : 0≤Y)) l).mp hall |>.1
  have hl0 : l=[] := List.length_eq_zero_iff.mp hlen
  simp only [hl0,List.prod_nil,Nat.cast_one] at hprodY
  linarith

private lemma sum_shift_two (f : ℕ → ℝ) (K : ℕ) :
    (∑ ell ∈ Finset.range (K+2), f ell) =
      f 0 + f 1 + ∑ n ∈ Finset.range K, f (n+2) := by
  induction K with
  | zero =>
      simp only [Nat.zero_add,Finset.sum_range_succ,Finset.sum_range_zero,
        add_zero]
      ring
  | succ K ih =>
      rw [show K+1+2=(K+2)+1 by omega,Finset.sum_range_succ,
        ih,Finset.sum_range_succ]
      ring

theorem sourceD27_length_sum_split (K : ℕ) (Y Δ y : ℝ)
    (hY : 1≤Y) :
    (∑ ell∈Finset.range (K+2),
      ((sourceD24OrderedCellTuples ell Y Δ y).card:ℝ)/
        (ell.factorial:ℝ)) =
    ((sourceD24OrderedCellTuples 1 Y Δ y).card:ℝ) +
      ∑ n∈Finset.range K,
        ((sourceD24OrderedCellTuples (n+2) Y Δ y).card:ℝ)/
          ((n+2).factorial:ℝ) := by
  let f : ℕ → ℝ := fun ell =>
    ((sourceD24OrderedCellTuples ell Y Δ y).card:ℝ)/(ell.factorial:ℝ)
  have hz : f 0=0 := by
    simp [f,sourceD27_empty_tuple_cell Y Δ y hY]
  simpa only [f,hz,zero_add,Nat.factorial_one, Nat.cast_one,div_one] using
    (sum_shift_two f K)



end Green64Analytic.SourceBlockSieve

end

