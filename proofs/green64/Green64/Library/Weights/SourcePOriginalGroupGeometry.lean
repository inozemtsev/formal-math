module

public import Mathlib

@[expose] public section

/-!
# Weights / SourcePOriginalGroupGeometry

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourcePOriginalGroupGeometry -/

section

set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Exactly s_j = s' 2^{-j} L, with s'=1/(r₀ (1+6/5)), from wt:geometry. -/
noncomputable def sourceOriginalPGroupScale (r₀ : ℕ) (L : ℝ) (j : ℕ) : ℝ :=
  L / ((r₀ : ℝ) * (11/5 : ℝ) * (2 : ℝ)^j)

/-- Actual source P-band membership, including BOTH containment endpoints. -/
def sourceOriginalPGroupIndex (r₀ : ℕ) (L : ℝ) (j : ℕ) : Prop :=
  let s := sourceOriginalPGroupScale r₀ L j
  (L^(1/10 : ℝ) ≤ (3/2 : ℝ)*s ∧
   (9/5 : ℝ)*s ≤ L^(1/5 : ℝ)) ∨
  (L^(3/10 : ℝ) ≤ (3/2 : ℝ)*s ∧
   (9/5 : ℝ)*s ≤ L^(2/5 : ℝ))

/-- Exactly the indices j≤j_x selected in original 04-weights.tex. -/
noncomputable def sourceOriginalPGroupIndices (r₀ jₓ : ℕ) (L : ℝ) : Finset ℕ :=
  (Finset.range (jₓ+1)).filter (sourceOriginalPGroupIndex r₀ L)

private theorem source_original_P_group_band_lower
    (r₀ : ℕ) (L : ℝ) (hL : 1 ≤ L) (j : ℕ)
    (hj : sourceOriginalPGroupIndex r₀ L j) :
    1 ≤ (3/2 : ℝ)*sourceOriginalPGroupScale r₀ L j := by
  rcases hj with ⟨ha, _⟩ | ⟨ha, _⟩
  · exact (Real.one_le_rpow hL (by norm_num)).trans ha
  · exact (Real.one_le_rpow hL (by norm_num)).trans ha

/-- Source band containment itself bounds the dyadic index logarithmically. -/
theorem source_original_P_group_index_log_bound
    (r₀ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) (hL : 1 < L)
    (j : ℕ) (hj : sourceOriginalPGroupIndex r₀ L j) :
    (j : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log L := by
  let d : ℝ := (r₀:ℝ) * (11/5 : ℝ)
  let p : ℝ := (2:ℝ)^j
  have hd : 1 ≤ d := by
    dsimp [d]
    have hcast : (1:ℝ) ≤ r₀ := by exact_mod_cast hr₀
    nlinarith
  have hp : 0 < p := pow_pos (by norm_num) _
  have hdp : 0 < d*p := mul_pos (lt_of_lt_of_le (by norm_num) hd) hp
  have hlow := source_original_P_group_band_lower r₀ L (le_of_lt hL) j hj
  have hquot : 1 ≤ ((3/2:ℝ)*L)/(d*p) := by
    convert hlow using 1 <;> simp only [sourceOriginalPGroupScale, d, p]
    ring
  have hcross : d*p ≤ (3/2:ℝ)*L := by
    have h := (le_div_iff₀ hdp).mp hquot
    nlinarith
  have hpdp : p ≤ d*p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (le_of_lt hp)]
  have hpL : p ≤ 2*L := by
    calc
      p ≤ d*p := hpdp
      _ ≤ (3/2:ℝ)*L := hcross
      _ ≤ 2*L := by nlinarith [le_of_lt hL]
  have hlog := Real.log_le_log hp hpL
  have hLne : L ≠ 0 := ne_of_gt (by linarith : 0 < L)
  have h2ne : (2:ℝ) ≠ 0 := by norm_num
  change Real.log ((2:ℝ)^j) ≤ Real.log (2*L) at hlog
  rw [Real.log_pow, Real.log_mul h2ne hLne] at hlog
  exact hlog

/-- Real form of the explicit upper index bound. -/
theorem source_original_P_group_index_le_log
    (r₀ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) (hL : 1 < L)
    (j : ℕ) (hj : sourceOriginalPGroupIndex r₀ L j) :
    (j:ℝ) ≤ 1 + Real.log L / Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hh := source_original_P_group_index_log_bound r₀ L hr₀ hL j hj
  have hh' : (j:ℝ) ≤ (Real.log 2 + Real.log L) / Real.log 2 :=
    (le_div_iff₀ h2).mpr hh
  rw [add_div, div_self (ne_of_gt h2)] at hh'
  exact hh'

end Green64Analytic.SourceBlockSieve

end

