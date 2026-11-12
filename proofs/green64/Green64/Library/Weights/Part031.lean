module

public import Green64.Library.Weights.OriginalGroupMasses

@[expose] public section

/-!
# Weights / Part031

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceNativeCorrectedChartDefinitions -/

section

open scoped BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false

theorem source_corrected_dyadic_depth_exists (A : ℝ) (hA : 1 ≤ A) :
    ∃ N : ℕ, 192*A ≤ (2:ℝ)^N ∧ (2:ℝ)^N ≤ 384*A := by
  obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near
    (show (1:ℝ) ≤ 192*A by linarith) (by norm_num : (1:ℝ)<2)
  refine ⟨n+1,hhi.le,?_⟩
  rw [pow_succ]
  linarith

noncomputable def sourceCorrectedDyadicScale (U V M : ℝ) (j : ℕ) : ℝ :=
  ((U*V)*M/8)*(2:ℝ)^j

noncomputable def sourceCorrectedSmoothKSet (M A : ℝ) : Finset ℤ :=
  (Finset.Icc (-(⌊2*M*A⌋₊:ℤ)) (⌊2*M*A⌋₊:ℤ)).filter
    (fun k => k ≠ 0 ∧ Even k)

theorem source_corrected_smooth_shift_abs_le (M A : ℝ) (hMA : 0 ≤ 2*M*A)
    (k : ℤ) (hk : k ∈ sourceCorrectedSmoothKSet M A) :
    k ≠ 0 ∧ Even k ∧ (k.natAbs:ℝ) ≤ 2*M*A := by
  obtain ⟨hbox,hk,hke⟩ := Finset.mem_filter.mp hk
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hbox
  have hn : k.natAbs ≤ ⌊2*M*A⌋₊ := by omega
  refine ⟨hk,hke,?_⟩
  have hn' : (k.natAbs:ℝ) ≤ (⌊2*M*A⌋₊:ℝ) := by exact_mod_cast hn
  exact hn'.trans (Nat.floor_le hMA)

end Green64Analytic.ShiftTwoTerminal

end

/-! ## SourceNativeOriginalChartBounds -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Any genuine atom in an original natural dyadic cell with mn=u+2 gives
the UV comparison used by the moving corrected chart. -/
theorem source_native_original_atom_uv_bounds434
    (X U V : ℝ) (hX : 2 ≤ X) (hU : 0 < U) (hV : 0 < V)
    (u a b : ℕ) (hu : X ≤ (u:ℝ) ∧ (u:ℝ) ≤ 2*X)
    (ha : U ≤ (a:ℝ) ∧ (a:ℝ) ≤ 2*U)
    (hb : V ≤ (b:ℝ) ∧ (b:ℝ) ≤ 2*V) (heq : a*b=u+2) :
    X/4 ≤ U*V ∧ U*V ≤ 3*X := by
  have hEq : (a:ℝ)*(b:ℝ) = (u:ℝ)+2 := by exact_mod_cast heq
  have hlo := mul_le_mul ha.1 hb.1 hV.le (Nat.cast_nonneg a)
  have hhi := mul_le_mul ha.2 hb.2 (Nat.cast_nonneg b) (by positivity : 0 ≤ 2*U)
  constructor <;> nlinarith

/-- Literal native dyads: their polynomial enlargement is uniform in the
actual moving dyadic depth and index. -/
theorem source_native_original_dyad_bounds434
    (L K U V : ℝ) (hL : 0 < L)
    (hUVlo : Real.exp L/4 ≤ U*V) (hUVhi : U*V ≤ 3*Real.exp L)
    (N j : ℕ) (hj : j ≤ N) (hN : (2:ℝ)^N ≤ 384*L^(89:ℝ)) :
    0 < sourceCorrectedDyadicScale U V (L^K) j ∧
    Real.exp L*L^K/32 ≤ sourceCorrectedDyadicScale U V (L^K) j ∧
    sourceCorrectedDyadicScale U V (L^K) j ≤ 144*Real.exp L*L^(K+89) := by
  have hp : 0 < L^K := Real.rpow_pos_of_pos hL _
  have huv : 0 < U*V := (div_pos (Real.exp_pos L) (by norm_num)).trans_le hUVlo
  have hjlo : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have hjhi : (2:ℝ)^j ≤ 384*L^(89:ℝ) := by
    calc
      _ ≤ (2:ℝ)^N := by gcongr <;> norm_num
      _ ≤ _ := hN
  have hbase : 0 < (U*V)*L^K/8 := by positivity
  refine ⟨by unfold sourceCorrectedDyadicScale; positivity, ?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_right hUVlo hp.le
    have h2 := mul_le_mul_of_nonneg_left hjlo hbase.le
    unfold sourceCorrectedDyadicScale
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_right hUVhi hp.le
    have h2 := mul_le_mul_of_nonneg_left hjhi hbase.le
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hL.le (89:ℝ))
    rw [Real.rpow_add hL]
    unfold sourceCorrectedDyadicScale
    nlinarith

/-- Logarithmic form of the same literal dyadic bounds. -/
theorem source_native_original_dyad_log_bounds434
    (L K U V : ℝ) (hL : 0 < L)
    (hUVlo : Real.exp L/4 ≤ U*V) (hUVhi : U*V ≤ 3*Real.exp L)
    (N j : ℕ) (hj : j ≤ N) (hN : (2:ℝ)^N ≤ 384*L^(89:ℝ)) :
    L+K*Real.log L-Real.log 32 ≤ Real.log (sourceCorrectedDyadicScale U V (L^K) j) ∧
    Real.log (sourceCorrectedDyadicScale U V (L^K) j) ≤
      L+(K+89)*Real.log L+Real.log 144 := by
  have hd := source_native_original_dyad_bounds434 L K U V hL hUVlo hUVhi N j hj hN
  have hp : 0 < L^K := Real.rpow_pos_of_pos hL _
  constructor
  · have h := Real.log_le_log (by positivity : 0 < Real.exp L*L^K/32) hd.2.1
    simpa only [Real.log_div (by positivity : Real.exp L*L^K ≠ 0) (by norm_num : (32:ℝ) ≠ 0),
      Real.log_mul (Real.exp_ne_zero L) hp.ne', Real.log_exp, Real.log_rpow hL] using h
  · have h := Real.log_le_log hd.1 hd.2.2
    have hp' : 0 < L^(K+89) := Real.rpow_pos_of_pos hL _
    rw [Real.log_mul (by positivity : 144*Real.exp L ≠ 0) hp'.ne',
      Real.log_mul (by norm_num : (144:ℝ) ≠ 0) (Real.exp_ne_zero L),
      Real.log_exp, Real.log_rpow hL] at h
    linarith
end Green64Analytic.ShiftTwoTerminal

end

end

