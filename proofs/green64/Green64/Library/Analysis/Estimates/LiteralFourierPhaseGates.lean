module

public import Green64.Library.Weights.LiteralEndpointProfiles

@[expose] public section

/-!
# Analysis / Estimates / LiteralFourierPhaseGates

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## LiteralFourierPhaseGates -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

private theorem source_B578_two_phase434 (L : ℝ) (n : ℕ) (hL : 4 ≤ L)
    (p q : ℝ) (hp : |p| ≤ L^n) (hq : |q| ≤ L^n) :
    |2*Real.pi*p+2*Real.pi*q| ≤ L^(n+2) := by
  have hLp : 0 ≤ L := by linarith
  have hn : 0 ≤ L^n := pow_nonneg hLp _
  have hc : 0 ≤ 2*Real.pi := by positivity
  have h2 : (16:ℝ) ≤ L^2 := by nlinarith
  calc
    _ ≤ |2*Real.pi*p|+|2*Real.pi*q| := abs_add_le _ _
    _ = 2*Real.pi*(|p|+|q|) := by simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),abs_of_pos Real.pi_pos]; ring
    _ ≤ 2*Real.pi*(2*L^n) := mul_le_mul_of_nonneg_left (by linarith) hc
    _ ≤ 16*L^n := by nlinarith [Real.pi_lt_four]
    _ ≤ L^n*L^2 := by nlinarith [mul_nonneg hn (sub_nonneg.mpr h2)]
    _ = _ := by rw [pow_add]

private theorem source_B578_three_phase434 (L : ℝ) (n : ℕ) (hL : 4 ≤ L)
    (p q r : ℝ) (hp : |p| ≤ L^n) (hq : |q| ≤ L^n) (hr : |r| ≤ L^n) :
    |2*Real.pi*p+2*Real.pi*q+2*Real.pi*r| ≤ L^(n+3) := by
  have hLp : 0 ≤ L := by linarith
  have hn : 0 ≤ L^n := pow_nonneg hLp _
  have hc : 0 ≤ 2*Real.pi := by positivity
  have h3 : (24:ℝ) ≤ L^3 := by
    calc
      _ ≤ (4:ℝ)^3 := by norm_num
      _ ≤ L^3 := by gcongr
  calc
    _ ≤ |2*Real.pi*p|+|2*Real.pi*q|+|2*Real.pi*r| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ = 2*Real.pi*(|p|+|q|+|r|) := by simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),abs_of_pos Real.pi_pos]; ring
    _ ≤ 2*Real.pi*(3*L^n) := mul_le_mul_of_nonneg_left (by linarith) hc
    _ ≤ 24*L^n := by nlinarith [Real.pi_lt_four]
    _ ≤ L^n*L^3 := by nlinarith [mul_nonneg hn (sub_nonneg.mpr h3)]
    _ = _ := by rw [pow_add]

/-- Actual original Fourier phases, with 2*pi in every place and the
negative reciprocal first endpoint.  The graph phase cancels the outer
rho EXACTLY, so its exponent depends only on the inner box and cutoff 3.
The original frequency cutoffs are not enlarged after J. -/
theorem source_B578_literal_native_phase_boxes434
    (L : ℝ) (nout nin : ℕ) (rho : ℝ) (zeta : Fin 3 → ℝ) (t : ℝ)
    (hL : 4 ≤ L) (hrho : |rho| ≤ L^nout)
    (hzeta : ∀i,|zeta i| ≤ L^nin) (ht : |t| ≤ L^3) :
    |2*Real.pi*rho-2*Real.pi*zeta 1| ≤ L^(max nout nin+2) ∧
    |2*Real.pi*zeta 0+2*Real.pi*rho| ≤ L^(max nout nin+2) ∧
    |-(2*Real.pi*rho+2*Real.pi*zeta 2+2*Real.pi*t)| ≤
      L^(max (max nout nin) 3+3) ∧
    |-2*Real.pi*rho| ≤ L^(max (max nout nin) 3+3) ∧
    |-( (2*Real.pi*rho+2*Real.pi*zeta 2)+(-2*Real.pi*rho)+2*Real.pi*t)| ≤
      L^(max nin 3+2) := by
  have hL1 : 1 ≤ L := by linarith
  have hp : ∀a b : ℕ,a ≤ b → L^a ≤ L^b :=
    fun a b hab=>pow_le_pow_right₀ hL1 hab
  have hr0 := hrho.trans (hp nout (max nout nin) (le_max_left _ _))
  have hz0 := fun i=>(hzeta i).trans (hp nin (max nout nin) (le_max_right _ _))
  have hr1 := hr0.trans (hp (max nout nin) (max (max nout nin) 3) (le_max_left _ _))
  have hz1 := (hz0 2).trans (hp (max nout nin) (max (max nout nin) 3) (le_max_left _ _))
  have ht1 := ht.trans (hp 3 (max (max nout nin) 3) (le_max_right _ _))
  have hF : |2*Real.pi*rho-2*Real.pi*zeta 1| ≤ L^(max nout nin+2) := by
    have hnz : |-(zeta 1)| ≤ L^(max nout nin) := by simpa only [abs_neg] using hz0 1
    simpa only [mul_neg,sub_eq_add_neg] using source_B578_two_phase434 L _ hL rho (-(zeta 1)) hr0 hnz
  refine ⟨hF,source_B578_two_phase434 L _ hL _ _ (hz0 0) hr0,?_,?_,?_⟩
  · simpa only [abs_neg] using source_B578_three_phase434 L _ hL _ _ _ hr1 hz1 ht1
  · have h0 : |(0:ℝ)| ≤ L^(max (max nout nin) 3) := by
      simpa only [abs_zero] using pow_nonneg (show (0:ℝ) ≤ L by linarith) (max (max nout nin) 3)
    have hh := source_B578_three_phase434 L _ hL rho 0 0 hr1 h0 h0
    simpa only [mul_zero,add_zero,neg_mul,abs_neg] using hh
  · have hz := (hzeta 2).trans (hp nin (max nin 3) (le_max_left _ _))
    have ht' := ht.trans (hp 3 (max nin 3) (le_max_right _ _))
    have hh := source_B578_two_phase434 L _ hL (zeta 2) t hz ht'
    have he : (2*Real.pi*rho+2*Real.pi*zeta 2)+(-2*Real.pi*rho)+2*Real.pi*t =
        2*Real.pi*zeta 2+2*Real.pi*t := by ring
    rw [he,abs_neg]
    exact hh
end Green64Analytic.CorrelationSquare

end

