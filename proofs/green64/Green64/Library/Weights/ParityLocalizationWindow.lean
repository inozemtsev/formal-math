module

public import Green64.Library.Weights.ParityStepCap
public import Green64.Library.Weights.Part004

@[expose] public section

/-!
# Weights / ParityLocalizationWindow

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ParityLocalizationWindow -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Radius of a window containing every actual N=2 ceil(L^.52) prefix. -/
def b651ParityPathRadius434 (J : ℕ) (Ck L : ℝ) : ℕ :=
  Nat.ceil (((2*Nat.ceil (L^(13/25:ℝ)) : ℕ):ℝ)*b651ParityMaxStep434 J Ck L)

/-- The literal number of integers in the symmetric localization window. -/
def b651ParityWindowSize434 (J : ℕ) (Ck L : ℝ) : ℕ :=
  2*b651ParityPathRadius434 J Ck L+1

theorem b651_parity_window_card434 (J : ℕ) (Ck L : ℝ) (n : ℤ) :
    (Finset.Icc (n-(b651ParityPathRadius434 J Ck L:ℤ))
      (n+(b651ParityPathRadius434 J Ck L:ℤ))).card = b651ParityWindowSize434 J Ck L := by
  rw [Int.card_Icc]
  unfold b651ParityWindowSize434
  omega

/-- Every actual signed prefix, all original marks and auxiliary draws,
lies in the same finite enlarged integer window around its starting point. -/
theorem b651_actual_parity_prefix_mem_window434 (J m : ℕ) (Ck L : ℝ)
    (hL : Real.exp 1 ≤ L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (ω : B643AllPrimePath434
      (SourceNativeMemorySP434 20 L hS) (SourceNativeMemoryBP434 20 L) J 1 m patterns
      (2*Nat.ceil (L^(13/25:ℝ))))
    (k : ℤ) (hk : (k.natAbs : ℝ) ≤ L^Ck) (n : ℤ) (t : ℕ) :
    n+b643AllPrimeOffset434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns ω (2*k) t ∈
    Finset.Icc (n-(b651ParityPathRadius434 J Ck L:ℤ))
      (n+(b651ParityPathRadius434 J Ck L:ℤ)) := by
  let off := b643AllPrimeOffset434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns ω (2*k) t
  have hpre := b651_actual_parity_prefix_cap434 J m Ck L hL hS patterns ω k hk t
  have hr : |(off:ℝ)| ≤ (b651ParityPathRadius434 J Ck L:ℝ) :=
    hpre.trans (Nat.le_ceil _)
  have hi : |off| ≤ (b651ParityPathRadius434 J Ck L:ℤ) := by exact_mod_cast hr
  have hh := abs_le.mp hi
  change n+off ∈ _
  apply Finset.mem_Icc.mpr
  constructor <;> omega

/-- The localization radius covers the numerical maximum graph step,
and its exact cardinality H also dominates that radius. -/
theorem b651_parity_maxstep_window_bounds434 (J : ℕ) (Ck L : ℝ) (hL : 1 ≤ L) :
    b651ParityMaxStep434 J Ck L ≤ (b651ParityPathRadius434 J Ck L:ℝ) ∧
      (b651ParityPathRadius434 J Ck L:ℝ) ≤ (b651ParityWindowSize434 J Ck L:ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hstep : 0 ≤ b651ParityMaxStep434 J Ck L := by
    unfold b651ParityMaxStep434
    positivity
  have hN : (1:ℝ) ≤ ((2*Nat.ceil (L^(13/25:ℝ)):ℕ):ℝ) := by
    exact_mod_cast (b638_moment_and_order434 L hL).1
  constructor
  · apply le_trans _ (Nat.le_ceil _)
    have hh := mul_le_mul_of_nonneg_right hN hstep
    simpa only [one_mul] using hh
  · unfold b651ParityWindowSize434
    push_cast
    have hr : (0:ℝ) ≤ b651ParityPathRadius434 J Ck L := Nat.cast_nonneg _
    linarith

/-- The exact rounded window size, including its +1 endpoint, has a
uniform polynomial-times-exponential bound. Constants precede all paths. -/
theorem b651_parity_window_polynomial_bound434 (J : ℕ) (Ck : ℝ) (hCk : 0 ≤ Ck)
    (L : ℝ) (hL : 1 ≤ L) :
    (b651ParityWindowSize434 J Ck L:ℝ) ≤
      19*L^(Ck+13/25)*Real.exp (b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hCJ : 0 ≤ b651ParityDConstant434 J := (b651_parity_D_constant_pos434 J).le
  let N := 2*Nat.ceil (L^(13/25:ℝ))
  let E := Real.exp (b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ))
  let W := L^(Ck+13/25)*E
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hW1 : 1 ≤ W :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hL (by linarith)) hE1
  have hN : (N:ℝ) ≤ 4*L^(13/25:ℝ) := (b638_moment_and_order434 L hL).2.1
  have hstep0 : 0 ≤ b651ParityMaxStep434 J Ck L := by
    unfold b651ParityMaxStep434
    positivity
  have harg : (N:ℝ)*b651ParityMaxStep434 J Ck L ≤ 8*W := by
    calc
      _ ≤ (4*L^(13/25:ℝ))*(2*L^Ck*E) :=
        mul_le_mul_of_nonneg_right hN hstep0
      _ = 8*(L^(13/25:ℝ)*L^Ck)*E := by ring
      _ = _ := by
        rw [←Real.rpow_add hLp]
        have he : (13/25:ℝ)+Ck = Ck+13/25 := by ring
        rw [he]
        dsimp [W]
        ring
  have hceil := (Nat.ceil_lt_add_one
    (mul_nonneg (Nat.cast_nonneg N : (0:ℝ)≤N) hstep0)).le
  have hH : (b651ParityWindowSize434 J Ck L:ℝ) ≤
      2*((N:ℝ)*b651ParityMaxStep434 J Ck L)+3 := by
    dsimp [b651ParityWindowSize434,b651ParityPathRadius434,N]
    push_cast
    dsimp [N] at hceil
    push_cast at hceil
    nlinarith only [hceil]
  dsimp [W,E] at harg hW1
  nlinarith only [hH,harg,hW1]

/-- A genuine subexponential localization window, derived from the
actual maximum D and original moment exponent .52. -/
theorem b651_eventually_parity_window_sqrt434 (J : ℕ) (Ck : ℝ) (hCk : 0 ≤ Ck) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      (b651ParityWindowSize434 J Ck L:ℝ) ≤ Real.exp (Real.sqrt L) := by
  filter_upwards [
    b638_eventually_log_power434 (b651ParityDConstant434 J) (2/5) (9/20)
      (b651_parity_D_constant_pos434 J).le (by norm_num),
    b638_eventually_poly_exp434 19 (Ck+13/25) (9/20) (by norm_num) (by norm_num),
    b638_eventually_const_power434 2 (9/20) (1/2) (by norm_num),
    eventually_ge_atTop (Real.exp 1)] with L hD hpoly hscale hLarge
  have hL : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLarge
  have hD' : b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ) ≤ L^(9/20:ℝ) := by
    nlinarith only [hD]
  refine ⟨hLarge,?_⟩
  calc
    _ ≤ 19*L^(Ck+13/25)*Real.exp (b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ)) :=
      b651_parity_window_polynomial_bound434 J Ck hCk L hL
    _ ≤ Real.exp (L^(9/20:ℝ))*Real.exp (L^(9/20:ℝ)) :=
      mul_le_mul hpoly (Real.exp_le_exp.mpr hD') (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (2*L^(9/20:ℝ)) := by rw [←Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      simpa only [Real.sqrt_eq_rpow] using hscale

/-- The full localization normalization is O(1) at the original R.
Its window H is the proved actual finite window, never the long CRT interval. -/
theorem b651_eventually_parity_localization_factor434
    (J : ℕ) (Ck Csup : ℝ) (hCk : 0 ≤ Ck) (hCsup : 0 ≤ Csup) :
    ∀ᶠ L : ℝ in atTop,
      ((b651ParityWindowSize434 J Ck L:ℝ)*Real.exp (2*Csup*Real.sqrt L))^
        (1/(2*(Nat.ceil (L^(13/25:ℝ)):ℝ))) ≤ Real.exp (1+2*Csup) := by
  filter_upwards [b651_eventually_parity_window_sqrt434 J Ck hCk] with L h
  have hL : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans h.1
  let R := Nat.ceil (L^(13/25:ℝ))
  have hR1 : (1:ℝ) ≤ R := (Real.one_le_rpow hL (by norm_num : (0:ℝ)≤13/25)).trans
    (Nat.le_ceil _)
  have hRp : 0 < (R:ℝ) := lt_of_lt_of_le (by norm_num) hR1
  have hden : 0 < 2*(R:ℝ) := by positivity
  have hpow : 0 ≤ 1/(2*(R:ℝ)) := (one_div_pos.mpr hden).le
  have hR : Real.sqrt L ≤ (R:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1/2:ℝ)≤13/25)).trans
      (Nat.le_ceil _)
  have hprod : (b651ParityWindowSize434 J Ck L:ℝ)*Real.exp (2*Csup*Real.sqrt L) ≤
      Real.exp ((1+2*Csup)*Real.sqrt L) := by
    calc
      _ ≤ Real.exp (Real.sqrt L)*Real.exp (2*Csup*Real.sqrt L) :=
        mul_le_mul_of_nonneg_right h.2 (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  change _ ^ (1/(2*(R:ℝ))) ≤ _
  apply (Real.rpow_le_rpow (by positivity) hprod hpow).trans
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  apply Real.exp_le_exp.mpr
  have hc : 0 ≤ 1+2*Csup := by linarith
  have hs : Real.sqrt L ≤ 2*(R:ℝ) := by linarith
  have hh := (div_le_iff₀ hden).mpr (mul_le_mul_of_nonneg_left hs hc)
  simpa only [div_eq_mul_inv,one_div,one_mul] using hh

/-- The localization conclusions on the nonempty actual moving r20
source family, with all constants fixed before L. -/
theorem b651_eventually_actual_parity_localization434
    (J : ℕ) (Ck Csup : ℝ) (hCk : 0 ≤ Ck) (hCsup : 0 ≤ Csup) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧ (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      (b651ParityWindowSize434 J Ck L:ℝ) ≤ Real.exp (Real.sqrt L) ∧
      ((b651ParityWindowSize434 J Ck L:ℝ)*Real.exp (2*Csup*Real.sqrt L))^
        (1/(2*(Nat.ceil (L^(13/25:ℝ)):ℝ))) ≤ Real.exp (1+2*Csup) := by
  filter_upwards [b651_eventually_parity_window_sqrt434 J Ck hCk,
    b651_eventually_parity_localization_factor434 J Ck Csup hCk hCsup,
    eventually_source_native_original_group_masses434 20 (by norm_num)]
    with L hW hF hMass
  exact ⟨hW.1,hMass.2.1,hW.2,hF⟩
end Green64Analytic.SourceBlockSieve

end

end

