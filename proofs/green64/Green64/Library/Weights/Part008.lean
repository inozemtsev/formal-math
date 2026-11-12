module

public import Green64.Library.Weights.Part007
public import Mathlib.Tactic
public import Green64.Library.Weights.Part006
public import Green64.Library.Analysis.Estimates.Part001
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Green64.Library.Weights.Part002
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Green64.Library.Weights.Part001

@[expose] public section

/-!
# Weights / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## M1RealVertical -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem real_smooth_vertical_integrable
    (h : ℝ → ℝ) (σ M : ℝ)
    (hd : ContDiff ℝ (↑(⊤:ℕ∞)) h)
    (hM : 1 ≤ M)
    (hsupp : ∀ t : ℝ, t ≤ (1/2:ℝ) ∨ (3:ℝ) < t → h t = 0)
    (hflat : ∀ k : ℕ, iteratedDeriv k h (1/2:ℝ) = 0 ∧
      iteratedDeriv k h (3:ℝ) = 0)
    (hrange : ∀ t ∈ Set.Icc (1/2:ℝ) 3, |h t| ≤ 1)
    (hderiv : ∀ t ∈ Set.Icc (1/2:ℝ) 3, |iteratedDeriv 2 h t| ≤ M)
    (hσlo : -1 ≤ σ) (hσhi : σ ≤ 1) :
    Complex.VerticalIntegrable (mellin (fun t : ℝ => (h t : ℂ))) σ := by
  let g : ℕ → ℝ → ℂ := complexIteratedDerivFamily h
  have hg0 : ∀ t ∈ Set.Icc (1/2:ℝ) 3, ‖g 0 t‖ ≤ M := by
    intro t ht
    change ‖((h t : ℝ) : ℂ)‖ ≤ M
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hrange t ht).trans hM
  have hgj : ∀ t ∈ Set.Icc (1/2:ℝ) 3, ‖g 2 t‖ ≤ M := by
    intro t ht
    change ‖((iteratedDeriv 2 h t : ℝ) : ℂ)‖ ≤ M
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hderiv t ht
  have hgsupport : ∀ t : ℝ, t ≤ (1/2:ℝ) ∨ (3:ℝ) < t →
      g 0 t = 0 := by
    intro t ht
    change ((h t:ℝ):ℂ) = 0
    simp [hsupp t ht]
  have hgcont : ∀ k ≤ 2, Continuous (g k) := by
    intro k hk
    exact complexIteratedDerivFamily_continuous h hd k
  have hgderiv : ∀ k < 2, ∀ t ∈ Set.Icc (1/2:ℝ) 3,
      HasDerivAt (g k) (g (k+1) t) t := by
    intro k hk t ht
    exact complexIteratedDerivFamily_hasDerivAt h hd k t
  have hgflat : ∀ k < 2,
      g k (1/2:ℝ) = 0 ∧ g k (3:ℝ) = 0 := by
    intro k hk
    constructor
    · change ((iteratedDeriv k h (1/2:ℝ):ℝ):ℂ) = 0
      simpa using congrArg Complex.ofReal ((hflat k).1)
    · change ((iteratedDeriv k h (3:ℝ):ℝ):ℂ) = 0
      simpa using congrArg Complex.ofReal ((hflat k).2)
  have hresult := vertical_integrable_from_s2 (1/2:ℝ) 3 σ M g
    (by norm_num) (by norm_num) (by norm_num)
    hσlo hσhi (le_trans (by norm_num) hM)
    hgsupport hgcont hgderiv hgflat hg0 hgj
  have hfun : g 0 = (fun t : ℝ => ((h t : ℝ) : ℂ)) := by
    funext t
    exact complexIteratedDerivFamily_zero _ t
  rw [hfun] at hresult
  exact hresult
end Green64Analytic.LongPrime

end

/-! ## S1S2RealBridge -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem real_smooth_mellin_decay
    (j : ℕ) (h : ℝ → ℝ) (s : ℂ) (M : ℝ)
    (hd : ContDiff ℝ (↑(⊤:ℕ∞)) h)
    (hM : 1 ≤ M)
    (hsupp : ∀ t : ℝ, t ≤ (1/2:ℝ) ∨ (3:ℝ) < t → h t = 0)
    (hflat : ∀ k : ℕ, iteratedDeriv k h (1/2:ℝ) = 0 ∧
      iteratedDeriv k h (3:ℝ) = 0)
    (hrange : ∀ t ∈ Set.Icc (1/2:ℝ) 3, |h t| ≤ 1)
    (hderiv : ∀ t ∈ Set.Icc (1/2:ℝ) 3, |iteratedDeriv j h t| ≤ M)
    (hσlo : -1 ≤ s.re) (hσhi : s.re ≤ 1) :
    ‖mellin (fun t : ℝ => (h t : ℂ)) s‖ ≤
      20*(8:ℝ)^j*M/(1+|s.im|)^j := by
  let g : ℕ → ℝ → ℂ := complexIteratedDerivFamily h
  have hg0 : ∀ t ∈ Set.Icc (1/2:ℝ) 3, ‖g 0 t‖ ≤ M := by
    intro t ht
    have hh := hrange t ht
    change ‖((h t : ℝ) : ℂ)‖ ≤ M
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hh.trans hM
  have hgj : ∀ t ∈ Set.Icc (1/2:ℝ) 3, ‖g j t‖ ≤ M := by
    intro t ht
    change ‖((iteratedDeriv j h t : ℝ) : ℂ)‖ ≤ M
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hderiv t ht
  have hgsupport : ∀ t : ℝ, t ≤ (1/2:ℝ) ∨ (3:ℝ) < t →
      g 0 t = 0 := by
    intro t ht
    change ((h t:ℝ):ℂ) = 0
    simp [hsupp t ht]
  have hgcont : ∀ k ≤ j, Continuous (g k) := by
    intro k hk
    exact complexIteratedDerivFamily_continuous h hd k
  have hgderiv : ∀ k < j, ∀ t ∈ Set.Icc (1/2:ℝ) 3,
      HasDerivAt (g k) (g (k+1) t) t := by
    intro k hk t ht
    exact complexIteratedDerivFamily_hasDerivAt h hd k t
  have hgflat : ∀ k < j,
      g k (1/2:ℝ) = 0 ∧ g k (3:ℝ) = 0 := by
    intro k hk
    constructor
    · change ((iteratedDeriv k h (1/2:ℝ):ℝ):ℂ) = 0
      simpa using congrArg Complex.ofReal ((hflat k).1)
    · change ((iteratedDeriv k h (3:ℝ):ℝ):ℂ) = 0
      simpa using congrArg Complex.ofReal ((hflat k).2)
  have hh := mellin_oneplus_decay j (1/2:ℝ) 3 g s M
    (by norm_num) (by norm_num) (by norm_num)
    hσlo hσhi (le_trans (by norm_num) hM)
    hgsupport hgderiv
    (fun k hk => (hgcont (k+1) (Nat.succ_le_of_lt hk)).intervalIntegrable _ _)
    hgflat hg0 hgj
  have hfun : g 0 = (fun t : ℝ => ((h t : ℝ) : ℂ)) := by
    funext t
    exact complexIteratedDerivFamily_zero h t
  rw [hfun] at hh
  exact hh
end Green64Analytic.LongPrime

end

/-! ## S1S2ActualDecay -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem actual_smooth_cutoff_mellin_decay
    (j : ℕ) (a b ε : ℝ) (s : ℂ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hε : 0 < ε) (hεquarter : ε ≤ 1/4)
    (hσlo : -1 ≤ s.re) (hσhi : s.re ≤ 1) :
    ‖mellin (fun t : ℝ => ((smoothIntervalWeight a b ε t : ℝ) : ℂ)) s‖ ≤
      20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)/
        (1+|s.im|)^j := by
  have hInv : 1 ≤ ε⁻¹ :=
    (one_le_inv₀ hε).2 (by linarith)
  have hM : 1 ≤ ε⁻¹^j*sourceCutoffDerivConst j :=
    one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ hInv) (sourceCutoffDerivConst_ge_one j)
  have hsupport : ∀ t : ℝ, t ≤ (1/2:ℝ) ∨ (3:ℝ) < t →
      smoothIntervalWeight a b ε t = 0 := by
    intro t ht
    rcases ht with ht | ht
    · exact smoothIntervalWeight_zero_left a b ε t hε (by linarith)
    · exact smoothIntervalWeight_zero_right a b ε t hε (by linarith)
  have hRange : ∀ t ∈ Set.Icc (1/2:ℝ) 3,
      |smoothIntervalWeight a b ε t| ≤ 1 := by
    intro t ht
    obtain ⟨h0,h1⟩ := smoothIntervalWeight_range a b ε t
    simpa only [abs_of_nonneg h0] using h1
  have hDerivative : ∀ t ∈ Set.Icc (1/2:ℝ) 3,
      |iteratedDeriv j (smoothIntervalWeight a b ε) t| ≤
        ε⁻¹^j*sourceCutoffDerivConst j := by
    intro t ht
    exact smoothIntervalWeight_deriv_scaled j a b ε t hε
  exact real_smooth_mellin_decay j (smoothIntervalWeight a b ε) s
    (ε⁻¹^j*sourceCutoffDerivConst j)
    (smoothIntervalWeight_contDiff a b ε) hM
    hsupport (smoothIntervalWeight_flat_endpoints a b ε ha hb hε hεquarter)
    hRange hDerivative hσlo hσhi
end Green64Analytic.LongPrime

end

/-! ## M1ActualCutoffInv -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem actual_source_cutoff_mellin_inversion
    (a b ε σ x : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hε : 0 < ε) (hεquarter : ε ≤ 1/4)
    (hσlo : -1 ≤ σ) (hσhi : σ ≤ 1) (hx : 0 < x) :
    mellinInv σ (mellin (fun t : ℝ =>
      ((smoothIntervalWeight a b ε t : ℝ) : ℂ))) x =
      ((smoothIntervalWeight a b ε x : ℝ) : ℂ) := by
  let h : ℝ → ℝ := smoothIntervalWeight a b ε
  let M : ℝ := ε⁻¹^2 * sourceCutoffDerivConst 2
  have hInv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 (by linarith)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hInv) (sourceCutoffDerivConst_ge_one 2)
  have hsupport : ∀ t : ℝ, t ≤ (1/2:ℝ) ∨ (3:ℝ) < t → h t = 0 := by
    intro t ht
    rcases ht with ht | ht
    · exact smoothIntervalWeight_zero_left a b ε t hε (by
        linarith)
    · exact smoothIntervalWeight_zero_right a b ε t hε (by
        linarith)
  have hRange : ∀ t ∈ Set.Icc (1/2:ℝ) 3, |h t| ≤ 1 := by
    intro t ht
    obtain ⟨h0,h1⟩ := smoothIntervalWeight_range a b ε t
    simpa only [h, abs_of_nonneg h0] using h1
  have hDerivative : ∀ t ∈ Set.Icc (1/2:ℝ) 3,
      |iteratedDeriv 2 h t| ≤ M := by
    intro t ht
    exact smoothIntervalWeight_deriv_scaled 2 a b ε t hε
  exact real_smooth_mellin_inversion h σ M x
    (smoothIntervalWeight_contDiff a b ε) hM
    hsupport (smoothIntervalWeight_flat_endpoints a b ε ha hb hε hεquarter)
    hRange hDerivative hσlo hσhi hx
end Green64Analytic.LongPrime

end

/-! ## M1ActualCutoffVertical -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem actual_source_cutoff_vertical_integrable
    (a b ε σ : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hε : 0 < ε) (hεquarter : ε ≤ 1/4)
    (hσlo : -1 ≤ σ) (hσhi : σ ≤ 1) :
    Complex.VerticalIntegrable (mellin (fun t : ℝ =>
      ((smoothIntervalWeight a b ε t : ℝ) : ℂ))) σ := by
  let h : ℝ → ℝ := smoothIntervalWeight a b ε
  let M : ℝ := ε⁻¹^2 * sourceCutoffDerivConst 2
  have hInv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 (by linarith)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hInv) (sourceCutoffDerivConst_ge_one 2)
  have hsupport : ∀ t : ℝ, t ≤ (1/2:ℝ) ∨ (3:ℝ) < t → h t = 0 := by
    intro t ht
    rcases ht with ht | ht
    · exact smoothIntervalWeight_zero_left a b ε t hε (by
        linarith)
    · exact smoothIntervalWeight_zero_right a b ε t hε (by
        linarith)
  have hRange : ∀ t ∈ Set.Icc (1/2:ℝ) 3, |h t| ≤ 1 := by
    intro t ht
    obtain ⟨h0,h1⟩ := smoothIntervalWeight_range a b ε t
    simpa only [h, abs_of_nonneg h0] using h1
  have hDerivative : ∀ t ∈ Set.Icc (1/2:ℝ) 3,
      |iteratedDeriv 2 h t| ≤ M := by
    intro t ht
    exact smoothIntervalWeight_deriv_scaled 2 a b ε t hε
  exact real_smooth_vertical_integrable h σ M
    (smoothIntervalWeight_contDiff a b ε) hM
    hsupport (smoothIntervalWeight_flat_endpoints a b ε ha hb hε hεquarter)
    hRange hDerivative hσlo hσhi
end Green64Analytic.LongPrime

end

/-! ## M1ActualSmoothMangoldt -/

section

open ArithmeticFunction MeasureTheory
open scoped LSeries.notation
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem actual_smooth_cutoff_twisted_mangoldt_formula
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N a b ε σ t : ℝ)
    (hN : 0 < N) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hε : 0 < ε) (hεquarter : ε ≤ 1/4)
    (hσ : 0 < σ) (hσhi : σ ≤ 1) :
    let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
      (fun k : ℕ => (Λ k : ℂ))
    let s₀ : ℂ := 1-(t:ℂ)*Complex.I
    let g : ℝ → ℂ := fun x => ((smoothIntervalWeight a b ε x : ℝ) : ℂ)
    (∑' n : ℕ, LSeries.term f s₀ (n+1) *
       g (((n+1:ℕ):ℝ)/N)) =
    (1/(2*Real.pi):ℂ) * ∫ y : ℝ,
      (N:ℂ)^((σ:ℂ)+(y:ℂ)*Complex.I) *
      (-(deriv (DirichletCharacter.LFunction χ)
        (s₀+((σ:ℂ)+(y:ℂ)*Complex.I))) /
       DirichletCharacter.LFunction χ
        (s₀+((σ:ℂ)+(y:ℂ)*Complex.I))) *
      mellin g ((σ:ℂ)+(y:ℂ)*Complex.I) := by
  let g : ℝ → ℂ := fun x => ((smoothIntervalWeight a b ε x : ℝ) : ℂ)
  have hV : Complex.VerticalIntegrable (mellin g) σ :=
    actual_source_cutoff_vertical_integrable
      a b ε σ ha hab hb hε hεquarter (by linarith) hσhi
  have hInv : ∀ x : ℝ, 0 < x → mellinInv σ (mellin g) x = g x := by
    intro x hx
    exact actual_source_cutoff_mellin_inversion
      a b ε σ x ha hab hb hε hεquarter (by linarith) hσhi hx
  exact source_mangoldt_weighted_inverse_assembly
    q χ N σ t (mellin g) g hN hσ hV hInv
end Green64Analytic.LongPrime

end

/-! ## M2ActualEdges -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem actual_cutoff_mellin_rectangle_edges
    (j : ℕ) (a b ε δ right H : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hε : 0 < ε) (hεq : ε ≤ 1/4)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hright : 0 ≤ right) (hright1 : right ≤ 1)
    (hH : 0 ≤ H) :
    let g : ℝ → ℂ := fun t =>
      ((smoothIntervalWeight a b ε t : ℝ) : ℂ)
    let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
    (∀ y ∈ Set.Icc (-H) H,
      ‖mellin g ((-δ:ℂ)+(y:ℂ)*Complex.I)‖ ≤ B) ∧
    (∀ u ∈ Set.Icc (-δ) right,
      ‖mellin g ((u:ℂ)-H*Complex.I)‖ ≤ B/(1+H)^j ∧
      ‖mellin g ((u:ℂ)+H*Complex.I)‖ ≤ B/(1+H)^j) := by
  let g : ℝ → ℂ := fun t =>
    ((smoothIntervalWeight a b ε t : ℝ) : ℂ)
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  have hB : 0 ≤ B := by
    dsimp [B]
    have hC : 0 ≤ sourceCutoffDerivConst j :=
      (by norm_num : (0:ℝ) ≤ 1).trans (sourceCutoffDerivConst_ge_one j)
    positivity
  constructor
  · intro y hy
    have hs := actual_smooth_cutoff_mellin_decay j a b ε
      ((-δ:ℂ)+(y:ℂ)*Complex.I)
      ha hab hb hε hεq (by simp; linarith) (by simp; linarith)
    have him : ((-δ:ℂ)+(y:ℂ)*Complex.I).im = y := by simp
    rw [him] at hs
    have hden : (1+|y|)^j ≥ 1 :=
      one_le_pow₀ (by have := abs_nonneg y; linarith)
    have hpos : 0 < (1+|y|)^j := by positivity
    have hdiv : B/(1+|y|)^j ≤ B :=
      (div_le_iff₀ hpos).2 (by nlinarith [mul_nonneg hB (sub_nonneg.mpr hden)])
    exact hs.trans hdiv
  · intro u hu
    have hulo : -1 ≤ u := le_trans (by linarith) hu.1
    have huhi : u ≤ 1 := hu.2.trans hright1
    constructor
    · have hs := actual_smooth_cutoff_mellin_decay j a b ε
        ((u:ℂ)-(H:ℂ)*Complex.I)
        ha hab hb hε hεq (by simpa using hulo) (by simpa using huhi)
      have him : (((u:ℂ)-(H:ℂ)*Complex.I).im) = -H := by simp
      rw [him, abs_neg, abs_of_nonneg hH] at hs
      exact hs
    · have hs := actual_smooth_cutoff_mellin_decay j a b ε
        ((u:ℂ)+(H:ℂ)*Complex.I)
        ha hab hb hε hεq (by simpa using hulo) (by simpa using huhi)
      have him : (((u:ℂ)+(H:ℂ)*Complex.I).im) = H := by simp
      rw [him, abs_of_nonneg hH] at hs
      exact hs
end Green64Analytic.LongPrime

end

/-! ## M2KhaleActual -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem khale_truncated_actual_source_cutoff :
∃ δ₀ : ℝ, 0 < δ₀ ∧
  let D : ℝ → ℝ → ℝ := fun Q v =>
    10.5 * Real.log Q + 61.5 * (Real.log |v|) ^ (2/3:ℝ) *
       (Real.log (Real.log |v|)) ^ (1/3:ℝ)
  (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
     3 ≤ Q → 10 ≤ |s.im| → 1-(D Q s.im)⁻¹ ≤ s.re →
     DirichletCharacter.LFunction χ s ≠ 0) →
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N Q V δ right H t K T L a b ε : ℝ) (j : ℕ),
  let c : ℝ → ℂ := fun v => (1+δ:ℝ) + (v:ℂ)*Complex.I
  let f := DirichletCharacter.LFunction χ
  let g : ℝ → ℂ := fun u => ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
  let F : ℂ → ℂ := fun z => mellin g z * (N:ℂ)^z *
     (-deriv f (1-(t:ℂ)*Complex.I+z) / f (1-(t:ℂ)*Complex.I+z))
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  1 ≤ N → 3*(q:ℝ) ≤ Q → 0 < δ → δ < δ₀ → δ ≤ 1 →
  0 ≤ right → right ≤ 1 → right ≤ δ → 0 ≤ H →
  20+H ≤ |t| → |t|+H+8*δ ≤ V → 100*δ*D Q V ≤ 1 →
  0 < K → 0 ≤ T → 0 < L → T ≤ δ*L →
  1 ≤ a → a ≤ b → b ≤ 2 → 0 < ε → ε ≤ 1/4 →
  (∀ y ∈ Set.Icc (-H) H, ∀ w ∈ Metric.ball (c (y-t)) (8*δ),
      Real.log ‖f w‖ ≤ K*(T+δ*L)) →
  -K*T ≤ Real.log δ - Real.log 2 →
  ‖∫ y in (-H)..H, F ((right:ℂ)+y*Complex.I)‖ ≤
    2*H*(B*N^(-δ)*(3*K*L)) +
    2*(right+δ)*((B/(1+H)^j)*N^right*(3*K*L)) := by
  obtain ⟨δ₀, hδ₀, hbase⟩ := khale_truncated_mellin_lower_discharged
  refine ⟨δ₀, hδ₀, ?_⟩
  dsimp only
  intro hKh q hq χ N Q V δ right H t K T L a b ε j
    hN hqQ hδ hδ₀' hδ1 hright hright1 hra hH
    ht hV hD hK hT hL hTL
    ha hab hb hε hεq hgrowth hcenter
  let g : ℝ → ℂ := fun u => ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  have hB : 0 ≤ B := by
    dsimp [B]
    have hC := sourceCutoffDerivConst_ge_one j
    positivity
  have hMh : 0 ≤ B/(1+H)^j :=
    div_nonneg hB (pow_nonneg (by linarith) _)
  have hcont : Continuous g := by
    exact Complex.continuous_ofReal.comp
      (smoothIntervalWeight_contDiff a b ε).continuous
  have hsupport : ∀ u : ℝ, u < 1/2 ∨ 3 < u → g u = 0 := by
    intro u hu
    change ((smoothIntervalWeight a b ε u:ℝ):ℂ) = 0
    have hs := smoothIntervalWeight_support a b ε u
      ha hb hε (by linarith : ε ≤ 1/2)
      (by rcases hu with h1|h2
          · exact fun hh => (not_lt_of_ge hh.1) h1
          · exact fun hh => (not_lt_of_ge hh.2) h2)
    simpa [hs]
  have hedges := actual_cutoff_mellin_rectangle_edges
    j a b ε δ right H ha hab hb hε hεq hδ.le hδ1 hright hright1 hH
  dsimp only at hedges
  have hLeft : ∀ y ∈ Set.Icc (-H) H,
      ‖mellin g (((-δ:ℝ):ℂ)+(y:ℂ)*Complex.I)‖ ≤ B := by
    intro y hy
    simpa only [Complex.ofReal_neg] using hedges.1 y hy
  have hHorizontal : ∀ u ∈ Set.Icc (-δ) right,
      ‖mellin g ((u:ℂ)-H*Complex.I)‖ ≤ B/(1+H)^j ∧
      ‖mellin g ((u:ℂ)+H*Complex.I)‖ ≤ B/(1+H)^j := by
    intro u hu
    exact hedges.2 u hu
  exact hbase hKh q χ N Q V δ right H t K T L
    B (B/(1+H)^j) g
    hN hqQ hδ hδ₀' hδ1 hright hra hH ht hV hD
    hK hT hL hTL hB hMh hcont hsupport hgrowth hcenter
    hLeft hHorizontal
end Green64Analytic.LongPrime

end

/-! ## M2RightKernel -/

section

namespace Green64Analytic.LongPrime

theorem m2_actual_right_kernel_pointwise :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ α : ℝ, 0 < α → α < α₀ → 2*α ≤ 1 →
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
          (N a b ε t y : ℝ) (j : ℕ),
        1 ≤ N → 1 ≤ a → a ≤ b → b ≤ 2 →
        0 < ε → ε ≤ 1/4 →
        let g : ℝ → ℂ := fun u => ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
        let z : ℂ := (2*α:ℝ) + (y:ℂ)*Complex.I
        let s : ℂ := 1-(t:ℂ)*Complex.I + z
        let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
        ‖mellin g z * (N:ℂ)^z *
          (-deriv (DirichletCharacter.LFunction χ) s /
            DirichletCharacter.LFunction χ s)‖ ≤
          (B/(1+|y|)^j)*N^(2*α)*(2/α^2) := by
  obtain ⟨α₀, hα₀, hlogder⟩ := m2_right_line_quadratic_uniform
  refine ⟨α₀, hα₀, ?_⟩
  intro α hα hα₀ hα1 q _ χ N a b ε t y j
  intro hN ha hab hb hε hεq
  dsimp only

  let g : ℝ → ℂ := fun u => ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
  let z : ℂ := ((2*α:ℝ):ℂ) + (y:ℂ)*Complex.I
  let s : ℂ := 1-(t:ℂ)*Complex.I+z
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  have hNpos : 0 < N := by linarith
  have hm : ‖mellin g z‖ ≤ B/(1+|y|)^j := by
    have hs := actual_smooth_cutoff_mellin_decay j a b ε z
      ha hab hb hε hεq
      (by dsimp [z]; simp; linarith)
      (by dsimp [z]; simp; linarith)
    have him : z.im = y := by dsimp [z]; simp
    simpa [g, B, him] using hs
  have hsEq : s = ((1+2*α:ℝ):ℂ) + ((y-t:ℝ):ℂ)*Complex.I := by
    dsimp [s,z]
    push_cast
    ring
  have hd : ‖-deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s‖ ≤ 2/α^2 := by
    rw [hsEq]
    exact hlogder α hα hα₀ q χ (y-t)
  have hp : ‖(N:ℂ)^z‖ = N^(2*α) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    dsimp [z]
    simp
  have hB : 0 ≤ B := by
    dsimp [B]
    have hc := sourceCutoffDerivConst_ge_one j
    positivity
  have hBdiv : 0 ≤ B/(1+|y|)^j :=
    div_nonneg hB (pow_nonneg (by positivity) _)
  have hNp : 0 ≤ N^(2*α) := Real.rpow_nonneg (by linarith) _
  change ‖mellin g z * (N:ℂ)^z *
       (-deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s)‖ ≤
      (B/(1+|y|)^j)*N^(2*α)*(2/α^2)
  calc
    _ = ‖mellin g z‖ * N^(2*α) *
      ‖-deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s‖ := by
      rw [norm_mul, norm_mul, hp]
    _ ≤ (B/(1+|y|)^j)*N^(2*α)*(2/α^2) := by
      gcongr
end Green64Analytic.LongPrime

end

/-! ## M2KernelContinuity -/

section

set_option autoImplicit false

namespace Green64Analytic.LongPrime

theorem m2_right_kernel_continuous
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (g : ℝ → ℂ) (hg : Continuous g)
    (hsupport : ∀ u : ℝ, u < 1/2 ∨ 3 < u → g u = 0)
    (N α t : ℝ) (hN : 0 < N) (hα : 0 < α) :
    Continuous (fun y : ℝ =>
      let z : ℂ := ((2*α:ℝ):ℂ) + (y:ℂ)*Complex.I
      let s : ℂ := 1-(t:ℂ)*Complex.I+z
      mellin g z * (N:ℂ)^z *
        (-(deriv (DirichletCharacter.LFunction χ) s)/
           DirichletCharacter.LFunction χ s)) := by
  let Ω : Set ℂ := {s : ℂ | 1 < s.re}
  have ho : IsOpen Ω := isOpen_Ioi.preimage Complex.continuous_re
  have hL : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) Ω := by
    intro w hw
    exact (DirichletCharacter.differentiableAt_LFunction χ w
      (Or.inl (by
        intro h
        have : w.re = 1 := congrArg Complex.re h
        dsimp [Ω] at hw
        simp_all))).differentiableWithinAt
  have hdL : DifferentiableOn ℂ (deriv (DirichletCharacter.LFunction χ)) Ω :=
    hL.deriv ho
  let z : ℝ → ℂ := fun y => ((2*α:ℝ):ℂ)+(y:ℂ)*Complex.I
  let s : ℝ → ℂ := fun y => 1-(t:ℂ)*Complex.I+z y
  have hz : Continuous z := by dsimp [z]; fun_prop
  have hs : Continuous s := by dsimp [s]; fun_prop
  have hMem : ∀ y : ℝ, s y ∈ Ω := by
    intro y
    dsimp [s, z, Ω]
    simp
    linarith
  have hNo (y : ℝ) :
      DirichletCharacter.LFunction χ (s y) ≠ 0 := by
    have hr : 1 < (s y).re := hMem y
    rw [DirichletCharacter.LFunction_eq_LSeries χ hr]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hr
  have hF : Continuous (fun y : ℝ =>
      DirichletCharacter.LFunction χ (s y)) :=
    hL.continuousOn.comp_continuous hs hMem
  have hdF : Continuous (fun y : ℝ =>
      deriv (DirichletCharacter.LFunction χ) (s y)) :=
    hdL.continuousOn.comp_continuous hs hMem
  have hM : Continuous (fun y : ℝ => mellin g (z y)) :=
    (compact_mellin_entire g hg hsupport).continuous.comp hz
  have hP : Continuous (fun y : ℝ => (N:ℂ)^(z y)) := by
    have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    exact hz.const_cpow (.inl hNc)
  change Continuous (fun y =>
      mellin g (z y) * (N:ℂ)^(z y) *
      (-(deriv (DirichletCharacter.LFunction χ) (s y)) /
         DirichletCharacter.LFunction χ (s y)))
  exact (hM.mul hP).mul (hdF.neg.div hF hNo)
end Green64Analytic.LongPrime

end

/-! ## Standalone.LongPrimeStageA -/

section

-- Flat compilation of unchanged original theorem/proof bodies.

-- BEGIN M2RightShiftScale

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Right-line offset compatible with the G2 zero-free strip budget. -/
theorem m2_right_shift_feasible
    (L δ : ℝ) (hL : 0 < L) (hbudget : L⁻¹ ≤ δ)
    (hsmall : δ ≤ 1/100) :
    0 < L⁻¹ ∧ L⁻¹ ≤ δ ∧ L⁻¹ ≤ 1 := by
  exact ⟨inv_pos.mpr hL, hbudget, hbudget.trans (by linarith)⟩

/-- On the full source U1 scale, the Mellin right-line factor is
bounded independently of x, N, q, χ and the large frequency t. -/
theorem m2_right_shift_power_uniform
    (L η N : ℝ) (hL : 0 < L) (hN : 0 < N)
    (hupper : N ≤ (Real.exp L)^η) :
    N ^ L⁻¹ ≤ Real.exp η := by
  have htarget : 0 < (Real.exp L)^η :=
    Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hlog : Real.log N ≤ η*L := by
    calc
      Real.log N ≤ Real.log ((Real.exp L)^η) :=
        Real.log_le_log hN hupper
      _ = η*L := by rw [Real.log_rpow (Real.exp_pos L) η, Real.log_exp]
  have hscaled : Real.log N * L⁻¹ ≤ η := by
    have hi := mul_le_mul_of_nonneg_right hlog (le_of_lt (inv_pos.mpr hL))
    calc
      Real.log N * L⁻¹ ≤ (η*L)*L⁻¹ := hi
      _ = η := by
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hL), mul_one]
  rw [Real.rpow_def_of_pos hN]
  exact Real.exp_le_exp.mpr hscaled


end Green64Analytic.LongPrime

-- END M2RightShiftScale

-- BEGIN M2SourceKhaleSpecialization

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- The complete *source-parameter* truncated Khale shift.
The external hypothesis is precisely the source zero-free region for L-functions:
no prime polynomial bound or all-interval prime estimate is assumed. -/
theorem m2_source_khale_truncated_parameters :
      (let D : ℝ → ℝ → ℝ := fun Q v =>
         10.5 * Real.log Q +
         61.5 * (Real.log |v|) ^ (2/3:ℝ) *
           (Real.log (Real.log |v|)) ^ (1/3:ℝ)
       (∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
         3 ≤ Q → 10 ≤ |s.im| → 1-(D Q s.im)⁻¹ ≤ s.re →
         DirichletCharacter.LFunction χ s ≠ 0)) →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ C C₅ : ℝ, 0 < C → 0 ≤ C₅ →
      ∃ L₀ : ℝ, 3 ≤ L₀ ∧
        ∀ L : ℝ, L₀ ≤ L →
          let Q : ℝ := 3*L^C
          let V : ℝ := 3*Real.exp (3*L)
          let D : ℝ := 10.5*Real.log Q +
            61.5*(Real.log V)^(2/3:ℝ) *
              (Real.log (Real.log V))^(1/3:ℝ)
          let δ : ℝ := (100*D)⁻¹
          let H : ℝ := L^C₅
          let right : ℝ := L⁻¹
          ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
            (q:ℝ) ≤ L^C →
          ∀ (N a b ε t : ℝ) (j : ℕ),
            1 ≤ N → 1 ≤ a → a ≤ b → b ≤ 2 →
            0 < ε → ε ≤ 1/4 →
            L^(C₅+3) ≤ |t| → |t| ≤ (Real.exp L)^2 →
            let g : ℝ → ℂ :=
              fun u => ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
            let f := DirichletCharacter.LFunction χ
            let F : ℂ → ℂ := fun z =>
              mellin g z * (N:ℂ)^z *
                (-deriv f (1-(t:ℂ)*Complex.I+z) /
                  f (1-(t:ℂ)*Complex.I+z))
            let B : ℝ :=
              20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
            ‖∫ y in (-H)..H, F ((right:ℂ)+(y:ℂ)*Complex.I)‖ ≤
              2*H*(B*N^(-δ)*(3*50*L)) +
                2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L))
  := by
  intro hKhale
  obtain ⟨δ₀, hδ₀, hcontour⟩ := khale_truncated_actual_source_cutoff
  dsimp only at hcontour
  refine ⟨δ₀, hδ₀, ?_⟩
  intro C C₅ hC hC₅
  obtain ⟨L₁,hL₁,hParam⟩ :=
    g2_all_source_parameters C C₅ δ₀ hC hC₅ hδ₀
  obtain ⟨L₂,hL₂,hGrowth⟩ :=
    g2_actual_LFunction_disk_growth C C₅ δ₀ hC hC₅ hδ₀
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL Q V D δ H right q _ χ hq N a b ε t j
    hN ha hab hb hε hεq htlo hthi
  dsimp only
  have hL₁' : L₁ ≤ L := (le_max_left _ _).trans hL
  have hL₂' : L₂ ≤ L := (le_max_right _ _).trans hL
  have hL3 : 3 ≤ L := hL₁.trans hL₁'
  have hLp : 0 < L := by linarith
  have hp := hParam L hL₁'
  change
    0 < δ ∧ δ < δ₀ ∧ δ ≤ 1/100 ∧ L⁻¹ ≤ δ ∧
      Real.log L ≤ δ*L ∧
      -50*Real.log L ≤ Real.log δ-Real.log 2 ∧
      100*δ*D=1 ∧
      (∀ (q : ℕ), (q:ℝ) ≤ L^C → 3*(q:ℝ) ≤ Q) ∧
      (∀ (t y : ℝ), L^(C₅+3) ≤ |t| →
        |t| ≤ (Real.exp L)^2 → |y| ≤ L^C₅ →
        20+L^C₅ ≤ |t| ∧
          20 ≤ |y-t| ∧ |y-t| ≤ 2*(Real.exp L)^2 ∧
          |t|+L^C₅+8*δ ≤ V) at hp
  rcases hp with ⟨hδp,hδmax,hδsmall,hRight,hLog,hCenter,hD,hQ,hFreq⟩
  have hHp : 0 < H := by
    dsimp [H]
    exact Real.rpow_pos_of_pos hLp C₅
  have hFreq0 : |(0:ℝ)| ≤ H := by
    simp only [abs_zero]
    exact hHp.le
  obtain ⟨hHt,_,_,hV⟩ := hFreq t 0 htlo hthi hFreq0
  have hRightp : 0 ≤ right := by dsimp [right]; positivity
  have hRight1 : right ≤ 1 := by
    dsimp [right]
    have := hRight.trans hδsmall
    linarith
  have hGrowthDisk : ∀ y ∈ Set.Icc (-H) H,
     ∀ w ∈ Metric.ball
       (((1+δ:ℝ):ℂ)+((y-t:ℝ):ℂ)*Complex.I) (8*δ),
      Real.log ‖DirichletCharacter.LFunction χ w‖ ≤
        50*(Real.log L+δ*L) := by
    intro y hy w hw
    have hyabs : |y| ≤ H := abs_le.mpr ⟨hy.1,hy.2⟩
    have hBall : ‖w - ((1+δ:ℝ):ℂ) -
        ((y-t:ℝ):ℂ)*Complex.I‖ ≤ 8*δ := by
      have hww := Metric.mem_ball.mp hw
      simpa only [dist_eq_norm, sub_add_eq_sub_sub] using (le_of_lt hww)
    exact hGrowth L hL₂' q χ hq t y w htlo hthi hyabs hBall
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hBudget : 100*δ*(10.5*Real.log Q +
      61.5*(Real.log |V|)^(2/3:ℝ) *
        (Real.log (Real.log |V|))^(1/3:ℝ)) ≤ 1 := by
    rw [abs_of_pos hVpos]
    change 100*δ*D ≤ 1
    exact hD.le
  have hB := hcontour hKhale q χ N Q V δ right H t
    50 (Real.log L) L a b ε j
    hN (hQ q hq) hδp hδmax
    (by linarith : δ ≤ 1)
    hRightp hRight1 hRight hHp.le hHt hV
    hBudget
    (by norm_num : 0 < (50:ℝ))
    (Real.log_nonneg (by linarith : 1 ≤ L))
    hLp hLog
    ha hab hb hε hεq hGrowthDisk hCenter
  simpa only using hB

end Green64Analytic.LongPrime

-- END M2SourceKhaleSpecialization

-- BEGIN M2TailEnvelope

open MeasureTheory Set Real Module

namespace Green64Analytic.LongPrime

theorem m2_upper_tail_integral_decay
    (r H : ℝ) (hr : 1 < r) (hH : 0 < H) :
    (∫ y : ℝ in Set.Ioi H, (1+|y|)^(-r)) ≤
      -H^(-r+1)/(-r+1) := by
  have hdim : (finrank ℝ ℝ : ℝ) < r := by
    simpa using hr
  have hglobal : Integrable (fun y : ℝ => (1+|y|)^(-r)) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E:=ℝ) hdim)
  have hleft : IntegrableOn (fun y : ℝ => (1+|y|)^(-r)) (Set.Ioi H) :=
    hglobal.integrableOn
  have hright : IntegrableOn (fun y : ℝ => y^(-r)) (Set.Ioi H) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hH
  calc
    (∫ y : ℝ in Set.Ioi H, (1+|y|)^(-r)) ≤
      ∫ y : ℝ in Set.Ioi H, y^(-r) := by
        apply MeasureTheory.setIntegral_mono_on hleft hright measurableSet_Ioi
        intro y hy
        have hypos : 0 < y := hH.trans (Set.mem_Ioi.mp hy)
        rw [abs_of_pos hypos]
        exact Real.rpow_le_rpow_of_nonpos hypos (by linarith) (by linarith)
    _ = -H^(-r+1)/(-r+1) :=
      integral_Ioi_rpow_of_lt (by linarith) hH

theorem m2_lower_tail_integral_decay
    (r H : ℝ) (hr : 1 < r) (hH : 0 < H) :
    (∫ y : ℝ in Set.Iio (-H), (1+|y|)^(-r)) ≤
      -H^(-r+1)/(-r+1) := by
  have heq :
      (∫ y : ℝ in Set.Iio (-H), (1+|y|)^(-r)) =
      (∫ y : ℝ in Set.Ioi H, (1+|y|)^(-r)) := by
    calc
      _ = ∫ y : ℝ in Set.Iic (-H), (1+|y|)^(-r) := by
          rw [integral_Iic_eq_integral_Iio]
      _ = ∫ y : ℝ in Set.Ioi H, (1+|-y|)^(-r) :=
          (integral_comp_neg_Ioi H (fun y : ℝ => (1+|y|)^(-r))).symm
      _ = ∫ y : ℝ in Set.Ioi H, (1+|y|)^(-r) := by
          simp only [abs_neg]
  rw [heq]
  exact m2_upper_tail_integral_decay r H hr hH

end Green64Analytic.LongPrime

-- END M2TailEnvelope

-- BEGIN M2IntegralTail

open MeasureTheory Set Real Module

namespace Green64Analytic.LongPrime

theorem m2_complex_right_tail_bound
    (f : ℝ → ℂ) (r H C : ℝ)
    (hr : 1 < r) (hH : 0 < H) (hC : 0 ≤ C)
    (hf : Continuous f)
    (hpoint : ∀ y : ℝ, ‖f y‖ ≤ C * (1+|y|)^(-r)) :
    ‖∫ y : ℝ in Set.Ioi H, f y‖ ≤
      C * (-H^(-r+1)/(-r+1)) := by
  have hdim : (finrank ℝ ℝ : ℝ) < r := by simpa using hr
  have hg0 : Integrable (fun y : ℝ => (1+|y|)^(-r)) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E:=ℝ) hdim)
  have hg : IntegrableOn (fun y : ℝ => C * (1+|y|)^(-r)) (Set.Ioi H) :=
    (hg0.const_mul C).integrableOn
  have hfi : IntegrableOn f (Set.Ioi H) := by
    apply Integrable.mono' hg (hf.aestronglyMeasurable)
    exact Filter.Eventually.of_forall hpoint
  have hmono :
      (∫ y : ℝ in Set.Ioi H, ‖f y‖) ≤
        ∫ y : ℝ in Set.Ioi H, C * (1+|y|)^(-r) := by
    exact setIntegral_mono_on hfi.norm hg measurableSet_Ioi
      (fun y _ => hpoint y)
  calc
    ‖∫ y : ℝ in Set.Ioi H, f y‖ ≤
       ∫ y : ℝ in Set.Ioi H, ‖f y‖ :=
         norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ in Set.Ioi H, C * (1+|y|)^(-r) := hmono
    _ = C * (∫ y : ℝ in Set.Ioi H, (1+|y|)^(-r)) := by rw [integral_const_mul]
    _ ≤ C * (-H^(-r+1)/(-r+1)) :=
      mul_le_mul_of_nonneg_left
        (m2_upper_tail_integral_decay r H hr hH) hC

theorem m2_complex_left_tail_bound
    (f : ℝ → ℂ) (r H C : ℝ)
    (hr : 1 < r) (hH : 0 < H) (hC : 0 ≤ C)
    (hf : Continuous f)
    (hpoint : ∀ y : ℝ, ‖f y‖ ≤ C * (1+|y|)^(-r)) :
    ‖∫ y : ℝ in Set.Iio (-H), f y‖ ≤
      C * (-H^(-r+1)/(-r+1)) := by
  have hdim : (finrank ℝ ℝ : ℝ) < r := by simpa using hr
  have hg0 : Integrable (fun y : ℝ => (1+|y|)^(-r)) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E:=ℝ) hdim)
  have hg : IntegrableOn (fun y : ℝ => C * (1+|y|)^(-r))
      (Set.Iio (-H)) := (hg0.const_mul C).integrableOn
  have hfi : IntegrableOn f (Set.Iio (-H)) := by
    apply Integrable.mono' hg (hf.aestronglyMeasurable)
    exact Filter.Eventually.of_forall hpoint
  have hmono :
      (∫ y : ℝ in Set.Iio (-H), ‖f y‖) ≤
        ∫ y : ℝ in Set.Iio (-H), C * (1+|y|)^(-r) := by
    exact setIntegral_mono_on hfi.norm hg measurableSet_Iio
      (fun y _ => hpoint y)
  calc
    ‖∫ y : ℝ in Set.Iio (-H), f y‖ ≤
       ∫ y : ℝ in Set.Iio (-H), ‖f y‖ :=
         norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ in Set.Iio (-H), C * (1+|y|)^(-r) := hmono
    _ = C * (∫ y : ℝ in Set.Iio (-H), (1+|y|)^(-r)) := by rw [integral_const_mul]
    _ ≤ C * (-H^(-r+1)/(-r+1)) :=
      mul_le_mul_of_nonneg_left
        (m2_lower_tail_integral_decay r H hr hH) hC

end Green64Analytic.LongPrime

-- END M2IntegralTail

-- BEGIN M2ActualTails
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem m2_actual_source_cutoff_both_right_tails :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ α : ℝ, 0 < α → α < α₀ → 2*α ≤ 1 →
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
          (N a b ε t H : ℝ) (j : ℕ),
        1 ≤ N → 1 ≤ a → a ≤ b → b ≤ 2 →
        0 < ε → ε ≤ 1/4 → 0 < H → 2 ≤ j →
        let g : ℝ → ℂ := fun u => ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
        let F : ℝ → ℂ := fun y =>
          let z : ℂ := ((2*α:ℝ):ℂ) + (y:ℂ)*Complex.I
          let s : ℂ := 1-(t:ℂ)*Complex.I + z
          mellin g z * (N:ℂ)^z *
            (-deriv (DirichletCharacter.LFunction χ) s /
              DirichletCharacter.LFunction χ s)
        let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
        let C : ℝ := B * N^(2*α) * (2/α^2)
        (‖∫ y : ℝ in Set.Ioi H, F y‖ ≤ C * (-H^(1-(j:ℝ))/(1-(j:ℝ)))) ∧
        (‖∫ y : ℝ in Set.Iio (-H), F y‖ ≤ C * (-H^(1-(j:ℝ))/(1-(j:ℝ)))) := by
  obtain ⟨α₀, hα₀, hpointAll⟩ := m2_actual_right_kernel_pointwise
  refine ⟨α₀, hα₀, ?_⟩
  intro α hα hα₀ hαone q _ χ N a b ε t H j
  intro hN ha hab hb hε hεq hH hj
  dsimp only
  let g : ℝ → ℂ := fun u => ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
  let F : ℝ → ℂ := fun y =>
    let z : ℂ := ((2*α:ℝ):ℂ) + (y:ℂ)*Complex.I
    let s : ℂ := 1-(t:ℂ)*Complex.I + z
    mellin g z * (N:ℂ)^z *
       (-deriv (DirichletCharacter.LFunction χ) s /
         DirichletCharacter.LFunction χ s)
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  let C : ℝ := B * N^(2*α) * (2/α^2)
  have hNpos : 0 < N := by linarith
  have hg : Continuous g :=
    Complex.continuous_ofReal.comp
      (smoothIntervalWeight_contDiff a b ε).continuous
  have hsup : ∀ u : ℝ, u < 1/2 ∨ 3 < u → g u = 0 := by
    intro u hu
    change ((smoothIntervalWeight a b ε u : ℝ) : ℂ) = 0
    have hs := smoothIntervalWeight_support a b ε u
      ha hb hε (by linarith : ε ≤ 1/2)
      (by
        rcases hu with h1 | h2
        · exact fun hh => (not_lt_of_ge hh.1) h1
        · exact fun hh => (not_lt_of_ge hh.2) h2)
    simp [hs]
  have hcont : Continuous F := by
    exact m2_right_kernel_continuous q χ g hg hsup N α t hNpos hα
  have hC : 0 ≤ C := by
    dsimp [C,B]
    have hc := sourceCutoffDerivConst_ge_one j
    positivity
  have hr : (1:ℝ) < (j:ℝ) := by exact_mod_cast (show 1 < j by omega)
  have hpoint : ∀ y : ℝ, ‖F y‖ ≤
      C * (1+|y|)^(-(j:ℝ)) := by
    intro y
    have hm := hpointAll α hα hα₀ hαone q χ N a b ε t y j
      hN ha hab hb hε hεq
    change ‖F y‖ ≤ B/(1+|y|)^j * N^(2*α) * (2/α^2) at hm
    have hpos : 0 < 1+|y| := by positivity
    have hrpow : (1+|y|)^(-(j:ℝ)) = 1/(1+|y|)^j := by
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
      exact (one_div _).symm
    calc
      ‖F y‖ ≤ B/(1+|y|)^j * N^(2*α) * (2/α^2) := hm
      _ = C * (1+|y|)^(-(j:ℝ)) := by
        rw [hrpow]
        dsimp [C]
        ring
  have hexp : -(j:ℝ) + 1 = 1-(j:ℝ) := by ring
  constructor
  · have h := m2_complex_right_tail_bound F (j:ℝ) H C hr hH hC hcont hpoint
    simpa only [hexp] using h
  · have h := m2_complex_left_tail_bound F (j:ℝ) H C hr hH hC hcont hpoint
    simpa only [hexp] using h

end Green64Analytic.LongPrime

-- END M2ActualTails

-- BEGIN M2RightSourceTailScale

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Both actual right-line Mellin tails are polynomially small in H,
with the dangerous N^δ replaced by exp η.  No estimate for primes is
assumed; this is a consequence of the von Mangoldt Dirichlet series. -/
theorem m2_actual_source_right_tails_on_log_scale :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ L η N a b ε t H : ℝ, ∀ j : ℕ,
      1 ≤ L → 1 ≤ N → N ≤ (Real.exp L)^η →
      1 ≤ a → a ≤ b → b ≤ 2 →
      0 < ε → ε ≤ 1/4 → 0 < H → 2 ≤ j →
      L⁻¹ ≤ 1 → L⁻¹ / 2 < α₀ →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      let α : ℝ := L⁻¹ / 2
      let g : ℝ → ℂ := fun u => ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
      let F : ℝ → ℂ := fun y =>
        let z : ℂ := ((2*α:ℝ):ℂ) + (y:ℂ)*Complex.I
        let s : ℂ := 1-(t:ℂ)*Complex.I + z
        mellin g z * (N:ℂ)^z *
          (-deriv (DirichletCharacter.LFunction χ) s /
            DirichletCharacter.LFunction χ s)
      let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
      let C : ℝ := B * (Real.exp η) * (8*L^2)
      (‖∫ y : ℝ in Set.Ioi H, F y‖ ≤
          C * (-H^(1-(j:ℝ))/(1-(j:ℝ)))) ∧
      (‖∫ y : ℝ in Set.Iio (-H), F y‖ ≤
          C * (-H^(1-(j:ℝ))/(1-(j:ℝ)))) := by
  obtain ⟨α₀, hα₀, htails⟩ := m2_actual_source_cutoff_both_right_tails
  refine ⟨α₀, hα₀, ?_⟩
  intro L η N a b ε t H j hL hN hNmax ha hab hb hε hεmax hH hj
    hshift hαmax q _ χ
  dsimp only
  let α : ℝ := L⁻¹ / 2
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  have hLp : 0 < L := by linarith
  have hαp : 0 < α := by
    dsimp [α]
    exact half_pos (inv_pos.mpr hLp)
  have htwos : 2*α ≤ 1 := by
    dsimp [α]
    nlinarith [hshift]
  have hnp : N^(2*α) ≤ Real.exp η := by
    have heq : 2*α = L⁻¹ := by dsimp [α]; ring
    rw [heq]
    exact m2_right_shift_power_uniform L η N hLp
      (by linarith) hNmax
  have hconst : (2:ℝ)/α^2 = 8*L^2 := by
    dsimp [α]
    field_simp [ne_of_gt hLp]
    ring
  have hB : 0 ≤ B := by
    dsimp [B]
    have hc := sourceCutoffDerivConst_ge_one j
    positivity
  have hC : B * N^(2*α) * (2/α^2) ≤
      B * (Real.exp η) * (8*L^2) := by
    rw [hconst]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnp hB) (by positivity)
  have hjr : (1:ℝ) < j := by exact_mod_cast
    (show 1 < j by omega)
  have hpow : 0 ≤ H^(1-(j:ℝ)) := Real.rpow_nonneg hH.le _
  have hden : 0 ≤ (j:ℝ)-1 := by linarith
  have hfac : 0 ≤ -H^(1-(j:ℝ))/(1-(j:ℝ)) := by
    calc
      -(H^(1-(j:ℝ)))/(1-(j:ℝ)) =
          H^(1-(j:ℝ))/((j:ℝ)-1) := by
            rw [show (1:ℝ)-(j:ℝ) = -((j:ℝ)-1) by ring]
            simp only [div_neg, neg_div, neg_neg]
      _ ≥ 0 := div_nonneg hpow hden
  obtain ⟨hp,hn⟩ := htails α hαp
    (show α < α₀ from hαmax) htwos q χ
    N a b ε t H j hN ha hab hb hε hεmax hH hj
  dsimp only at hp hn
  constructor
  · exact hp.trans (mul_le_mul_of_nonneg_right hC hfac)
  · exact hn.trans (mul_le_mul_of_nonneg_right hC hfac)

end Green64Analytic.LongPrime

-- END M2RightSourceTailScale

-- BEGIN M2WholeLineGluing

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open MeasureTheory Set

/-- No gap between the truncated contour and the two infinite tails. -/
theorem m2_whole_line_as_truncated_and_tails
    (f : ℝ → ℂ) (H : ℝ) (hH : 0 ≤ H) (hf : Integrable f) :
    (∫ y : ℝ, f y) =
      (∫ y : ℝ in Set.Iio (-H), f y) +
      (∫ y in (-H)..H, f y) +
      (∫ y : ℝ in Set.Ioi H, f y) := by
  have hlo : IntegrableOn f (Set.Iio (-H)) := hf.integrableOn
  have hhi : IntegrableOn f (Set.Iio H) := hf.integrableOn
  have hright : IntegrableOn f (Set.Ici H) := hf.integrableOn
  have hsplit :=
    intervalIntegral.integral_Iio_sub_Iio' hhi hlo
  have hwhole :=
    intervalIntegral.integral_Iio_add_Ici hhi hright
  rw [integral_Ici_eq_integral_Ioi] at hwhole
  calc
    (∫ y : ℝ, f y) =
      (∫ y : ℝ in Set.Iio H, f y) +
        (∫ y : ℝ in Set.Ioi H, f y) := hwhole.symm
    _ = (∫ y : ℝ in Set.Iio (-H), f y) +
      (∫ y in (-H)..H, f y) +
      (∫ y : ℝ in Set.Ioi H, f y) := by rw [← hsplit]; ring

/-- The norm version used to combine Khale's finite-window contour
with the two polynomially decaying Mellin tails. -/
theorem m2_whole_line_norm_le_three
    (f : ℝ → ℂ) (H : ℝ) (hH : 0 ≤ H) (hf : Integrable f) :
    ‖∫ y : ℝ, f y‖ ≤
      ‖∫ y : ℝ in Set.Iio (-H), f y‖ +
      ‖∫ y in (-H)..H, f y‖ +
      ‖∫ y : ℝ in Set.Ioi H, f y‖ := by
  rw [m2_whole_line_as_truncated_and_tails f H hH hf]
  have hleft := norm_add_le
    (∫ y : ℝ in Set.Iio (-H), f y)
    (∫ y in (-H)..H, f y)
  have hfull := norm_add_le
    ((∫ y : ℝ in Set.Iio (-H), f y) +
     (∫ y in (-H)..H, f y))
    (∫ y : ℝ in Set.Ioi H, f y)
  linarith

end Green64Analytic.LongPrime

-- END M2WholeLineGluing

-- BEGIN M2ActualFullLine

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open MeasureTheory Set Real Module

/-- Polynomial Mellin decay of order >1 certifies integrability
over the *whole* right-hand line, not only over finite rectangles. -/
theorem m2_polynomial_complex_integrable
    (F : ℝ → ℂ) (r C : ℝ)
    (hr : 1 < r) (hC : 0 ≤ C)
    (hcont : Continuous F)
    (hmajorant : ∀ y : ℝ, ‖F y‖ ≤ C * (1+|y|)^(-r)) :
    Integrable F := by
  have hdim : (finrank ℝ ℝ : ℝ) < r := by simpa using hr
  have hpower : Integrable (fun y : ℝ => (1+|y|)^(-r)) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E:=ℝ) hdim)
  apply Integrable.mono' (hpower.const_mul C) hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall hmajorant

/-- Actual smooth source Mellin / -L'/L kernel is globally
integrable, uniformly for all q,χ,t once the positive right-line
offset is in the absolute-convergence range. -/
theorem m2_actual_right_source_integrable :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ α : ℝ, 0 < α → α < α₀ → 2*α ≤ 1 →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (N a b ε t : ℝ) (j : ℕ),
      1 ≤ N → 1 ≤ a → a ≤ b → b ≤ 2 →
      0 < ε → ε ≤ 1/4 → 2 ≤ j →
      let g : ℝ → ℂ := fun u =>
        ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
      let F : ℝ → ℂ := fun y =>
        let z : ℂ := ((2*α:ℝ):ℂ)+(y:ℂ)*Complex.I
        let s : ℂ := 1-(t:ℂ)*Complex.I+z
        mellin g z * (N:ℂ)^z *
          (-deriv (DirichletCharacter.LFunction χ) s /
            DirichletCharacter.LFunction χ s)
      Integrable F := by
  obtain ⟨α₀, hα₀, hpointAll⟩ := m2_actual_right_kernel_pointwise
  refine ⟨α₀, hα₀, ?_⟩
  intro α hα hαmax hα1 q _ χ N a b ε t j
    hN ha hab hb hε hεmax hj
  dsimp only
  let g : ℝ → ℂ := fun u =>
    ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
  let F : ℝ → ℂ := fun y =>
    let z : ℂ := ((2*α:ℝ):ℂ) + (y:ℂ)*Complex.I
    let s : ℂ := 1-(t:ℂ)*Complex.I + z
    mellin g z * (N:ℂ)^z *
      (-deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s)
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  let C : ℝ := B * N^(2*α) * (2/α^2)
  have hNpos : 0 < N := by linarith
  have hg : Continuous g :=
    Complex.continuous_ofReal.comp
      (smoothIntervalWeight_contDiff a b ε).continuous
  have hsup : ∀ u : ℝ, u < 1/2 ∨ 3 < u → g u = 0 := by
    intro u hu
    change ((smoothIntervalWeight a b ε u : ℝ) : ℂ) = 0
    have hs := smoothIntervalWeight_support a b ε u
      ha hb hε (by linarith : ε ≤ 1/2)
      (by
        rcases hu with h1 | h2
        · exact fun hh => (not_lt_of_ge hh.1) h1
        · exact fun hh => (not_lt_of_ge hh.2) h2)
    simp [hs]
  have hcont : Continuous F :=
    m2_right_kernel_continuous q χ g hg hsup N α t hNpos hα
  have hC : 0 ≤ C := by
    dsimp [C, B]
    have hc := sourceCutoffDerivConst_ge_one j
    positivity
  have hr : (1:ℝ) < (j:ℝ) := by
    exact_mod_cast (show 1 < j by omega)
  have hpoint : ∀ y : ℝ, ‖F y‖ ≤
      C * (1+|y|)^(-(j:ℝ)) := by
    intro y
    have hm := hpointAll α hα hαmax hα1 q χ N a b ε t y j
      hN ha hab hb hε hεmax
    change ‖F y‖ ≤ B/(1+|y|)^j * N^(2*α) * (2/α^2) at hm
    have hpos : 0 < 1+|y| := by positivity
    have hrpow : (1+|y|)^(-(j:ℝ)) = 1/(1+|y|)^j := by
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
      exact (one_div _).symm
    calc
      ‖F y‖ ≤ B/(1+|y|)^j * N^(2*α) * (2/α^2) := hm
      _ = C * (1+|y|)^(-(j:ℝ)) := by
        rw [hrpow]
        dsimp [C]
        ring
  exact m2_polynomial_complex_integrable F j C hr hC hcont hpoint

end Green64Analytic.LongPrime

-- END M2ActualFullLine

-- BEGIN P2LogRemoval

open Finset
namespace Green64Analytic.LongPrime

noncomputable def inverseLogProfile (N : ℝ) (i : ℕ) : ℝ :=
  (Real.log (max N (i : ℝ)))⁻¹

theorem inverseLogProfile_nonneg (N : ℝ) (hN : 1 < N) (i : ℕ) :
    0 ≤ inverseLogProfile N i := by
  unfold inverseLogProfile
  exact le_of_lt (inv_pos.mpr
    (Real.log_pos (lt_of_lt_of_le hN (le_max_left N (i : ℝ)))))

theorem inverseLogProfile_antitone (N : ℝ) (hN : 1 < N) (i : ℕ) :
    inverseLogProfile N (i+1) ≤ inverseLogProfile N i := by
  unfold inverseLogProfile
  have hi : 0 < max N (i : ℝ) :=
    lt_of_lt_of_le (by linarith : (0:ℝ) < N) (le_max_left N (i : ℝ))
  have hnext : max N (i : ℝ) ≤ max N ((i+1 : ℕ) : ℝ) :=
    max_le_max_left N (by exact_mod_cast Nat.le_succ i)
  exact inv_anti₀ (Real.log_pos (lt_of_lt_of_le hN (le_max_left N (i : ℝ))))
    (Real.log_le_log hi hnext)

theorem inverseLogProfile_zero (N : ℝ) (hN : 1 < N) :
    inverseLogProfile N 0 = (Real.log N)⁻¹ := by
  unfold inverseLogProfile
  simp [max_eq_left (show (0:ℝ) ≤ N by linarith)]

theorem p2_log_removal
    (c : ℕ → ℂ) (N E : ℝ) (n : ℕ)
    (hN : 1 < N) (hE : 0 ≤ E)
    (hsupport : ∀ i, i < n → c i ≠ 0 → N ≤ (i : ℝ))
    (hprefix : ∀ k, k ≤ n →
      ‖∑ i ∈ Finset.range k, ((Real.log (i : ℝ) : ℝ) : ℂ) * c i‖ ≤ E) :
    ‖∑ i ∈ Finset.range n, c i‖ ≤ E / Real.log N := by
  let w := inverseLogProfile N
  have hw₀ : w 0 = (Real.log N)⁻¹ :=
    inverseLogProfile_zero N hN
  have hAbel : ‖∑ i ∈ Finset.range n,
      (w i : ℂ) * (((Real.log (i : ℝ) : ℝ) : ℂ) * c i)‖ ≤ E * w 0 := by
    apply p2_abel_complex_prefix_bound
      (fun i => ((Real.log (i : ℝ) : ℝ) : ℂ) * c i) w n E
    · exact hE
    · exact inverseLogProfile_nonneg N hN 0
    · intro i _
      exact inverseLogProfile_antitone N hN i
    · intro _; exact inverseLogProfile_nonneg N hN _
    · exact hprefix
  have hterms : ∀ i ∈ Finset.range n,
      (w i : ℂ) * (((Real.log (i : ℝ) : ℝ) : ℂ) * c i) = c i := by
    intro i hi
    by_cases hc : c i = 0
    · simp [hc]
    have hiN : N ≤ (i : ℝ) := hsupport i (Finset.mem_range.mp hi) hc
    have hlog : Real.log (i : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (lt_of_lt_of_le hN hiN))
    have hwi : w i = (Real.log (i : ℝ))⁻¹ := by
      simp [w, inverseLogProfile, max_eq_right hiN]
    rw [hwi, ← mul_assoc, ← Complex.ofReal_mul]
    rw [inv_mul_cancel₀ hlog]
    simp
  have hEq : (∑ i ∈ Finset.range n,
    (w i : ℂ) * (((Real.log (i : ℝ) : ℝ) : ℂ) * c i)) =
      ∑ i ∈ Finset.range n, c i :=
    Finset.sum_congr rfl hterms
  rw [hEq, hw₀] at hAbel
  simpa [div_eq_mul_inv] using hAbel

end Green64Analytic.LongPrime

-- END P2LogRemoval

-- BEGIN P2SourcePrimes

namespace Green64Analytic.LongPrime
open Finset

noncomputable def sourcePrimeTerm
    (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ) (p : ℕ) : ℂ :=
  χ (p : ZMod q) * (p : ℂ)^((-1 : ℂ) + (t : ℂ)*Complex.I)

noncomputable def sourcePrimeCoeff
    (q : ℕ) (χ : DirichletCharacter ℂ q) (I : Set ℝ) (t : ℝ) (p : ℕ) : ℂ :=
  by classical exact if p.Prime ∧ (p : ℝ) ∈ I then sourcePrimeTerm q χ t p else 0

theorem p2_source_prime_prefix
    (q : ℕ) (χ : DirichletCharacter ℂ q) (N E t : ℝ) (I : Set ℝ)
    (hN : 1 < N) (hE : 0 ≤ E)
    (hI : I ⊆ Set.Icc N (2*N))
    (hprefix : ∀ k : ℕ, k ≤ ⌊2*N⌋₊ + 1 →
      ‖∑ p ∈ Finset.range k, ((Real.log (p : ℝ) : ℝ) : ℂ) *
        sourcePrimeCoeff q χ I t p‖ ≤ E) :
    ‖∑ p ∈ (@Finset.filter ℕ (fun p => (p : ℝ) ∈ I)
      (fun _ => Classical.propDecidable _)
      ((Finset.range (⌊2*N⌋₊ + 1)).filter Nat.Prime)),
      sourcePrimeTerm q χ t p‖ ≤
        E / Real.log N := by
  classical
  let c : ℕ → ℂ := sourcePrimeCoeff q χ I t
  have hsupport : ∀ i, i < ⌊2*N⌋₊ + 1 → c i ≠ 0 → N ≤ (i : ℝ) := by
    intro i _ hc
    by_cases hm : i.Prime ∧ (i : ℝ) ∈ I
    · exact (hI hm.2).1
    · have : c i = 0 := by simp [c, sourcePrimeCoeff, hm]
      exact False.elim (hc this)
  have hbound := p2_log_removal c N E (⌊2*N⌋₊ + 1) hN hE
      hsupport (by simpa [c] using hprefix)
  have hEq :
      (∑ p ∈ Finset.range (⌊2*N⌋₊ + 1), c p) =
      (∑ p ∈ (@Finset.filter ℕ (fun p => (p : ℝ) ∈ I)
        (fun _ => Classical.propDecidable _)
        ((Finset.range (⌊2*N⌋₊ + 1)).filter Nat.Prime)),
        sourcePrimeTerm q χ t p) := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hprime : p.Prime
    · by_cases hmem : (p : ℝ) ∈ I
      · simp [c, sourcePrimeCoeff, hprime, hmem]
      · simp [c, sourcePrimeCoeff, hprime, hmem]
    · simp [c, sourcePrimeCoeff, hprime]
  rw [← hEq]
  exact hbound

end Green64Analytic.LongPrime

-- END P2SourcePrimes

-- BEGIN P1PrimePowerPointwise

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction

/-- Prime-power error: the actual twisted Lambda term has no larger
pointwise mass than its untwisted Lambda coefficient, uniformly in χ,t. -/
theorem p1_actual_twisted_mangoldt_pointwise
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N t : ℝ) (n : ℕ)
    (hN : 0 < N) (hn : N ≤ (n:ℝ)) :
    ‖χ (n : ZMod q) * (Λ n : ℂ) *
       (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)‖ ≤ (Λ n) / N := by
  have hnpos : 0 < (n:ℝ) := lt_of_lt_of_le hN hn
  have hchi : ‖χ (n : ZMod q)‖ ≤ 1 := χ.norm_le_one n
  have hΛpos : 0 ≤ Λ n := vonMangoldt_nonneg
  have hΛnorm : ‖(Λ n : ℂ)‖ = Λ n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛpos]
  have hpow : ‖(n:ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)‖ = 1/(n:ℝ) := by
    change ‖((n:ℝ):ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)‖ = 1/(n:ℝ)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    have hre : ((-1:ℂ)+(t:ℂ)*Complex.I).re = -1 := by simp
    rw [hre, Real.rpow_neg_one]
    ring
  have hninv : 1/(n:ℝ) ≤ 1/N := one_div_le_one_div_of_le hN hn
  calc
    ‖χ (n : ZMod q) * (Λ n : ℂ) *
        (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)‖ =
      ‖χ (n : ZMod q)‖ * (Λ n) * (1/(n:ℝ)) := by
        rw [norm_mul, norm_mul, hΛnorm, hpow]
    _ ≤ 1 * (Λ n) * (1/(n:ℝ)) := by
        gcongr
    _ ≤ 1 * (Λ n) * (1/N) := by
        gcongr
    _ = (Λ n)/N := by ring

end Green64Analytic.LongPrime

-- END P1PrimePowerPointwise

-- BEGIN P1PrimePowerFinset

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction

/-- Genuine prime-power loss for every subset of the source interval,
every Dirichlet character, every real height and every modulus,
without a prime polynomial estimate. -/
theorem p1_prime_power_actual_complex_finset
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N t : ℝ) (x : ℕ) (S : Finset ℕ)
    (hN : 0 < N) (hx : 1 ≤ x)
    (hS : S ⊆ (Finset.Ioc 0 x).filter (fun n : ℕ => ¬n.Prime))
    (hLow : ∀ n ∈ S, N ≤ (n:ℝ)) :
    ‖∑ n ∈ S, χ (n : ZMod q) * (Λ n : ℂ) *
       (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (2*Real.sqrt (x:ℝ)*Real.log (x:ℝ))/N := by
  classical
  let T : Finset ℕ :=
    (Finset.Ioc 0 x).filter (fun n : ℕ => ¬n.Prime)
  have hMono : (∑ n ∈ S, Λ n) ≤ ∑ n ∈ T, Λ n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun n _ _ => vonMangoldt_nonneg)
  have hCheb : (∑ n ∈ T, Λ n) =
     Chebyshev.psi (x:ℝ) - Chebyshev.theta (x:ℝ) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,
      Nat.floor_natCast]
  calc
    ‖∑ n ∈ S, χ (n : ZMod q) * (Λ n : ℂ) *
         (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      ∑ n ∈ S, ‖χ (n : ZMod q) * (Λ n : ℂ) *
         (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)‖ :=
           norm_sum_le _ _
    _ ≤ ∑ n ∈ S, (Λ n)/N := by
          apply Finset.sum_le_sum
          intro n hn
          exact p1_actual_twisted_mangoldt_pointwise q χ N t n
            hN (hLow n hn)
    _ = (∑ n ∈ S, Λ n)/N := by rw [Finset.sum_div]
    _ ≤ (∑ n ∈ T, Λ n)/N :=
          div_le_div_of_nonneg_right hMono hN.le
    _ = (Chebyshev.psi (x:ℝ) - Chebyshev.theta (x:ℝ))/N :=
          congrArg (· / N) hCheb
    _ ≤ (2*Real.sqrt (x:ℝ)*Real.log (x:ℝ))/N := by
          exact div_le_div_of_nonneg_right
            (Chebyshev.psi_sub_theta_le (by exact_mod_cast hx)) hN.le

end Green64Analytic.LongPrime

-- END P1PrimePowerFinset

-- BEGIN M2SourceWholeRightLine

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open MeasureTheory Set

/-- Exactly the uniform zero-free region used in Khale's source
contour argument (the only external number-theoretic input here). -/
noncomputable def SourceKhaleZeroFree : Prop :=
  let D : ℝ → ℝ → ℝ := fun Q v =>
    10.5 * Real.log Q +
    61.5 * (Real.log |v|) ^ (2/3:ℝ) *
      (Real.log (Real.log |v|)) ^ (1/3:ℝ)
  ∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
    3 ≤ Q → 10 ≤ |s.im| → 1 - (D Q s.im)⁻¹ ≤ s.re →
      DirichletCharacter.LFunction χ s ≠ 0

/-- Complete whole-line M2 analytic estimate: actual L'/L, actual
smooth cutoff, actual vertical and horizontal edges, and both
infinite right-line tails, with all source scales.
No prime-polynomial or source P1 hypothesis is assumed. -/
theorem m2_source_actual_whole_rightline_bound
    (hKhale : SourceKhaleZeroFree) :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ C C₅ : ℝ, 0 < C → 0 ≤ C₅ →
      ∃ L₀ : ℝ, 3 ≤ L₀ ∧
        ∀ L : ℝ, L₀ ≤ L →
          let Q : ℝ := 3*L^C
          let V : ℝ := 3*Real.exp (3*L)
          let D : ℝ := 10.5*Real.log Q +
            61.5*(Real.log V)^(2/3:ℝ) *
              (Real.log (Real.log V))^(1/3:ℝ)
          let δ : ℝ := (100*D)⁻¹
          let H : ℝ := L^C₅
          let right : ℝ := L⁻¹
          ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
            (q:ℝ) ≤ L^C →
          ∀ (η N a b ε t : ℝ) (j : ℕ),
            1 ≤ N → N ≤ (Real.exp L)^η →
            1 ≤ a → a ≤ b → b ≤ 2 →
            0 < ε → ε ≤ 1/4 →
            L^(C₅+3) ≤ |t| → |t| ≤ (Real.exp L)^2 →
            2 ≤ j →
            let g : ℝ → ℂ :=
              fun u => ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
            let F : ℝ → ℂ := fun y =>
              let z : ℂ := ((right:ℝ):ℂ)+(y:ℂ)*Complex.I
              let s : ℂ := 1-(t:ℂ)*Complex.I+z
              mellin g z * (N:ℂ)^z *
                (-deriv (DirichletCharacter.LFunction χ) s /
                  DirichletCharacter.LFunction χ s)
            let B : ℝ :=
              20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
            let R : ℝ :=
              B * Real.exp η * (8*L^2) *
                (-H^(1-(j:ℝ))/(1-(j:ℝ)))
            ‖∫ y : ℝ, F y‖ ≤
              2*H*(B*N^(-δ)*(3*50*L)) +
                2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) +
                2*R := by
  obtain ⟨αT,hαT,hTails⟩ := m2_actual_source_right_tails_on_log_scale
  obtain ⟨αI,hαI,hIntegrable⟩ := m2_actual_right_source_integrable
  have hα₀ : 0 < min αT αI := lt_min hαT hαI
  refine ⟨min αT αI, hα₀, ?_⟩
  intro C C₅ hC hC₅
  have hKh : (let D : ℝ → ℝ → ℝ := fun Q v =>
      10.5 * Real.log Q +
      61.5 * (Real.log |v|) ^ (2/3:ℝ) *
       (Real.log (Real.log |v|)) ^ (1/3:ℝ);
      ∀ (Q : ℕ) [NeZero Q] (χ : DirichletCharacter ℂ Q) (s : ℂ),
        3 ≤ Q → 10 ≤ |s.im| → 1-(D Q s.im)⁻¹ ≤ s.re →
          DirichletCharacter.LFunction χ s ≠ 0) := hKhale
  obtain ⟨δ₀, hδ₀, hKhaleParam⟩ :=
    m2_source_khale_truncated_parameters hKh
  obtain ⟨Lbase,hLbase,hTruncAll⟩ :=
    hKhaleParam C C₅ hC hC₅
  let α₀ : ℝ := min αT αI
  let L₀ : ℝ := max Lbase α₀⁻¹
  have hL₀ : 3 ≤ L₀ := hLbase.trans (le_max_left _ _)
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL Q V D δ H right q _ χ hq
    η N a b ε t j hN hNmax ha hab hb hε hεmax htlo hthi hj
  dsimp only
  have hLbase' : Lbase ≤ L :=
    (le_max_left _ _).trans hL
  have hLP' : α₀⁻¹ ≤ L :=
    (le_max_right _ _).trans hL
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<3)
    (hL₀.trans hL)
  have hshiftPos : 0 < L⁻¹ := inv_pos.mpr hLp
  have hshift1 : L⁻¹ ≤ 1 := by
    have haux : 1/L ≤ 1/(1:ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    simpa only [one_div, inv_one] using haux
  have hInvSmall : L⁻¹ ≤ α₀ := by
    have haux : 1/L ≤ 1/(α₀⁻¹) :=
      one_div_le_one_div_of_le (inv_pos.mpr hα₀) hLP'
    simpa [one_div] using haux
  let α : ℝ := L⁻¹/2
  have hαp : 0 < α := half_pos hshiftPos
  have hαless : α < α₀ := by
    dsimp [α]
    linarith
  have hαT' : α < αT := hαless.trans_le (min_le_left _ _)
  have hαI' : α < αI := hαless.trans_le (min_le_right _ _)
  have htwo : 2*α = right := by
    dsimp [α, right]
    ring
  have htwo1 : 2*α ≤ 1 := by rw [htwo]; exact hshift1
  have hHpos : 0 < H := by
    dsimp [H]
    exact Real.rpow_pos_of_pos hLp C₅
  let g : ℝ → ℂ :=
    fun u => ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
  let F : ℝ → ℂ := fun y =>
    let z : ℂ := ((right:ℝ):ℂ)+(y:ℂ)*Complex.I
    let s : ℂ := 1-(t:ℂ)*Complex.I+z
    mellin g z * (N:ℂ)^z *
      (-deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s)
  let B : ℝ :=
    20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  let R : ℝ :=
    B * Real.exp η * (8*L^2) *
      (-H^(1-(j:ℝ))/(1-(j:ℝ)))
  have hInt : Integrable F := by
    have hh := hIntegrable α hαp hαI' htwo1 q χ
      N a b ε t j hN ha hab hb hε hεmax hj
    simpa only [htwo] using hh
  have hT := hTails L η N a b ε t H j
    (by linarith : 1 ≤ L) hN hNmax ha hab hb hε hεmax
    hHpos hj hshift1 hαT' q χ
  have hTailBounds :
      (‖∫ y : ℝ in Set.Ioi H, F y‖ ≤ R) ∧
      (‖∫ y : ℝ in Set.Iio (-H), F y‖ ≤ R) := by
    have htwor : 2 * (L⁻¹ / 2) = right := by
      dsimp [right]
      ring
    simpa only [F, R, B, g, htwor] using hT
  obtain ⟨hTailR,hTailL⟩ := hTailBounds
  have hTrunc :
      ‖∫ y in (-H)..H, F y‖ ≤
        2*H*(B*N^(-δ)*(3*50*L)) +
        2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) := by
    have hh := hTruncAll L hLbase' q χ hq
      N a b ε t j hN ha hab hb hε hεmax htlo hthi
    simpa only using hh
  have hAllNorm := m2_whole_line_norm_le_three
    F H hHpos.le hInt
  linarith

end Green64Analytic.LongPrime

-- END M2SourceWholeRightLine

-- BEGIN M2ActualSmoothTransfer

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction MeasureTheory
open scoped LSeries.notation

/-- Transfer a proved whole-line Mellin estimate to the genuine source
weighted von Mangoldt sum, using native kernel-checked Mellin inversion.
The only quantitative input is the exact right-line norm bound. -/
theorem m2_actual_smooth_mangoldt_transfer
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N a b ε σ t M : ℝ)
    (hN : 0 < N) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hε : 0 < ε) (hεmax : ε ≤ 1/4)
    (hσ : 0 < σ) (hσmax : σ ≤ 1)
    (hM : 0 ≤ M)
    (hwhole :
      let g : ℝ → ℂ := fun u =>
        ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
      let F : ℝ → ℂ := fun y =>
        let z : ℂ := (σ:ℂ)+(y:ℂ)*Complex.I
        let s : ℂ := 1-(t:ℂ)*Complex.I+z
        mellin g z * (N:ℂ)^z *
          (-deriv (DirichletCharacter.LFunction χ) s /
            DirichletCharacter.LFunction χ s)
      ‖∫ y : ℝ, F y‖ ≤ M) :
    let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
      (fun k : ℕ => (Λ k : ℂ))
    let s₀ : ℂ := 1-(t:ℂ)*Complex.I
    let g : ℝ → ℂ := fun u =>
      ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
    ‖∑' n : ℕ, LSeries.term f s₀ (n+1) *
       g (((n+1:ℕ):ℝ)/N)‖ ≤ M/(2*Real.pi) := by
  dsimp only
  let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
      (fun k : ℕ => (Λ k : ℂ))
  let s₀ : ℂ := 1-(t:ℂ)*Complex.I
  let g : ℝ → ℂ := fun u =>
    ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
  let F : ℝ → ℂ := fun y =>
    let z : ℂ := (σ:ℂ)+(y:ℂ)*Complex.I
    let s : ℂ := 1-(t:ℂ)*Complex.I+z
    mellin g z * (N:ℂ)^z *
      (-deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s)
  have hformula :=
    actual_smooth_cutoff_twisted_mangoldt_formula
      q χ N a b ε σ t hN ha hab hb hε hεmax hσ hσmax
  dsimp only at hformula
  have hIntegrals :
    (∫ y : ℝ,
      (N:ℂ)^((σ:ℂ)+(y:ℂ)*Complex.I) *
      (-(deriv (DirichletCharacter.LFunction χ)
        (s₀+((σ:ℂ)+(y:ℂ)*Complex.I))) /
       DirichletCharacter.LFunction χ
        (s₀+((σ:ℂ)+(y:ℂ)*Complex.I))) *
        mellin g ((σ:ℂ)+(y:ℂ)*Complex.I)) =
      ∫ y : ℝ, F y := by
    apply integral_congr_ae
    filter_upwards [] with y
    change (N:ℂ)^((σ:ℂ)+(y:ℂ)*Complex.I) *
      (-deriv (DirichletCharacter.LFunction χ)
        (s₀+((σ:ℂ)+(y:ℂ)*Complex.I)) /
       DirichletCharacter.LFunction χ
        (s₀+((σ:ℂ)+(y:ℂ)*Complex.I))) *
        mellin g ((σ:ℂ)+(y:ℂ)*Complex.I) =
      F y
    dsimp [F, s₀]
    ring
  rw [hIntegrals] at hformula
  have hfactor : ‖((1/(2*Real.pi):ℝ):ℂ)‖ =
        1/(2*Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (1/(2*Real.pi):ℝ))]
  have hnorm : ‖∑' n : ℕ, LSeries.term f s₀ (n+1) *
        g (((n+1:ℕ):ℝ)/N)‖ ≤
      (1/(2*Real.pi))*M := by
    rw [hformula, norm_mul]
    have hcast : (1/(2*(Real.pi:ℂ))) =
      ((1/(2*Real.pi):ℝ):ℂ) := by push_cast; ring
    rw [hcast, hfactor]
    exact mul_le_mul_of_nonneg_left hwhole (by positivity)
  convert hnorm using 1 <;> ring

end Green64Analytic.LongPrime

-- END M2ActualSmoothTransfer

-- BEGIN M2SourceSmoothSum

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction MeasureTheory

/-- The source-scaled *actual* smoothed, twisted von Mangoldt sum.
This is the output of the full M1+M2 synthesis, conditional only on
the exact classical Khale zero-free region. -/
theorem m2_source_actual_smooth_mangoldt_bound
    (hKhale : SourceKhaleZeroFree) :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ C C₅ : ℝ, 0 < C → 0 ≤ C₅ →
      ∃ L₀ : ℝ, 3 ≤ L₀ ∧
        ∀ L : ℝ, L₀ ≤ L →
          let Q : ℝ := 3*L^C
          let V : ℝ := 3*Real.exp (3*L)
          let D : ℝ := 10.5*Real.log Q +
            61.5*(Real.log V)^(2/3:ℝ) *
              (Real.log (Real.log V))^(1/3:ℝ)
          let δ : ℝ := (100*D)⁻¹
          let H : ℝ := L^C₅
          let right : ℝ := L⁻¹
          ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
            (q:ℝ) ≤ L^C →
          ∀ (η N a b ε t : ℝ) (j : ℕ),
            1 ≤ N → N ≤ (Real.exp L)^η →
            1 ≤ a → a ≤ b → b ≤ 2 →
            0 < ε → ε ≤ 1/4 →
            L^(C₅+3) ≤ |t| → |t| ≤ (Real.exp L)^2 →
            2 ≤ j →
            let g : ℝ → ℂ :=
              fun u => ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
            let f : ℕ → ℂ :=
              (fun k : ℕ => χ (k : ZMod q)) *
              (fun k : ℕ => (Λ k : ℂ))
            let s₀ : ℂ := 1-(t:ℂ)*Complex.I
            let B : ℝ :=
              20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
            let R : ℝ :=
              B * Real.exp η * (8*L^2) *
                (-H^(1-(j:ℝ))/(1-(j:ℝ)))
            let M : ℝ :=
              2*H*(B*N^(-δ)*(3*50*L)) +
                2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) +
                2*R
            ‖∑' n : ℕ, LSeries.term f s₀ (n+1) *
               g (((n+1:ℕ):ℝ)/N)‖ ≤ M/(2*Real.pi) := by
  obtain ⟨α₀,hα₀,hWholeAll⟩ :=
    m2_source_actual_whole_rightline_bound hKhale
  refine ⟨α₀,hα₀,?_⟩
  intro C C₅ hC hC₅
  obtain ⟨L₀,hL₀,hWhole⟩ := hWholeAll C C₅ hC hC₅
  refine ⟨L₀,hL₀,?_⟩
  intro L hL Q V D δ H right q _ χ hq
    η N a b ε t j hN hNmax ha hab hb hε hεmax htlo hthi hj
  dsimp only
  let g : ℝ → ℂ := fun u =>
    ((smoothIntervalWeight a b ε u : ℝ) : ℂ)
  let f : ℕ → ℂ :=
    (fun k : ℕ => χ (k : ZMod q)) *
    (fun k : ℕ => (Λ k : ℂ))
  let s₀ : ℂ := 1-(t:ℂ)*Complex.I
  let B : ℝ :=
    20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  let R : ℝ :=
    B * Real.exp η * (8*L^2) *
      (-H^(1-(j:ℝ))/(1-(j:ℝ)))
  let M : ℝ :=
    2*H*(B*N^(-δ)*(3*50*L)) +
      2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) +
        2*R
  let F : ℝ → ℂ := fun y =>
    let z : ℂ := ((right:ℝ):ℂ)+(y:ℂ)*Complex.I
    let s : ℂ := 1-(t:ℂ)*Complex.I+z
    mellin g z * (N:ℂ)^z *
      (-deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s)
  have hIntBound : ‖∫ y : ℝ, F y‖ ≤ M := by
    have h := hWhole L hL q χ hq
      η N a b ε t j hN hNmax ha hab hb hε hεmax htlo hthi hj
    simpa only using h
  have hM : 0 ≤ M := (norm_nonneg _).trans hIntBound
  have hσpos : 0 < right := by
    dsimp [right]
    have : 0 < L := by linarith
    positivity
  have hσmax : right ≤ 1 := by
    dsimp [right]
    have h1 : 1 ≤ L := by linarith
    have hh : 1/L ≤ 1/(1:ℝ) :=
      one_div_le_one_div_of_le (by norm_num) h1
    simpa only [one_div, inv_one] using hh
  have hTransfer :=
    m2_actual_smooth_mangoldt_transfer
      q χ N a b ε right t M
      (by linarith) ha hab hb hε hεmax hσpos hσmax
      hM hIntBound
  simpa only using hTransfer

end Green64Analytic.LongPrime

-- END M2SourceSmoothSum

-- BEGIN P1FiniteSmoothIdentity

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction

/-- The actual smooth, twisted Mangoldt series has finite support. -/
theorem p1_actual_smooth_tsum_eq_finite
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N a b ε t : ℝ) (K : ℕ)
    (hN : 0 < N) (ha : 1 ≤ a) (hb : b ≤ 2)
    (hε : 0 < ε) (hεmax : ε ≤ 1/4)
    (hK : 3*N ≤ (K : ℝ)) :
    let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
      (fun k : ℕ => (Λ k : ℂ))
    let s₀ : ℂ := 1-(t:ℂ)*Complex.I
    let g : ℝ → ℂ := fun u => (smoothIntervalWeight a b ε u : ℝ)
    (∑' n : ℕ, LSeries.term f s₀ (n+1) *
      g (((n+1:ℕ):ℝ)/N)) =
    ∑ n ∈ Finset.range K, LSeries.term f s₀ (n+1) *
      g (((n+1:ℕ):ℝ)/N) := by
  dsimp only
  classical
  apply tsum_eq_sum
  intro n hn
  have hnK : K ≤ n := Nat.le_of_not_lt (by
    simpa only [Finset.mem_range] using hn)
  have hnReal : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnK
  have hu : 3 < ((n+1:ℕ):ℝ)/N := by
    apply (lt_div_iff₀ hN).mpr
    push_cast
    linarith
  have hnot : ((n+1:ℕ):ℝ)/N ∉ Set.Icc (1/2 : ℝ) 3 := by
    intro h
    exact (not_lt_of_ge h.2) hu
  have hg := smoothIntervalWeight_support a b ε
    (((n+1:ℕ):ℝ)/N) ha hb hε (by linarith) hnot
  simp only [hg, Complex.ofReal_zero, mul_zero]

end Green64Analytic.LongPrime

-- END P1FiniteSmoothIdentity

-- BEGIN P1LSeriesTerm

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction

/-- Exact unsmoothed complex coefficient of the genuine L-series at 1-it. -/
theorem p1_actual_lseries_term
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) :
    LSeries.term
      ((fun k : ℕ => χ (k : ZMod q)) * (fun k : ℕ => (Λ k : ℂ)))
      (1-(t:ℂ)*Complex.I) n =
    χ (n : ZMod q) * (Λ n : ℂ) *
      (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I) := by
  let f : ℕ → ℂ :=
    (fun k : ℕ => χ (k : ZMod q)) * (fun k : ℕ => (Λ k : ℂ))
  have hf : f 0 = 0 := by simp [f]
  have hex : -((1:ℂ)-(t:ℂ)*Complex.I) =
      (-1:ℂ)+(t:ℂ)*Complex.I := by ring
  change LSeries.term f (1-(t:ℂ)*Complex.I) n = _
  rw [LSeries.term_def₀ hf, hex]
  rfl

end Green64Analytic.LongPrime

-- END P1LSeriesTerm

-- BEGIN P1CollarCoefficient

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction

/-- On either ε-collar of a source interval, actual twisted Λ mass
is O(log(3N)/N), not the inadmissible constant bound. -/
theorem p1_twisted_mangoldt_collar_pointwise
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N a b ε t : ℝ) (n : ℕ)
    (hN : 0 < N) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hε : 0 < ε) (hεmax : ε ≤ 1/4)
    (hcollar : (a-ε < (n:ℝ)/N ∧ (n:ℝ)/N < a) ∨
               (b < (n:ℝ)/N ∧ (n:ℝ)/N < b+ε)) :
    ‖χ (n : ZMod q) * (Λ n : ℂ) *
      (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)‖ ≤
    (2*Real.log (3*N))/N := by
  have hratioLo : (1/2 : ℝ) ≤ (n:ℝ)/N := by
    rcases hcollar with h | h <;> linarith
  have hratioHi : (n:ℝ)/N ≤ (3 : ℝ) := by
    rcases hcollar with h | h <;> linarith
  have hnLo : N/2 ≤ (n:ℝ) := by
    nlinarith [(le_div_iff₀ hN).mp hratioLo]
  have hnHi : (n:ℝ) ≤ 3*N :=
    (div_le_iff₀ hN).mp hratioHi
  have hNhalf : 0 < N/2 := by positivity
  have hnPos : 0 < (n:ℝ) := lt_of_lt_of_le hNhalf hnLo
  have hlog : Λ n ≤ Real.log (3*N) := by
    exact (vonMangoldt_le_log : Λ n ≤ Real.log (n:ℝ)).trans
      (Real.log_le_log hnPos hnHi)
  have hbase := p1_actual_twisted_mangoldt_pointwise q χ
    (N/2) t n hNhalf hnLo
  calc
    ‖χ (n : ZMod q) * (Λ n : ℂ) *
      (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)‖ ≤ Λ n/(N/2) := hbase
    _ ≤ Real.log (3*N)/(N/2) :=
       div_le_div_of_nonneg_right hlog hNhalf.le
    _ = (2*Real.log (3*N))/N := by
      field_simp

end Green64Analytic.LongPrime

-- END P1CollarCoefficient

-- BEGIN P1SharpFromSmooth

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction
open scoped Classical

/-- Sharp, arbitrary finite interval coefficient control from a
genuinely smoothed Mangoldt estimate, with the correct small collar cost. -/
theorem p1_actual_sharp_from_smooth
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) (I : Set ℝ)
    (N a b ε t E : ℝ)
    (hN : 1 ≤ N) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hε : 0 < ε) (hεmax : ε ≤ 1/4)
    (hExact : ∀ n ∈ S, ((n : ℝ) ∈ I ↔
      a ≤ (n:ℝ)/N ∧ (n:ℝ)/N ≤ b))
    (hSmooth :
      ‖∑ n ∈ S, (χ (n : ZMod q) * (Λ n : ℂ) *
        (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) *
        ((smoothIntervalWeight a b ε ((n:ℝ)/N) : ℝ):ℂ)‖ ≤ E) :
    ‖∑ n ∈ S, if (n:ℝ) ∈ I then
      χ (n : ZMod q) * (Λ n : ℂ) *
        (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I) else 0‖ ≤
       E + (2*Real.log (3*N)/N)*(2*ε*N+2) := by
  classical
  let c : ℕ → ℂ := fun n =>
    χ (n : ZMod q) * (Λ n : ℂ) *
      (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)
  let g : ℕ → ℂ := fun n =>
    (smoothIntervalWeight a b ε ((n:ℝ)/N) : ℝ)
  let M := (2*Real.log (3*N))/N
  have hNp : 0 < N := by linarith
  have hM : 0 ≤ M := by
    dsimp [M]
    have hN3 : (1:ℝ) ≤ 3*N := by linarith
    exact div_nonneg
      (mul_nonneg (by norm_num) (Real.log_nonneg hN3)) hNp.le
  have hCoeff : ∀ n ∈ S,
      ((a-ε < (n:ℝ)/N ∧ (n:ℝ)/N < a) ∨
       (b < (n:ℝ)/N ∧ (n:ℝ)/N < b+ε)) → ‖c n‖ ≤ M := by
    intro n hn hcollar
    exact p1_twisted_mangoldt_collar_pointwise
      q χ N a b ε t n hNp ha hab hb hε hεmax hcollar
  have hColl := p1_localized_weighted_collar_error
    S I N ε a b M c hNp hε hab hExact hM hCoeff
  let sharp : ℂ := ∑ n ∈ S, if (n:ℝ) ∈ I then c n else 0
  let smooth : ℂ := ∑ n ∈ S, c n * g n
  have hEq : sharp = (sharp-smooth)+smooth := by ring
  change ‖sharp‖ ≤ E + M*(2*ε*N+2)
  rw [hEq]
  calc
    ‖(sharp-smooth)+smooth‖ ≤ ‖sharp-smooth‖ + ‖smooth‖ :=
      norm_add_le _ _
    _ ≤ M*(2*ε*N+2) + E := by
      apply add_le_add
      · simpa only [sharp, smooth, c, g] using hColl
      · simpa only [smooth, c, g] using hSmooth
    _ = E + M*(2*ε*N+2) := by ring

end Green64Analytic.LongPrime

-- END P1SharpFromSmooth

-- BEGIN P1PrimeLogSplit

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction
open scoped Classical

/-- Genuine prime contribution plus genuine prime-power remainder.
No analytic prime estimate is used in this exact finite identity. -/
theorem p1_actual_prime_log_split
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset ℕ) (I : Set ℝ) (t : ℝ) :
    (∑ n ∈ S, if n.Prime ∧ (n:ℝ) ∈ I then
      (Real.log (n:ℝ) : ℂ) *
      (χ (n : ZMod q) *
        (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) else 0) =
    (∑ n ∈ S, if (n:ℝ) ∈ I then
      χ (n : ZMod q) * (Λ n : ℂ) *
        (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I) else 0) -
    (∑ n ∈ S.filter (fun n : ℕ => ¬n.Prime ∧ (n:ℝ) ∈ I),
      χ (n : ZMod q) * (Λ n : ℂ) *
        (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) := by
  classical
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · by_cases hi : (n:ℝ) ∈ I
    · simp only [hp, hi, and_self, if_true, not_true_eq_false,
        false_and, if_false, sub_zero]
      rw [vonMangoldt_apply_prime hp]
      ring
    · simp [hp, hi]
  · by_cases hi : (n:ℝ) ∈ I
    · simp [hp, hi]
    · simp [hp, hi]

end Green64Analytic.LongPrime

-- END P1PrimeLogSplit

-- BEGIN P1PrimeLogBound

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction
open scoped Classical

/-- The genuine weighted prime polynomial is bounded by the
sharp von Mangoldt estimate plus a noncircular prime-power loss. -/
theorem p1_actual_prime_log_norm_le
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N t E : ℝ) (x : ℕ) (S : Finset ℕ) (I : Set ℝ)
    (hN : 1 ≤ N) (hx : 1 ≤ x)
    (hS : S ⊆ Finset.Ioc 0 x)
    (hI : I ⊆ Set.Icc N (2*N))
    (hSharp : ‖∑ n ∈ S, if (n:ℝ) ∈ I then
      χ (n : ZMod q) * (Λ n : ℂ) *
        (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I) else 0‖ ≤ E) :
    ‖∑ n ∈ S, if n.Prime ∧ (n:ℝ) ∈ I then
      (Real.log (n:ℝ) : ℂ) *
      (χ (n : ZMod q) *
        (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) else 0‖ ≤
    E + (2*Real.sqrt (x:ℝ)*Real.log (x:ℝ))/N := by
  classical
  let T : Finset ℕ :=
    S.filter (fun n : ℕ => ¬n.Prime ∧ (n:ℝ) ∈ I)
  have hTsub : T ⊆ (Finset.Ioc 0 x).filter (fun n : ℕ => ¬n.Prime) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnS,hnNon,hnI⟩
    exact Finset.mem_filter.mpr ⟨hS hnS,hnNon⟩
  have hLow : ∀ n ∈ T, N ≤ (n:ℝ) := by
    intro n hn
    exact (hI (Finset.mem_filter.mp hn).2.2).1
  have hNpos : 0 < N := by linarith
  have hPower := p1_prime_power_actual_complex_finset
    q χ N t x T hNpos hx hTsub hLow
  have hEq := p1_actual_prime_log_split q χ S I t
  rw [hEq]
  change ‖(∑ n ∈ S, if (n:ℝ) ∈ I then
      χ (n : ZMod q) * (Λ n : ℂ) *
        (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I) else 0) -
    (∑ n ∈ T, χ (n : ZMod q) * (Λ n : ℂ) *
      (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I))‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add hSharp hPower)

end Green64Analytic.LongPrime

-- END P1PrimeLogBound

-- BEGIN P1M2FiniteBridge

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction

/-- Turn the authentic M2 smooth Λ estimate into a finite, literal
twisted Mangoldt polynomial without adding a prime polynomial premise. -/
theorem p1_actual_m2_to_finite_smooth
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N a b ε t E : ℝ) (K : ℕ)
    (hN : 0 < N) (ha : 1 ≤ a) (hb : b ≤ 2)
    (hε : 0 < ε) (hεmax : ε ≤ 1/4)
    (hK : 3*N ≤ (K:ℝ))
    (hSmooth :
      let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
        (fun k : ℕ => (Λ k : ℂ))
      let s₀ : ℂ := 1-(t:ℂ)*Complex.I
      let g : ℝ → ℂ := fun u =>
        (smoothIntervalWeight a b ε u : ℝ)
      ‖∑' n : ℕ, LSeries.term f s₀ (n+1) *
        g (((n+1:ℕ):ℝ)/N)‖ ≤ E) :
    ‖∑ n ∈ Finset.range K,
      (χ ((n+1:ℕ) : ZMod q) * (Λ (n+1) : ℂ) *
        ((n+1:ℕ) : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) *
       ((smoothIntervalWeight a b ε (((n+1:ℕ):ℝ)/N) : ℝ):ℂ)‖ ≤ E := by
  have hFin := p1_actual_smooth_tsum_eq_finite
    q χ N a b ε t K hN ha hb hε hεmax hK
  dsimp only at hFin hSmooth
  rw [hFin] at hSmooth
  simp_rw [p1_actual_lseries_term q χ t] at hSmooth
  simpa only using hSmooth

end Green64Analytic.LongPrime

-- END P1M2FiniteBridge

-- BEGIN P1M2PositiveRange

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction
open scoped Classical

/-- Reindex the exact M2 finite sum over genuine positive integers. -/
theorem p1_actual_m2_to_positive_finite
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N a b ε t E : ℝ) (K : ℕ)
    (hN : 0 < N) (ha : 1 ≤ a) (hb : b ≤ 2)
    (hε : 0 < ε) (hεmax : ε ≤ 1/4)
    (hK : 3*N ≤ (K:ℝ))
    (hSmooth :
      let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
        (fun k : ℕ => (Λ k : ℂ))
      let s₀ : ℂ := 1-(t:ℂ)*Complex.I
      let g : ℝ → ℂ := fun u => (smoothIntervalWeight a b ε u : ℝ)
      ‖∑' n : ℕ, LSeries.term f s₀ (n+1) *
        g (((n+1:ℕ):ℝ)/N)‖ ≤ E) :
    ‖∑ n ∈ (Finset.range K).image Nat.succ,
      (χ (n : ZMod q) * (Λ n : ℂ) *
        (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) *
       ((smoothIntervalWeight a b ε ((n:ℝ)/N) : ℝ):ℂ)‖ ≤ E := by
  have hFin := p1_actual_m2_to_finite_smooth
    q χ N a b ε t E K hN ha hb hε hεmax hK hSmooth
  have hEq :
    (∑ n ∈ (Finset.range K).image Nat.succ,
      (χ (n : ZMod q) * (Λ n : ℂ) *
        (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) *
       ((smoothIntervalWeight a b ε ((n:ℝ)/N) : ℝ):ℂ)) =
    ∑ n ∈ Finset.range K,
      (χ ((n+1:ℕ) : ZMod q) * (Λ (n+1) : ℂ) *
        ((n+1:ℕ) : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) *
       ((smoothIntervalWeight a b ε (((n+1:ℕ):ℝ)/N) : ℝ):ℂ) := by
    rw [Finset.sum_image]
    intro i hi j hj heq
    exact Nat.succ_injective heq
  rw [hEq]
  exact hFin

end Green64Analytic.LongPrime

-- END P1M2PositiveRange

-- BEGIN P1AllIntervalsFromM2

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction
open scoped Classical

/-- Uniform M2 bounds for real smooth source cutoffs control *every*
sharp ordinary interval, including empty and singleton intersections. -/
theorem p1_all_intervals_from_actual_smooth_m2
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N ε t E : ℝ) (K : ℕ) (I : Set ℝ)
    (hN : 1 ≤ N) (hε : 0 < ε) (hεmax : ε ≤ 1/4)
    (hK : 3*N ≤ (K:ℝ))
    (hI : Set.OrdConnected I) (hIS : I ⊆ Set.Icc N (2*N))
    (hE : 0 ≤ E)
    (hSmoothAll : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2 →
      let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
        (fun k : ℕ => (Λ k : ℂ))
      let s₀ : ℂ := 1-(t:ℂ)*Complex.I
      let g : ℝ → ℂ := fun u => (smoothIntervalWeight a b ε u : ℝ)
      ‖∑' n : ℕ, LSeries.term f s₀ (n+1) *
        g (((n+1:ℕ):ℝ)/N)‖ ≤ E) :
    ‖∑ n ∈ (Finset.range K).image Nat.succ,
      if (n:ℝ) ∈ I then
        χ (n : ZMod q) * (Λ n : ℂ) *
          (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I) else 0‖ ≤
      E + (2*Real.log (3*N)/N)*(2*ε*N+2) := by
  classical
  let S : Finset ℕ := (Finset.range K).image Nat.succ
  have hNp : 0 < N := by linarith
  have hεhalf : ε ≤ 1/2 := by linarith
  have hcost :
      0 ≤ (2*Real.log (3*N)/N)*(2*ε*N+2) := by
    have hlog : 0 ≤ Real.log (3*N) :=
      Real.log_nonneg (by linarith : (1:ℝ) ≤ 3*N)
    apply mul_nonneg
    · exact div_nonneg (mul_nonneg (by norm_num) hlog) hNp.le
    · positivity
  by_cases hNE : ∃ n ∈ S, (n:ℝ) ∈ I
  · obtain ⟨a,b,ha,hab,hb,_,_,_,hExact,_,_⟩ :=
      smooth_finite_source_interval
        S I N ε hNp hε hεhalf hI hIS hNE
    have hSmooth := hSmoothAll a b ha hab hb
    have hFinite := p1_actual_m2_to_positive_finite
      q χ N a b ε t E K hNp ha hb hε hεmax hK hSmooth
    change ‖∑ n ∈ S, if (n:ℝ) ∈ I then
        χ (n : ZMod q) * (Λ n : ℂ) *
          (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I) else 0‖ ≤ _
    exact p1_actual_sharp_from_smooth q χ S I
      N a b ε t E hN ha hab hb hε hεmax hExact hFinite
  · have hzero :
        (∑ n ∈ S, if (n:ℝ) ∈ I then
          χ (n : ZMod q) * (Λ n : ℂ) *
            (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hi : (n:ℝ) ∉ I := by
        intro hm
        exact hNE ⟨n,hn,hm⟩
      simp only [if_neg hi]
    change ‖∑ n ∈ S, if (n:ℝ) ∈ I then
      χ (n : ZMod q) * (Λ n : ℂ) *
        (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I) else 0‖ ≤ _
    rw [hzero, norm_zero]
    linarith

end Green64Analytic.LongPrime

-- END P1AllIntervalsFromM2

-- BEGIN P1PrimeAllIntervals

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction
open scoped Classical

/-- Actual P1: uniform prime-log cancellation over an arbitrary
interval, with explicit smoothing and prime-power costs. -/
theorem p1_actual_prime_log_all_intervals
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N ε t E : ℝ) (K : ℕ) (I : Set ℝ)
    (hN : 1 ≤ N) (hε : 0 < ε) (hεmax : ε ≤ 1/4)
    (hK : 3*N ≤ (K:ℝ))
    (hI : Set.OrdConnected I) (hIS : I ⊆ Set.Icc N (2*N))
    (hE : 0 ≤ E)
    (hSmoothAll : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2 →
      let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
        (fun k : ℕ => (Λ k : ℂ))
      let s₀ : ℂ := 1-(t:ℂ)*Complex.I
      let g : ℝ → ℂ := fun u => (smoothIntervalWeight a b ε u : ℝ)
      ‖∑' n : ℕ, LSeries.term f s₀ (n+1) *
        g (((n+1:ℕ):ℝ)/N)‖ ≤ E) :
    ‖∑ n ∈ (Finset.range K).image Nat.succ,
      if n.Prime ∧ (n:ℝ) ∈ I then
        (Real.log (n:ℝ) : ℂ) *
          (χ (n : ZMod q) *
            (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) else 0‖ ≤
      E + (2*Real.log (3*N)/N)*(2*ε*N+2) +
        (2*Real.sqrt (K:ℝ)*Real.log (K:ℝ))/N := by
  classical
  let S : Finset ℕ := (Finset.range K).image Nat.succ
  have hSharp := p1_all_intervals_from_actual_smooth_m2
    q χ N ε t E K I hN hε hεmax hK hI hIS hE hSmoothAll
  have hx : 1 ≤ K := by
    exact_mod_cast (show (1:ℝ) ≤ (K:ℝ) by linarith)
  have hS : S ⊆ Finset.Ioc 0 K := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Ioc.mpr
      ⟨Nat.succ_pos m, Nat.succ_le_of_lt (Finset.mem_range.mp hm)⟩
  have hBound := p1_actual_prime_log_norm_le
    q χ N t (E + (2*Real.log (3*N)/N)*(2*ε*N+2))
    K S I hN hx hS hIS hSharp
  simpa only [S] using hBound

end Green64Analytic.LongPrime

-- END P1PrimeAllIntervals

-- BEGIN P1PositiveRangeMem

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open scoped Classical

theorem p1_mem_positive_range_iff (K n : ℕ) :
    n ∈ (Finset.range K).image Nat.succ ↔ 0 < n ∧ n ≤ K := by
  constructor
  · intro hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact ⟨Nat.succ_pos m, Nat.succ_le_of_lt (Finset.mem_range.mp hm)⟩
  · rintro ⟨hpos,hle⟩
    apply Finset.mem_image.mpr
    refine ⟨n-1, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · omega

end Green64Analytic.LongPrime

-- END P1PositiveRangeMem

-- BEGIN P1PrimePrefixIdentity

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction
open scoped Classical

/-- Exact identification of all prefix prime-log polynomials
with a sharp intersection of the source interval and Iio k. -/
theorem p1_actual_prime_prefix_eq
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (K k : ℕ) (I : Set ℝ) (t : ℝ) (hk : k ≤ K) :
    (∑ n ∈ (Finset.range K).image Nat.succ,
      if n.Prime ∧ (n:ℝ) ∈ (I ∩ Set.Iio (k:ℝ)) then
        (Real.log (n:ℝ) : ℂ) *
          (χ (n : ZMod q) *
            (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) else 0) =
    ∑ n ∈ Finset.range k, (Real.log (n:ℝ) : ℂ) *
      sourcePrimeCoeff q χ I t n := by
  classical
  let S : Finset ℕ := (Finset.range K).image Nat.succ
  let J : Set ℝ := I ∩ Set.Iio (k:ℝ)
  have hFiltered :
      S.filter (fun n : ℕ => n.Prime ∧ (n:ℝ) ∈ J) =
      (Finset.range k).filter (fun n : ℕ => n.Prime ∧ (n:ℝ) ∈ I) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnS,hp,hJ⟩ := Finset.mem_filter.mp hn
      have hnlt : n < k := by
        have hh : (n:ℝ) < (k:ℝ) := hJ.2
        exact_mod_cast hh
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hnlt, hp, hJ.1⟩
    · intro hn
      obtain ⟨hnk,hp,hI⟩ := Finset.mem_filter.mp hn
      have hnlt : n < k := Finset.mem_range.mp hnk
      have hnpos : 0 < n := hp.pos
      have hnle : n ≤ K := (Nat.le_of_lt hnlt).trans hk
      have hreal : (n:ℝ) < (k:ℝ) := by exact_mod_cast hnlt
      exact Finset.mem_filter.mpr
        ⟨(p1_mem_positive_range_iff K n).mpr ⟨hnpos,hnle⟩,
          hp, ⟨hI, hreal⟩⟩
  have hLeft :
      (∑ n ∈ S, if n.Prime ∧ (n:ℝ) ∈ J then
        (Real.log (n:ℝ) : ℂ) *
          (χ (n : ZMod q) *
            (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) else 0) =
      ∑ n ∈ S.filter (fun n : ℕ => n.Prime ∧ (n:ℝ) ∈ J),
        (Real.log (n:ℝ) : ℂ) * sourcePrimeTerm q χ t n := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime ∧ (n:ℝ) ∈ J
    · simp [hp, sourcePrimeTerm]
    · simp [hp]
  have hRight :
      (∑ n ∈ Finset.range k,
         (Real.log (n:ℝ) : ℂ) * sourcePrimeCoeff q χ I t n) =
      ∑ n ∈ (Finset.range k).filter
          (fun n : ℕ => n.Prime ∧ (n:ℝ) ∈ I),
        (Real.log (n:ℝ) : ℂ) * sourcePrimeTerm q χ t n := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime ∧ (n:ℝ) ∈ I
    · simp [sourcePrimeCoeff, hp]
    · simp [sourcePrimeCoeff, hp]
  calc
    (∑ n ∈ S, if n.Prime ∧ (n:ℝ) ∈ J then
        (Real.log (n:ℝ) : ℂ) *
          (χ (n : ZMod q) *
            (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) else 0) =
      ∑ n ∈ S.filter (fun n : ℕ => n.Prime ∧ (n:ℝ) ∈ J),
        (Real.log (n:ℝ) : ℂ) * sourcePrimeTerm q χ t n := hLeft
    _ = ∑ n ∈ (Finset.range k).filter
          (fun n : ℕ => n.Prime ∧ (n:ℝ) ∈ I),
        (Real.log (n:ℝ) : ℂ) * sourcePrimeTerm q χ t n := by
      rw [hFiltered]
    _ = _ := hRight.symm

end Green64Analytic.LongPrime

-- END P1PrimePrefixIdentity

-- BEGIN P1PrimePrefixBound

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction
open scoped Classical

/-- Uniform actual prime-log prefix bounds required by literal P2:
each prefix is an order-connected intersection, not a new premise. -/
theorem p1_actual_prime_prefix_from_smooth_m2
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N ε t E : ℝ) (K k : ℕ) (I : Set ℝ)
    (hN : 1 ≤ N) (hε : 0 < ε) (hεmax : ε ≤ 1/4)
    (hK : 3*N ≤ (K:ℝ)) (hk : k ≤ K)
    (hI : Set.OrdConnected I) (hIS : I ⊆ Set.Icc N (2*N))
    (hE : 0 ≤ E)
    (hSmoothAll : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2 →
      let f : ℕ → ℂ := (fun m : ℕ => χ (m : ZMod q)) *
        (fun m : ℕ => (Λ m : ℂ))
      let s₀ : ℂ := 1-(t:ℂ)*Complex.I
      let g : ℝ → ℂ := fun u => (smoothIntervalWeight a b ε u : ℝ)
      ‖∑' n : ℕ, LSeries.term f s₀ (n+1) *
        g (((n+1:ℕ):ℝ)/N)‖ ≤ E) :
    ‖∑ n ∈ Finset.range k, (Real.log (n:ℝ) : ℂ) *
      sourcePrimeCoeff q χ I t n‖ ≤
      E + (2*Real.log (3*N)/N)*(2*ε*N+2) +
        (2*Real.sqrt (K:ℝ)*Real.log (K:ℝ))/N := by
  let J : Set ℝ := I ∩ Set.Iio (k:ℝ)
  have hJ : Set.OrdConnected J :=
    hI.inter Set.ordConnected_Iio
  have hJS : J ⊆ Set.Icc N (2*N) := by
    intro x hx
    exact hIS hx.1
  have hBound := p1_actual_prime_log_all_intervals
    q χ N ε t E K J hN hε hεmax hK hJ hJS hE hSmoothAll
  rw [← p1_actual_prime_prefix_eq q χ K k I t hk]
  have hEqSum :
      (∑ n ∈ (Finset.range K).image Nat.succ,
        if n.Prime ∧ (n:ℝ) ∈ (I ∩ Set.Iio (k:ℝ)) then
          (Real.log (n:ℝ) : ℂ) *
            (χ (n : ZMod q) *
              (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) else 0) =
      (∑ n ∈ (Finset.range K).image Nat.succ,
        if n.Prime ∧ (n:ℝ) ∈ J then
          (Real.log (n:ℝ) : ℂ) *
            (χ (n : ZMod q) *
              (n : ℂ)^((-1:ℂ)+(t:ℂ)*Complex.I)) else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hh : n.Prime ∧ (n:ℝ) ∈ (I ∩ Set.Iio (k:ℝ))
    · simp [J, hh]
    · simp [J, hh]
  rw [hEqSum]
  simpa using hBound

end Green64Analytic.LongPrime

-- END P1PrimePrefixBound

-- BEGIN P1P2LiteralBound

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction
open scoped Classical

/-- Exact P1/P2 conclusion with literal U1 finite-prime indexing.
The only analytic hypothesis is the genuine M2 smooth Λ sum. -/
theorem p1p2_literal_prime_norm_le
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N ε t E : ℝ) (K : ℕ) (I : Set ℝ)
    (hN : 1 < N) (hε : 0 < ε) (hεmax : ε ≤ 1/4)
    (hK : 3*N ≤ (K:ℝ))
    (hI : Set.OrdConnected I) (hIS : I ⊆ Set.Icc N (2*N))
    (hE : 0 ≤ E)
    (hSmoothAll : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2 →
      let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
        (fun k : ℕ => (Λ k : ℂ))
      let s₀ : ℂ := 1-(t:ℂ)*Complex.I
      let g : ℝ → ℂ := fun u => (smoothIntervalWeight a b ε u : ℝ)
      ‖∑' n : ℕ, LSeries.term f s₀ (n+1) *
        g (((n+1:ℕ):ℝ)/N)‖ ≤ E) :
    ‖∑ p ∈ (@Finset.filter ℕ (fun p => (p:ℝ) ∈ I)
      (fun _ => Classical.propDecidable _)
      ((Finset.range (⌊2*N⌋₊ + 1)).filter Nat.Prime)),
      sourcePrimeTerm q χ t p‖ ≤
    (E + (2*Real.log (3*N)/N)*(2*ε*N+2) +
      (2*Real.sqrt (K:ℝ)*Real.log (K:ℝ))/N) /
       Real.log N := by
  let E' : ℝ :=
    E + (2*Real.log (3*N)/N)*(2*ε*N+2) +
      (2*Real.sqrt (K:ℝ)*Real.log (K:ℝ))/N
  have hFloor : (⌊2*N⌋₊ : ℝ) ≤ 2*N :=
    Nat.floor_le (by linarith)
  have hKprefix : ⌊2*N⌋₊ + 1 ≤ K := by
    have hReal : ((⌊2*N⌋₊ + 1 : ℕ):ℝ) ≤ (K:ℝ) := by
      push_cast
      linarith
    exact_mod_cast hReal
  have hprefix : ∀ k : ℕ, k ≤ ⌊2*N⌋₊ + 1 →
      ‖∑ p ∈ Finset.range k,
          (Real.log (p:ℝ) : ℂ) *
            sourcePrimeCoeff q χ I t p‖ ≤ E' := by
    intro k hk
    exact p1_actual_prime_prefix_from_smooth_m2
      q χ N ε t E K k I (by linarith) hε hεmax
      hK (hk.trans hKprefix) hI hIS hE hSmoothAll
  have hE' : 0 ≤ E' := by
    have h := hprefix 0 (by omega)
    simpa only [Finset.sum_range_zero, norm_zero] using h
  exact p2_source_prime_prefix q χ N E' t I
    hN hE' hIS hprefix

end Green64Analytic.LongPrime

-- END P1P2LiteralBound

-- BEGIN P1P2SourceM2

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction
open scoped Classical

/-- Complete source-quantified M2 -> P1 -> P2 inequality, with actual
prime sum, all χ and source intervals. Only SourceKhaleZeroFree remains
an external analytic assumption; no prime polynomial bound is assumed. -/
theorem p1p2_source_actual_prime_bound
    (hKhale : SourceKhaleZeroFree) :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ C C₅ : ℝ, 0 < C → 0 ≤ C₅ →
      ∃ L₀ : ℝ, 3 ≤ L₀ ∧
        ∀ L : ℝ, L₀ ≤ L →
          let Q : ℝ := 3*L^C
          let V : ℝ := 3*Real.exp (3*L)
          let D : ℝ := 10.5*Real.log Q +
            61.5*(Real.log V)^(2/3:ℝ) *
              (Real.log (Real.log V))^(1/3:ℝ)
          let δ : ℝ := (100*D)⁻¹
          let H : ℝ := L^C₅
          let right : ℝ := L⁻¹
          ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
            (q:ℝ) ≤ L^C →
          ∀ (η N ε t : ℝ) (j K : ℕ) (I : Set ℝ),
            1 < N → N ≤ (Real.exp L)^η →
            0 < ε → ε ≤ 1/4 →
            L^(C₅+3) ≤ |t| → |t| ≤ (Real.exp L)^2 →
            2 ≤ j → 3*N ≤ (K:ℝ) →
            Set.OrdConnected I → I ⊆ Set.Icc N (2*N) →
            let B : ℝ :=
              20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
            let R : ℝ :=
              B * Real.exp η * (8*L^2) *
                (-H^(1-(j:ℝ))/(1-(j:ℝ)))
            let M : ℝ :=
              2*H*(B*N^(-δ)*(3*50*L)) +
                2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) +
                  2*R
            ‖∑ p ∈ (@Finset.filter ℕ (fun p => (p:ℝ) ∈ I)
                (fun _ => Classical.propDecidable _)
                ((Finset.range (⌊2*N⌋₊+1)).filter Nat.Prime)),
                sourcePrimeTerm q χ t p‖ ≤
              (M/(2*Real.pi) +
                (2*Real.log (3*N)/N)*(2*ε*N+2) +
                (2*Real.sqrt (K:ℝ)*Real.log (K:ℝ))/N) /
                  Real.log N := by
  obtain ⟨α₀,hα₀,hMain⟩ :=
    m2_source_actual_smooth_mangoldt_bound hKhale
  refine ⟨α₀,hα₀,?_⟩
  intro C C₅ hC hC₅
  obtain ⟨L₀,hL₀,hBound⟩ := hMain C C₅ hC hC₅
  refine ⟨L₀,hL₀,?_⟩
  intro L hL Q V D δ H right q _ χ hq η N ε t j K I
    hN hNmax hε hεmax htlo hthi hj hK hI hIS
  dsimp only
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  let R : ℝ :=
    B * Real.exp η * (8*L^2) *
      (-H^(1-(j:ℝ))/(1-(j:ℝ)))
  let M : ℝ :=
    2*H*(B*N^(-δ)*(3*50*L)) +
      2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) +
        2*R
  have hSmoothAll : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2 →
      let f : ℕ → ℂ := (fun m : ℕ => χ (m : ZMod q)) *
        (fun m : ℕ => (Λ m : ℂ))
      let s₀ : ℂ := 1-(t:ℂ)*Complex.I
      let g : ℝ → ℂ := fun u => (smoothIntervalWeight a b ε u : ℝ)
      ‖∑' n : ℕ, LSeries.term f s₀ (n+1) *
        g (((n+1:ℕ):ℝ)/N)‖ ≤ M/(2*Real.pi) := by
    intro a b ha hab hb
    have h := hBound L hL q χ hq η N a b ε t j
      (by linarith) hNmax ha hab hb hε hεmax htlo hthi hj
    simpa only [B,R,M] using h
  have hM0 : 0 ≤ M/(2*Real.pi) := by
    have h := hSmoothAll 1 1 (by norm_num) (by norm_num) (by norm_num)
    dsimp only at h
    exact (norm_nonneg _).trans h
  have hResult := p1p2_literal_prime_norm_le
    q χ N ε t (M/(2*Real.pi)) K I hN hε hεmax hK hI hIS
      hM0 hSmoothAll
  simpa only [B,R,M] using hResult

end Green64Analytic.LongPrime

-- END P1P2SourceM2

end

/-! ## Standalone.LongPrimeStageA2 -/

section

-- Exact two source proof bodies; transitive imports made explicit.

-- BEGIN M2DampingPolynomial

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- The actual Khale denominator D = O(L^(3/4)) implies arbitrary
polynomial log damping for N >= exp(τL)/2, at an explicit threshold.
This closes the difficult left-line N^(-δ) scale comparison. -/
theorem m2_damping_superpolynomial_at_threshold
    (L τ N D κ M : ℝ)
    (hL : 3 ≤ L) (hτ : 0 < τ) (hκ : 0 < κ)
    (hM : 0 ≤ M) (hD : 0 < D)
    (hDmax : D ≤ κ*L^(3/4:ℝ))
    (hδsmall : (100*D)⁻¹ ≤ 1)
    (hN : (Real.exp L)^τ / 2 ≤ N)
    (hthreshold : 800*κ*M ≤ τ*L^(1/8:ℝ)) :
    N ^ (-(100*D)⁻¹) ≤ 2*L^(-M) := by
  let δ : ℝ := (100*D)⁻¹
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hlogpos : 0 ≤ Real.log L := Real.log_nonneg hLone
  have hpow : 0 ≤ L^(3/4:ℝ) := Real.rpow_nonneg hLp.le _
  have hlogbound : Real.log L ≤ 8*L^(1/8:ℝ) :=
    g2_log_power L hLone
  have hP7 : L^(3/4:ℝ)*L^(1/8:ℝ) = L^(7/8:ℝ) := by
    rw [← Real.rpow_add hLp]
    congr 1
    ring
  have hP8 : L^(1/8:ℝ)*L^(7/8:ℝ) = L := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hprod : 100*D*M*Real.log L ≤ τ*L := by
    calc
      100*D*M*Real.log L ≤
          100*(κ*L^(3/4:ℝ))*M*Real.log L := by
            apply mul_le_mul_of_nonneg_right
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left hDmax (by norm_num)
            · exact hM
            · exact hlogpos
      _ ≤ 100*(κ*L^(3/4:ℝ))*M*(8*L^(1/8:ℝ)) := by
            have hb : 0 ≤ 100*(κ*L^(3/4:ℝ))*M := by positivity
            exact mul_le_mul_of_nonneg_left hlogbound hb
      _ = (800*κ*M)*L^(7/8:ℝ) := by
            rw [← hP7]
            ring
      _ ≤ (τ*L^(1/8:ℝ))*L^(7/8:ℝ) := by
            exact mul_le_mul_of_nonneg_right hthreshold
              (Real.rpow_nonneg hLp.le _)
      _ = τ*L := by
            calc
              (τ*L^(1/8:ℝ))*L^(7/8:ℝ) =
                  τ*(L^(1/8:ℝ)*L^(7/8:ℝ)) := by ring
              _ = τ*L := by rw [hP8]
  have hunit : 100*D*δ = 1 := by
    dsimp [δ]
    field_simp
  have hExp : M*Real.log L ≤ τ*δ*L := by
    calc
      M*Real.log L = (100*D*δ)*(M*Real.log L) := by rw [hunit]; ring
      _ = (100*D*M*Real.log L)*δ := by ring
      _ ≤ (τ*L)*δ := mul_le_mul_of_nonneg_right hprod hδpos.le
      _ = τ*δ*L := by ring
  have hActual := m2_actual_vertical_damping
    (Real.exp L) τ N δ (Real.exp_pos _) hN hδpos.le
  have hActual' : N^(-δ) ≤
      (2:ℝ)^δ*Real.exp (-(τ*δ*L)) := by
    simpa only [Real.log_exp] using hActual
  have hDecay : Real.exp (-(τ*δ*L)) ≤ L^(-M) := by
    have hh : -(τ*δ*L) ≤ Real.log L*(-M) := by nlinarith [hExp]
    rw [Real.rpow_def_of_pos hLp (-M)]
    exact Real.exp_le_exp.mpr hh
  have hTwo : (2:ℝ)^δ ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 2) hδsmall
    simpa only [Real.rpow_one] using h
  calc
    N^(-δ) ≤ (2:ℝ)^δ*Real.exp (-(τ*δ*L)) := hActual'
    _ ≤ (2:ℝ)^δ*L^(-M) :=
      mul_le_mul_of_nonneg_left hDecay
        (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 2*L^(-M) :=
      mul_le_mul_of_nonneg_right hTwo
        (Real.rpow_nonneg hLp.le _)

end Green64Analytic.LongPrime

-- END M2DampingPolynomial

-- BEGIN M2DampingEventual

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- True source Khale D(L) is enough for arbitrary polynomial
damping, uniformly over the original short-interval lower scale. -/
theorem m2_source_damping_superpolynomial
    (C τ M : ℝ) (hC : 0 ≤ C) (hτ : 0 < τ) (hM : 0 ≤ M) :
    ∃ L₀ : ℝ, 3 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      let Q : ℝ := 3*L^C
      let V : ℝ := 3*Real.exp (3*L)
      let D : ℝ := 10.5*Real.log Q +
        61.5*(Real.log V)^(2/3:ℝ) *
          (Real.log (Real.log V))^(1/3:ℝ)
      ∀ N : ℝ, (Real.exp L)^τ/2 ≤ N →
        N^(-(100*D)⁻¹) ≤ 2*L^(-M) := by
  let κ : ℝ := 1100+100*C
  have hκ : 0 < κ := by dsimp [κ]; linarith
  let T : ℝ := κ*(M+1)/τ
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨L₀,hL₀,hPower⟩ := g2_eighth_threshold T hT
  refine ⟨L₀,hL₀,?_⟩
  intro L hL Q V D N hN
  have hL3 : 3 ≤ L := hL₀.trans hL
  have hDen := g2_Khale_denominator C L hC hL3
  change 0 < D ∧ D ≤ κ*L^(3/4:ℝ) at hDen
  obtain ⟨hD,hDmax⟩ := hDen
  have hDone := g2_denominator_ge_one C L hC hL3
  change 1 ≤ D at hDone
  have hδsmall : (100*D)⁻¹ ≤ 1 := by
    have hp : (0:ℝ) < 100*D := by positivity
    have hh : (1:ℝ) ≤ 100*D := by nlinarith
    calc
      (100*D)⁻¹ ≤ (1:ℝ)⁻¹ := by
        simpa only [one_div] using
          (one_div_le_one_div_of_le (by norm_num) hh)
      _ = 1 := by norm_num
  have hPowerL : 800*T ≤ L^(1/8:ℝ) := hPower L hL
  have hthreshold : 800*κ*M ≤ τ*L^(1/8:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hPowerL hτ.le
    dsimp [T] at hh
    have hτne : τ ≠ 0 := ne_of_gt hτ
    have hrewrite : τ*(800*(κ*(M+1)/τ)) = 800*κ*(M+1) := by
      field_simp
    rw [hrewrite] at hh
    nlinarith [hh]
  exact m2_damping_superpolynomial_at_threshold
    L τ N D κ M hL3 hτ hκ hM hD hDmax hδsmall hN hthreshold

end Green64Analytic.LongPrime

-- END M2DampingEventual

end

