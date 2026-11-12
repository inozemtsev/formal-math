module

public import Green64.Library.Weights.Part005
public import Mathlib.Tactic
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Green64.Library.Analysis.Estimates.Part001
public import Green64.Library.Weights.Part001
public import Green64.Library.Sieve.Foundations.Part002

@[expose] public section

/-!
# Weights / Part006

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## M1SourceInverseAssembly -/

section

open ArithmeticFunction MeasureTheory
open scoped LSeries.notation
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem source_mangoldt_weighted_inverse_assembly
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (N σ t : ℝ) (F : ℂ → ℂ) (g : ℝ → ℂ)
    (hN : 0 < N) (hσ : 0 < σ)
    (hV : Complex.VerticalIntegrable F σ)
    (hInv : ∀ x : ℝ, 0 < x → mellinInv σ F x = g x) :
    let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
      (fun k : ℕ => (Λ k : ℂ))
    let s₀ : ℂ := 1-(t:ℂ)*Complex.I
    (∑' n : ℕ, LSeries.term f s₀ (n+1) *
       g (((n+1:ℕ):ℝ)/N)) =
    (1/(2*Real.pi):ℂ) * ∫ y : ℝ,
      (N:ℂ)^((σ:ℂ)+(y:ℂ)*Complex.I) *
      (-(deriv (DirichletCharacter.LFunction χ)
        (s₀+((σ:ℂ)+(y:ℂ)*Complex.I))) /
       DirichletCharacter.LFunction χ
        (s₀+((σ:ℂ)+(y:ℂ)*Complex.I))) *
      F ((σ:ℂ)+(y:ℂ)*Complex.I) := by
  let f : ℕ → ℂ := (fun k : ℕ => χ (k : ZMod q)) *
    (fun k : ℕ => (Λ k : ℂ))
  let s₀ : ℂ := 1-(t:ℂ)*Complex.I
  let c : ℕ → ℂ := fun n => LSeries.term f s₀ (n+1)
  let u : ℕ → ℝ := fun n => ((n:ℝ)+1)/N
  have hu : ∀ n, 0 < u n := by
    intro n
    exact div_pos (by positivity) hN
  have hc : Summable (fun n : ℕ => ‖c n‖ * (u n)^(-σ)) :=
    by simpa only [u, Nat.cast_add, Nat.cast_one] using
      (twisted_mangoldt_mellin_coeff_summable q χ N σ t hN hσ)
  have hBase := infinite_weighted_mellin_inverse u c σ F hu hV hc
  have hActual := source_twisted_mangoldt_actual_integral
    q χ N σ t F hN hσ hV
  have hSwap := source_twisted_mangoldt_mellin_exchange
    q χ N σ t F hN hσ hV
  dsimp only [f,s₀,c,u] at *
  push_cast at *
  change (∑' n : ℕ, c n * g (u n)) = _
  calc
    (∑' n : ℕ, c n * g (u n)) =
      (∑' n : ℕ, c n * mellinInv σ F (u n)) := by
        apply tsum_congr
        intro n
        rw [hInv (u n) (hu n)]
    _ = (1/(2*Real.pi):ℂ) * (∫ y : ℝ,
          ∑' n : ℕ, (c n * (u n:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
            F ((σ:ℂ)+(y:ℂ)*Complex.I)) := by
      simpa only [c,u,f,s₀, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one] using hBase
    _ = _ := by
      congr 1
      calc
        (∫ y : ℝ, ∑' n : ℕ,
          (c n * (u n:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
            F ((σ:ℂ)+(y:ℂ)*Complex.I)) =
          (∑' n : ℕ, ∫ y : ℝ,
           (c n * (u n:ℂ)^(-((σ:ℂ)+(y:ℂ)*Complex.I))) *
            F ((σ:ℂ)+(y:ℂ)*Complex.I)) := by
            simpa only [c,u,f,s₀, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one] using hSwap.symm
        _ = _ := by
          simpa only [c,u,f,s₀, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast, Nat.cast_add, Nat.cast_one] using hActual
end Green64Analytic.LongPrime

end

/-! ## M2Damping -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Quantitative damping on the actual source prime interval lower scale.
No asymptotic or analytic-number-theory hypothesis is introduced. -/
theorem m2_actual_vertical_damping
    (x τ N δ : ℝ)
    (hx : 0 < x) (hN : x ^ τ / 2 ≤ N)
    (hδ : 0 ≤ δ) :
    N ^ (-δ) ≤ (2:ℝ) ^ δ *
      Real.exp (-(τ*δ*Real.log x)) := by
  have hxpow : 0 < x ^ τ := Real.rpow_pos_of_pos hx _
  have hlower : 0 < x ^ τ / 2 := by positivity
  have hNpos : 0 < N := lt_of_lt_of_le hlower hN
  have hlog := Real.log_le_log hlower hN
  have hlogpower : Real.log (x ^ τ / 2) =
      τ * Real.log x - Real.log 2 := by
    rw [Real.log_div (ne_of_gt hxpow) (by norm_num : (2:ℝ) ≠ 0),
      Real.log_rpow hx τ]
  have hlogN : τ*Real.log x-Real.log 2 ≤ Real.log N := by
    simpa only [hlogpower] using hlog
  rw [Real.rpow_def_of_pos hNpos (-δ),
    Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2) δ]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonpos_right hlogN (by linarith : -δ ≤ 0)]
end Green64Analytic.LongPrime

end

/-! ## M2RightLineUniform -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction
open scoped LSeries.notation

theorem m2_right_line_logderivative_uniform
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ y : ℝ) (hσ : 0 < σ) :
    ‖-(deriv (DirichletCharacter.LFunction χ)
       ((1+σ:ℝ) + (y:ℂ)*Complex.I)) /
         DirichletCharacter.LFunction χ
          ((1+σ:ℝ) + (y:ℂ)*Complex.I)‖ ≤
    ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => (Λ n : ℂ))
                  ((1+σ:ℝ):ℂ) n‖ := by
  let s : ℂ := ((1+σ:ℝ):ℂ) + (y:ℂ)*Complex.I
  have hs : 1 < s.re := by dsimp [s]; simp; linarith
  have hs0 : 1 < (((1+σ:ℝ):ℂ)).re := by simp; linarith
  have hχ : LSeriesSummable
      ((fun n : ℕ => χ (n : ZMod q)) * (fun n : ℕ => (Λ n : ℂ))) s :=
    χ.LSeriesSummable_twist_vonMangoldt hs
  have hΛ : LSeriesSummable (fun n : ℕ => (Λ n : ℂ))
      ((1+σ:ℝ):ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hs0
  have heach : ∀ n : ℕ,
      ‖LSeries.term
        ((fun n : ℕ => χ (n : ZMod q)) * (fun n : ℕ => (Λ n : ℂ))) s n‖ ≤
      ‖LSeries.term (fun n : ℕ => (Λ n : ℂ)) ((1+σ:ℝ):ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    have hsre : s.re = 1+σ := by dsimp [s]; simp
    rw [hsre]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [if_neg hn]
      apply div_le_div_of_nonneg_right
      · change ‖χ (n : ZMod q) * (Λ n : ℂ)‖ ≤ ‖(Λ n : ℂ)‖
        rw [norm_mul]
        simpa using
          (mul_le_mul_of_nonneg_right (χ.norm_le_one n) (norm_nonneg (Λ n : ℂ)))
      · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc
    ‖-(deriv (DirichletCharacter.LFunction χ) s) /
      DirichletCharacter.LFunction χ s‖ =
      ‖LSeries ((fun n : ℕ => χ (n : ZMod q)) *
                (fun n : ℕ => (Λ n : ℂ))) s‖ := by
        rw [actual_continued_twist_vonMangoldt q χ s hs]
    _ ≤ ∑' n : ℕ,
          ‖LSeries.term
            ((fun n : ℕ => χ (n : ZMod q)) * (fun n : ℕ => (Λ n : ℂ))) s n‖ :=
        norm_tsum_le_tsum_norm hχ.norm
    _ ≤ ∑' n : ℕ,
          ‖LSeries.term (fun n : ℕ => (Λ n : ℂ)) ((1+σ:ℝ):ℂ) n‖ :=
        Summable.tsum_le_tsum heach hχ.norm hΛ.norm
end Green64Analytic.LongPrime

end

/-! ## M2ZetaMajorant916 -/

section

namespace Green64Analytic.LongPrime
open ArithmeticFunction

theorem m2_vonMangoldt_zeta_term_majorant (α : ℝ) (hα : 0 < α) (n : ℕ) :
    ‖LSeries.term (fun n : ℕ => (Λ n : ℂ)) (((1+2*α:ℝ):ℂ)) n‖ ≤
    α⁻¹ * (1/(n:ℝ)^(1+α)) := by
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp only [if_pos rfl, Nat.cast_zero]
    positivity
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [if_neg hn]
  have hnorm : ‖(Λ n : ℂ)‖ = Λ n := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg vonMangoldt_nonneg
  rw [hnorm]
  have hbound : Λ n ≤ (n:ℝ)^α / α :=
    vonMangoldt_le_log.trans (Real.log_natCast_le_rpow_div n hα)
  calc
    (Λ n) / (n:ℝ)^(1+2*α) ≤
      ((n:ℝ)^α / α) / (n:ℝ)^(1+2*α) :=
        div_le_div_of_nonneg_right hbound (by positivity)
    _ = α⁻¹ * (1 / (n:ℝ)^(1+α)) := by
      have hnA : (n:ℝ)^α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos _)
      have hnB : (n:ℝ)^(1+α) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos _)
      have hαne : α ≠ 0 := ne_of_gt hα
      rw [show (1+2*α : ℝ) = (1+α)+α by ring, Real.rpow_add hnpos]
      field_simp

theorem m2_vonMangoldt_zeta_tsum_majorant
    (α : ℝ) (hα : 0 < α) :
    (∑' n : ℕ, ‖LSeries.term (fun n : ℕ => (Λ n : ℂ))
          ((1+2*α:ℝ):ℂ) n‖) ≤
      α⁻¹ * (∑' n : ℕ, 1 / (n:ℝ)^(1+α)) := by
  have hm : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n : ℕ => (Λ n : ℂ))
         ((1+2*α:ℝ):ℂ) n‖) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt
      (by simp; linarith : 1 < (((1+2*α:ℝ):ℂ)).re)).norm
  have hz : Summable (fun n : ℕ => 1/(n:ℝ)^(1+α)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  calc
    _ ≤ ∑' n : ℕ, α⁻¹ * (1 / (n:ℝ)^(1+α)) :=
      Summable.tsum_le_tsum
        (m2_vonMangoldt_zeta_term_majorant α hα) hm (hz.mul_left _)
    _ = _ := tsum_mul_left

theorem m2_zeta_residue_eventual :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ α : ℝ, 0 < α → α < α₀ →
        α * (∑' n : ℕ, 1 / (n:ℝ)^(1+α)) ≤ 2 := by
  have he : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
      (s-1) * (∑' n : ℕ, 1/(n:ℝ)^s) < 2 :=
    tendsto_sub_mul_tsum_nat_rpow.eventually_lt_const (by norm_num)
  obtain ⟨ε, hε, hmem⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨ε, hε, ?_⟩
  intro α hα hαε
  have hm : (1+α:ℝ) ∈ Metric.ball 1 ε ∩ Set.Ioi 1 := by
    constructor
    · change dist (1+α) 1 < ε
      rw [Real.dist_eq, show (1+α)-1 = α by ring, abs_of_pos hα]
      exact hαε
    · change 1 < 1+α
      linarith
  have hh := hmem hm
  change ((1+α:ℝ)-1) * (∑' n : ℕ, 1/(n:ℝ)^(1+α)) < 2 at hh
  simpa only [add_sub_cancel_left] using hh.le

theorem m2_vonMangoldt_quadratic_majorant :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ α : ℝ, 0 < α → α < α₀ →
        (∑' n : ℕ, ‖LSeries.term (fun n : ℕ => (Λ n : ℂ))
                ((1+2*α:ℝ):ℂ) n‖) ≤ 2 / α^2 := by
  obtain ⟨α₀, hα₀, hres⟩ := m2_zeta_residue_eventual
  refine ⟨α₀, hα₀, ?_⟩
  intro α hα hα₀'
  let Z : ℝ := ∑' n : ℕ, 1/(n:ℝ)^(1+α)
  have hZ : α*Z ≤ 2 := hres α hα hα₀'
  have hZle : Z ≤ 2/α := (le_div_iff₀ hα).2 (by nlinarith [hZ])
  calc
    _ ≤ α⁻¹ * Z := m2_vonMangoldt_zeta_tsum_majorant α hα
    _ ≤ α⁻¹ * (2/α) :=
      mul_le_mul_of_nonneg_left hZle (le_of_lt (inv_pos.mpr hα))
    _ = 2 / α^2 := by
      field_simp
      <;> ring

theorem m2_right_line_quadratic_uniform :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ α : ℝ, 0 < α → α < α₀ →
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ),
        ‖-(deriv (DirichletCharacter.LFunction χ)
            ((1+2*α:ℝ)+(y:ℂ)*Complex.I)) /
          DirichletCharacter.LFunction χ
            ((1+2*α:ℝ)+(y:ℂ)*Complex.I)‖ ≤ 2/α^2 := by
  obtain ⟨α₀, hα₀, hζ⟩ := m2_vonMangoldt_quadratic_majorant
  refine ⟨α₀, hα₀, ?_⟩
  intro α hα hα₀' q _ χ y
  exact (m2_right_line_logderivative_uniform q χ (2*α) y (by linarith)).trans
    (hζ α hα hα₀')

end Green64Analytic.LongPrime

end

/-! ## MinDisintegration -/

section

open MeasureTheory
open scoped BigOperators

namespace Green64Analytic.MinDisintegration

/-- Permuting independent coordinates preserves the product Lebesgue measure. -/
theorem coordinate_perm_volume (n : ℕ) (σ : Fin n ≃ Fin n) :
    Measure.map (fun x : Fin n → ℝ => fun i => x (σ i)) volume = volume := by
  have heq : (fun x : Fin n → ℝ => fun i => x (σ i)) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm) := by
    funext x i
    rw [MeasurableEquiv.coe_piCongrLeft]
    simpa using (Equiv.piCongrLeft_apply_apply
      (P := fun _ : Fin n => ℝ) (e := σ.symm) x (σ i)).symm
  rw [heq]
  exact (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm).map_eq

/-- The reciprocal product kernel is invariant under reindexing. -/
theorem coordinate_perm_reciprocal (n : ℕ) (σ : Fin n ≃ Fin n)
    (x : Fin n → ℝ) :
    (∏ i : Fin n, (x (σ i))⁻¹) = ∏ i : Fin n, (x i)⁻¹ := by
  simpa using σ.prod_comp (fun i => (x i)⁻¹)

/-- The permutation preserves every (possibly nonintegrable) Lebesgue integral. -/
theorem coordinate_perm_integral (n : ℕ) (σ : Fin n ≃ Fin n)
    (f : (Fin n → ℝ) → ℝ) :
    (∫ x : Fin n → ℝ, f (fun i => x (σ i))) = ∫ x : Fin n → ℝ, f x := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have hmap : (fun x : Fin n → ℝ => fun i => x (σ i)) = e := by
    funext x i
    change x (σ i) = (Equiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm) x i
    simpa using (Equiv.piCongrLeft_apply_apply
      (P := fun _ : Fin n => ℝ) (e := σ.symm) x (σ i)).symm
  have hh := (MeasureTheory.volume_measurePreserving_piCongrLeft
    (fun _ : Fin n => ℝ) σ.symm).integral_comp' f
  change (∫ x : Fin n → ℝ, f (e x)) = ∫ x : Fin n → ℝ, f x at hh
  rw [← hmap] at hh
  exact hh

/-- There are exactly ell equivalent minimum sectors, cancelling one factorial. -/
theorem factorial_minimum_normalization (ell : ℕ) :
    (ell + 1 : ℝ) / ((ell + 1).factorial : ℝ) =
      1 / (ell.factorial : ℝ) := by
  rw [Nat.factorial_succ]
  push_cast
  have h : (ell.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero ell
  field_simp

/-- Independent coordinate ties have zero product Lebesgue measure. -/
theorem independent_tie_null (n : ℕ) (i : Fin (n + 1)) (k : Fin n) :
    (volume : Measure (Fin (n + 1) → ℝ))
      {x | x i = x (i.succAbove k)} = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let S : Set (ℝ × (Fin n → ℝ)) := {z | z.1 = z.2 k}
  have hs : MeasurableSet S := by
    dsimp [S]
    measurability
  have hfiber (a : ℝ) :
      (volume : Measure (Fin n → ℝ)) (Prod.mk a ⁻¹' S) = 0 := by
    have hh := MeasureTheory.Measure.pi_hyperplane
      (fun _ : Fin n => (volume : Measure ℝ)) k a
    change (volume : Measure (Fin n → ℝ)) {t | a = t k} = 0
    rw [volume_pi]
    simpa only [eq_comm] using hh
  have hprod : ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) S = 0 := by
    exact MeasureTheory.Measure.measure_prod_null_of_ae_null hs
      (Filter.Eventually.of_forall hfiber)
  have hmp := MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) i
  have hpre : (volume : Measure (Fin (n + 1) → ℝ)) (e ⁻¹' S) = 0 := by
    rw [hmp.measure_preimage hs.nullMeasurableSet]
    exact hprod
  have heq : e ⁻¹' S = {x : Fin (n + 1) → ℝ | x i = x (i.succAbove k)} := by
    rfl
  rw [← heq]
  exact hpre

/-- Any two different independent coordinates tie only on a null set. -/
theorem any_independent_tie_null (n : ℕ) (i j : Fin (n + 1)) (hij : i ≠ j) :
    (volume : Measure (Fin (n + 1) → ℝ)) {x | x i = x j} = 0 := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  subst j
  exact independent_tie_null n i k

/-- For finite-dimensional Lebesgue measure the full pairwise-tie locus is null. -/
theorem independent_ties_union_null (n : ℕ) :
    (volume : Measure (Fin (n + 1) → ℝ))
      (⋃ i : Fin (n + 1), ⋃ j : Fin (n + 1),
        if i = j then (∅ : Set (Fin (n + 1) → ℝ)) else {x | x i = x j}) = 0 := by
  rw [MeasureTheory.measure_iUnion_null_iff]
  intro i
  rw [MeasureTheory.measure_iUnion_null_iff]
  intro j
  split_ifs with hij
  · simp
  · exact any_independent_tie_null n i j hij

/-- The affine reflection a ↦ c-a preserves one-dimensional Lebesgue measure. -/
theorem affine_reflection_volume (c : ℝ) :
    MeasurePreserving (fun a : ℝ => c - a) volume volume := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) c).comp
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  convert h using 1
  funext a
  simp only [Function.comp_apply, sub_eq_add_neg]

/-- Lebesgue measure is invariant under reflection of the first coordinate,
    with the reflecting center depending measurably on the other coordinates. -/
theorem dependent_reflection_volume (n : ℕ) (w : ℝ) :
    MeasurePreserving
      (fun z : ℝ × (Fin n → ℝ) => (w - (∑ j, z.2 j) - z.1, z.2))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
  let g : (Fin n → ℝ) → ℝ → ℝ := fun r a => (w - ∑ j, r j) - a
  have hmeas : Measurable (Function.uncurry g) := by
    dsimp [g, Function.uncurry]
    fun_prop
  have hpoint : ∀ r : Fin n → ℝ, Measure.map (g r) volume = volume := by
    intro r
    exact (affine_reflection_volume (w - ∑ j, r j)).map_eq
  have hp := MeasurePreserving.skew_product
    (MeasurePreserving.id (volume : Measure (Fin n → ℝ)))
    hmeas (Filter.Eventually.of_forall hpoint)
  have hswap1 := MeasureTheory.Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))
  have hswap2 := MeasureTheory.Measure.measurePreserving_swap
    (μ := (volume : Measure (Fin n → ℝ))) (ν := (volume : Measure ℝ))
  convert hswap2.comp (hp.comp hswap1) using 1
  funext z
  cases z with
  | mk a r => rfl

/-- Exchange the dependent last coordinate w-Σt with independent coordinate i.
    This is formulated via the canonical Fin-split equivalence, without changing
    the independent-coordinate Lebesgue normalization. -/
noncomputable def exchangeDependent (n : ℕ) (w : ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  e.symm (w - (∑ j : Fin n, (e x).2 j) - (e x).1, (e x).2)

/-- Source-dependent-coordinate exchange has absolute Jacobian one, in the
    precise stronger measure-preserving formulation. -/
theorem exchange_dependent_volume (n : ℕ) (w : ℝ) (i : Fin (n + 1)) :
    Measure.map (exchangeDependent n w i) volume = volume := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hleft := MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) i
  have hmid := dependent_reflection_volume n w
  have hright := hleft.symm e
  have htotal := hright.comp (hmid.comp hleft)
  have heq : exchangeDependent n w i = e.symm ∘
      (fun z : ℝ × (Fin n → ℝ) => (w - (∑ j, z.2 j) - z.1, z.2)) ∘ e := by
    funext x
    rfl
  rw [heq]
  exact htotal.map_eq

/-- Swapped coordinate is exactly the original dependent coordinate. -/
theorem exchange_dependent_at (n : ℕ) (w : ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) :
    exchangeDependent n w i x i = w - ∑ j, x j := by
  change i.insertNth (w - (∑ j : Fin n, (i.removeNth x) j) - x i)
    (i.removeNth x) i = w - ∑ j, x j
  rw [Fin.insertNth_apply_same, Fin.sum_univ_succAbove (fun j => x j) i]
  simp only [Fin.removeNth_apply]
  ring

/-- Every other independent coordinate remains unchanged. -/
theorem exchange_dependent_other (n : ℕ) (w : ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) (k : Fin n) :
    exchangeDependent n w i x (i.succAbove k) = x (i.succAbove k) := by
  change i.insertNth (w - (∑ j : Fin n, (i.removeNth x) j) - x i)
    (i.removeNth x) (i.succAbove k) = x (i.succAbove k)
  simp only [Fin.insertNth_apply_succAbove, Fin.removeNth_apply]

/-- A tie between an independent coordinate and the dependent last coordinate
    is a Lebesgue-null affine hyperplane. No generic hyperplane theorem is assumed. -/
theorem dependent_tie_null (n : ℕ) (w : ℝ) (i : Fin (n + 1)) :
    (volume : Measure (Fin (n + 1) → ℝ))
      {x | x i = w - ∑ j, x j} = 0 := by
  let S : Set ((Fin n → ℝ) × ℝ) :=
    {z | z.2 = w - (∑ j : Fin n, z.1 j) - z.2}
  have hs : MeasurableSet S := by
    dsimp [S]
    measurability
  have hfiber (r : Fin n → ℝ) :
      (volume : Measure ℝ) (Prod.mk r ⁻¹' S) = 0 := by
    have hsub : Prod.mk r ⁻¹' S ⊆ { (w - ∑ j : Fin n, r j) / 2 } := by
      intro a ha
      change a = w - (∑ j : Fin n, r j) - a at ha
      change a = (w - ∑ j : Fin n, r j) / 2
      linarith
    exact MeasureTheory.measure_mono_null hsub (by simp)
  have hprod :
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) S = 0 := by
    exact MeasureTheory.Measure.measure_prod_null_of_ae_null hs
      (Filter.Eventually.of_forall hfiber)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let F : (Fin (n + 1) → ℝ) → ((Fin n → ℝ) × ℝ) :=
    fun x => ((e x).2, (e x).1)
  have he := MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) i
  have hswap := MeasureTheory.Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))
  have hF := hswap.comp he
  have hpre : (volume : Measure (Fin (n + 1) → ℝ)) (F ⁻¹' S) = 0 := by
    have hmap : F = Prod.swap ∘ (⇑e) := by
      funext x
      rfl
    rw [hmap]
    rw [hF.measure_preimage hs.nullMeasurableSet]
    exact hprod
  have heq : F ⁻¹' S = {x : Fin (n + 1) → ℝ | x i = w - ∑ j, x j} := by
    ext x
    change x i = w - (∑ j : Fin n, x (i.succAbove j)) - x i ↔
      x i = w - ∑ j, x j
    rw [Fin.sum_univ_succAbove (fun j => x j) i]
    constructor <;> intro hx <;> linarith
  rw [← heq]
  exact hpre

/-- Exchanging a coordinate with the dependent coordinate sends the new
    independent sum to w minus the old coordinate. -/
theorem exchange_dependent_sum (n : ℕ) (w : ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) :
    (∑ j, exchangeDependent n w i x j) = w - x i := by
  rw [Fin.sum_univ_succAbove (fun j => exchangeDependent n w i x j) i,
    exchange_dependent_at]
  have hrest : (∑ k : Fin n, exchangeDependent n w i x (i.succAbove k)) =
      ∑ k : Fin n, x (i.succAbove k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact exchange_dependent_other n w i x k
  rw [hrest, Fin.sum_univ_succAbove (fun j => x j) i]
  ring

/-- The new dependent coordinate is exactly the old independent coordinate. -/
theorem exchange_dependent_last (n : ℕ) (w : ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) :
    w - (∑ j, exchangeDependent n w i x j) = x i := by
  rw [exchange_dependent_sum]
  ring

/-- Reciprocal kernel is genuinely invariant when swapping with dependent slot. -/
theorem exchange_dependent_reciprocal (n : ℕ) (w : ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) :
    (∏ j, (exchangeDependent n w i x j)⁻¹) *
      (w - ∑ j, exchangeDependent n w i x j)⁻¹ =
    (∏ j, (x j)⁻¹) * (w - ∑ j, x j)⁻¹ := by
  rw [Fin.prod_univ_succAbove (fun j => (exchangeDependent n w i x j)⁻¹) i,
    exchange_dependent_at, exchange_dependent_last,
    Fin.prod_univ_succAbove (fun j => (x j)⁻¹) i]
  have hp : (∏ k : Fin n, (exchangeDependent n w i x (i.succAbove k))⁻¹) =
      ∏ k : Fin n, (x (i.succAbove k))⁻¹ := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [exchange_dependent_other]
  rw [hp]
  ring

/-- The dependent-coordinate exchange is an involution, so it is a true
    permutation of the ell coordinates restricted to their fixed sum. -/
theorem exchange_dependent_involutive (n : ℕ) (w : ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) :
    exchangeDependent n w i (exchangeDependent n w i x) = x := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [exchange_dependent_at, exchange_dependent_last]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
    subst j
    rw [exchange_dependent_other, exchange_dependent_other]

/-- Literal constrained simplex, with the last coordinate depending on the
    others and all ell coordinates bounded below by gamma. -/
def sourceSimplex (n : ℕ) (γ w : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {x | (∀ j, γ ≤ x j) ∧ (∑ j, x j) ≤ w - γ}

/-- The literal source-simplex domain is invariant under exchanging any one
    independent coordinate with the dependent coordinate. -/
theorem exchange_dependent_source_simplex (n : ℕ) (γ w : ℝ)
    (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    exchangeDependent n w i x ∈ sourceSimplex n γ w ↔ x ∈ sourceSimplex n γ w := by
  have hfwd (y : Fin (n + 1) → ℝ) (hy : y ∈ sourceSimplex n γ w) :
      exchangeDependent n w i y ∈ sourceSimplex n γ w := by
    change (∀ j, γ ≤ exchangeDependent n w i y j) ∧
      (∑ j, exchangeDependent n w i y j) ≤ w - γ
    constructor
    · intro j
      by_cases hji : j = i
      · subst j
        rw [exchange_dependent_at]
        have hs := hy.2
        linarith
      · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
        subst j
        rw [exchange_dependent_other]
        exact hy.1 _
    · rw [exchange_dependent_sum]
      have hi := hy.1 i
      linarith
  constructor
  · intro hx
    have hh := hfwd (exchangeDependent n w i x) hx
    simpa only [exchange_dependent_involutive] using hh
  · exact hfwd x

/-- Full Lebesgue integral transport under swapping with the dependent slot. -/
theorem exchange_dependent_integral (n : ℕ) (w : ℝ) (i : Fin (n + 1))
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : StronglyMeasurable f) :
    (∫ x : Fin (n + 1) → ℝ, f (exchangeDependent n w i x)) =
      ∫ x : Fin (n + 1) → ℝ, f x := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have heq : exchangeDependent n w i = e.symm ∘
      (fun z : ℝ × (Fin n → ℝ) => (w - (∑ j, z.2 j) - z.1, z.2)) ∘ e := by
    funext x
    rfl
  have hmid : Measurable
      (fun z : ℝ × (Fin n → ℝ) => (w - (∑ j, z.2 j) - z.1, z.2)) := by
    fun_prop
  have hm : Measurable (exchangeDependent n w i) := by
    rw [heq]
    exact e.symm.measurable.comp (hmid.comp e.measurable)
  have hint := MeasureTheory.integral_map_of_stronglyMeasurable
    (μ := (volume : Measure (Fin (n + 1) → ℝ))) hm hf
  rw [exchange_dependent_volume n w i] at hint
  exact hint.symm

/-- Literal set-indicator reciprocal kernel, with no squarefree restriction. -/
noncomputable def sourceWeight (n : ℕ) (γ w : ℝ)
    (x : Fin (n + 1) → ℝ) : ℝ :=
  (sourceSimplex n γ w).indicator
    (fun y => (∏ j, (y j)⁻¹) * (w - ∑ j, y j)⁻¹) x

/-- Symmetry applies simultaneously to the exact source simplex and density. -/
theorem exchange_dependent_source_weight (n : ℕ) (γ w : ℝ)
    (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    sourceWeight n γ w (exchangeDependent n w i x) = sourceWeight n γ w x := by
  have hm := exchange_dependent_source_simplex n γ w i x
  by_cases hx : x ∈ sourceSimplex n γ w
  · simp only [sourceWeight, Set.indicator_of_mem hx,
      Set.indicator_of_mem (hm.mpr hx)]
    exact exchange_dependent_reciprocal n w i x
  · have hn : exchangeDependent n w i x ∉ sourceSimplex n γ w := by
      exact fun hc => hx (hm.mp hc)
    simp [sourceWeight, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem hn]

/-- Minimum sector where the dependent last coordinate is smallest. -/
def dependentMinimumSector (n : ℕ) (γ w : ℝ) :
    Set (Fin (n + 1) → ℝ) :=
  {x | x ∈ sourceSimplex n γ w ∧ ∀ j, w - (∑ k, x k) ≤ x j}

/-- Minimum sector where a fixed independent coordinate i is smallest. -/
def independentMinimumSector (n : ℕ) (γ w : ℝ) (i : Fin (n + 1)) :
    Set (Fin (n + 1) → ℝ) :=
  {x | x ∈ sourceSimplex n γ w ∧
    x i ≤ w - (∑ k, x k) ∧ ∀ j, x i ≤ x j}

/-- The actual dependent-minimum sector pulls back to any independent-minimum
    sector under the exact affine coordinate exchange. -/
theorem exchange_minimum_sectors (n : ℕ) (γ w : ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) :
    exchangeDependent n w i x ∈ independentMinimumSector n γ w i ↔
      x ∈ dependentMinimumSector n γ w := by
  constructor
  · intro hx
    change exchangeDependent n w i x ∈ sourceSimplex n γ w ∧
      exchangeDependent n w i x i ≤ w - (∑ j, exchangeDependent n w i x j) ∧
      (∀ j, exchangeDependent n w i x i ≤ exchangeDependent n w i x j) at hx
    refine ⟨(exchange_dependent_source_simplex n γ w i x).mp hx.1, ?_⟩
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [exchange_dependent_at, exchange_dependent_last] using hx.2.1
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
      subst j
      simpa only [exchange_dependent_at, exchange_dependent_other] using hx.2.2 (i.succAbove k)
  · intro hx
    change x ∈ sourceSimplex n γ w ∧ (∀ j, w - (∑ k, x k) ≤ x j) at hx
    change exchangeDependent n w i x ∈ sourceSimplex n γ w ∧
      exchangeDependent n w i x i ≤ w - (∑ j, exchangeDependent n w i x j) ∧
      (∀ j, exchangeDependent n w i x i ≤ exchangeDependent n w i x j)
    refine ⟨(exchange_dependent_source_simplex n γ w i x).mpr hx.1, ?_, ?_⟩
    · simpa only [exchange_dependent_at, exchange_dependent_last] using hx.2 i
    · intro j
      by_cases hji : j = i
      · subst j
        exact le_refl _
      · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
        subst j
        simpa only [exchange_dependent_at, exchange_dependent_other] using hx.2 (i.succAbove k)

/-- Explicit measurability of the finite source coordinate kernel. -/
theorem source_kernel_measurable (n : ℕ) (w : ℝ) :
    Measurable (fun x : Fin (n + 1) → ℝ =>
      (∏ j, (x j)⁻¹) * (w - ∑ j, x j)⁻¹) := by
  measurability

/-- All independent-minimum sectors are Borel sets. -/
theorem independent_minimum_measurable (n : ℕ) (γ w : ℝ)
    (i : Fin (n + 1)) : MeasurableSet (independentMinimumSector n γ w i) := by
  dsimp [independentMinimumSector, sourceSimplex]
  measurability

/-- The dependent-minimum sector is Borel. -/
theorem dependent_minimum_measurable (n : ℕ) (γ w : ℝ) :
    MeasurableSet (dependentMinimumSector n γ w) := by
  dsimp [dependentMinimumSector, sourceSimplex]
  measurability

/-- Exact reciprocal-simplex sector equality, not a combinatorial or candidate
    premise. Both integrals use n+1 independent Lebesgue coordinates. -/
theorem minimum_sector_integral_equality (n : ℕ) (γ w : ℝ)
    (i : Fin (n + 1)) :
    (∫ x in independentMinimumSector n γ w i,
      (∏ j, (x j)⁻¹) * (w - ∑ j, x j)⁻¹) =
    (∫ x in dependentMinimumSector n γ w,
      (∏ j, (x j)⁻¹) * (w - ∑ j, x j)⁻¹) := by
  let f : (Fin (n + 1) → ℝ) → ℝ :=
    fun x => (∏ j, (x j)⁻¹) * (w - ∑ j, x j)⁻¹
  let A := independentMinimumSector n γ w i
  let B := dependentMinimumSector n γ w
  have hA : MeasurableSet A := independent_minimum_measurable n γ w i
  have hB : MeasurableSet B := dependent_minimum_measurable n γ w
  have hf : StronglyMeasurable f := (source_kernel_measurable n w).stronglyMeasurable
  have hcomp (x : Fin (n + 1) → ℝ) :
      A.indicator f (exchangeDependent n w i x) = B.indicator f x := by
    by_cases hb : x ∈ B
    · have ha : exchangeDependent n w i x ∈ A :=
        (exchange_minimum_sectors n γ w i x).mpr hb
      rw [Set.indicator_of_mem ha, Set.indicator_of_mem hb]
      exact exchange_dependent_reciprocal n w i x
    · have ha : exchangeDependent n w i x ∉ A := fun hc =>
        hb ((exchange_minimum_sectors n γ w i x).mp hc)
      rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem hb]
  have hint := exchange_dependent_integral n w i (A.indicator f) (hf.indicator hA)
  have heq : (∫ x : Fin (n + 1) → ℝ, B.indicator f x) =
      ∫ x : Fin (n + 1) → ℝ, A.indicator f x := by
    calc
      _ = ∫ x : Fin (n + 1) → ℝ, A.indicator f (exchangeDependent n w i x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => (hcomp x).symm)
      _ = _ := hint
  rw [← integral_indicator hA, ← integral_indicator hB]
  exact heq.symm

/-- Both kinds of tied minima (independent-independent and
    independent-dependent) form a null set. -/
theorem all_source_ties_null (n : ℕ) (w : ℝ) :
    (volume : Measure (Fin (n + 1) → ℝ))
      ((⋃ i : Fin (n + 1), ⋃ j : Fin (n + 1),
          if i = j then (∅ : Set (Fin (n + 1) → ℝ)) else {x | x i = x j}) ∪
       (⋃ i : Fin (n + 1), {x | x i = w - ∑ j, x j})) = 0 := by
  apply measure_union_null
  · exact independent_ties_union_null n
  · rw [measure_iUnion_null_iff]
    exact fun i => dependent_tie_null n w i

/-- The literal source simplex is covered by exactly the kinds of minimum
    sectors needed for disintegration (ties permitted in this set identity). -/
theorem minimum_sectors_cover (n : ℕ) (γ w : ℝ) :
    sourceSimplex n γ w =
    dependentMinimumSector n γ w ∪
      (⋃ i : Fin (n + 1), independentMinimumSector n γ w i) := by
  ext x
  constructor
  · intro hx
    have hne : (Finset.univ : Finset (Fin (n + 1))).Nonempty :=
      ⟨0, Finset.mem_univ _⟩
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image
      (Finset.univ : Finset (Fin (n + 1))) (fun j => x j) hne
    have hm (j : Fin (n + 1)) : x i ≤ x j := hmin j (Finset.mem_univ j)
    by_cases hd : w - (∑ j, x j) ≤ x i
    · exact Or.inl ⟨hx, fun j => (hd.trans (hm j))⟩
    · apply Or.inr
      apply Set.mem_iUnion.mpr
      exact ⟨i, ⟨hx, le_of_lt (lt_of_not_ge hd), hm⟩⟩
  · intro hx
    rcases hx with ha | hb
    · exact ha.1
    · rcases Set.mem_iUnion.mp hb with ⟨i, hi⟩
      exact hi.1

/-- Distinct independent-minimum sectors overlap only on a null tie hyperplane. -/
theorem independent_minimum_aedisjoint (n : ℕ) (γ w : ℝ)
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    AEDisjoint (volume : Measure (Fin (n + 1) → ℝ))
      (independentMinimumSector n γ w i) (independentMinimumSector n γ w j) := by
  change (volume : Measure (Fin (n + 1) → ℝ))
    (independentMinimumSector n γ w i ∩ independentMinimumSector n γ w j) = 0
  have hsub : (independentMinimumSector n γ w i ∩ independentMinimumSector n γ w j) ⊆
      {x : Fin (n + 1) → ℝ | x i = x j} := by
    intro x hx
    have hi := hx.1
    have hj := hx.2
    change x ∈ sourceSimplex n γ w ∧ x i ≤ w - (∑ k, x k) ∧
      (∀ k, x i ≤ x k) at hi
    change x ∈ sourceSimplex n γ w ∧ x j ≤ w - (∑ k, x k) ∧
      (∀ k, x j ≤ x k) at hj
    exact le_antisymm (hi.2.2 j) (hj.2.2 i)
  exact measure_mono_null hsub (any_independent_tie_null n i j hij)

/-- Independent and dependent minimum sectors overlap only on a null tie. -/
theorem dependent_independent_aedisjoint (n : ℕ) (γ w : ℝ)
    (i : Fin (n + 1)) :
    AEDisjoint (volume : Measure (Fin (n + 1) → ℝ))
      (dependentMinimumSector n γ w) (independentMinimumSector n γ w i) := by
  change (volume : Measure (Fin (n + 1) → ℝ))
    (dependentMinimumSector n γ w ∩ independentMinimumSector n γ w i) = 0
  have hsub : (dependentMinimumSector n γ w ∩ independentMinimumSector n γ w i) ⊆
      {x : Fin (n + 1) → ℝ | x i = w - ∑ k, x k} := by
    intro x hx
    have hd := hx.1
    have hi := hx.2
    change x ∈ sourceSimplex n γ w ∧
      (∀ k, w - (∑ j, x j) ≤ x k) at hd
    change x ∈ sourceSimplex n γ w ∧ x i ≤ w - (∑ j, x j) ∧
      (∀ k, x i ≤ x k) at hi
    exact le_antisymm hi.2.1 (hd.2 i)
  exact measure_mono_null hsub (dependent_tie_null n w i)

/-- Exact finite (n+2)-way minimum disintegration for the literal
    reciprocal-simplex integral, given integrability of its source kernel.
    This is a conditional integration lemma, not a new axiom or PNT premise. -/
theorem minimum_partition_exact (n : ℕ) (γ w : ℝ)
    (hfin : IntegrableOn
      (fun x : Fin (n + 1) → ℝ => (∏ j, (x j)⁻¹) * (w - ∑ j, x j)⁻¹)
      (sourceSimplex n γ w)) :
    (∫ x in sourceSimplex n γ w,
      (∏ j, (x j)⁻¹) * (w - ∑ j, x j)⁻¹) =
      (n + 2 : ℝ) * (∫ x in dependentMinimumSector n γ w,
        (∏ j, (x j)⁻¹) * (w - ∑ j, x j)⁻¹) := by
  classical
  let f : (Fin (n + 1) → ℝ) → ℝ :=
    fun x => (∏ j, (x j)⁻¹) * (w - ∑ j, x j)⁻¹
  let s : Option (Fin (n + 1)) → Set (Fin (n + 1) → ℝ)
    | none => dependentMinimumSector n γ w
    | some i => independentMinimumSector n γ w i
  have hm (o : Option (Fin (n + 1))) : NullMeasurableSet (s o) volume := by
    cases o with
    | none => exact (dependent_minimum_measurable n γ w).nullMeasurableSet
    | some i => exact (independent_minimum_measurable n γ w i).nullMeasurableSet
  have hd : Pairwise (fun a b =>
      AEDisjoint (volume : Measure (Fin (n + 1) → ℝ)) (s a) (s b)) := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => exact False.elim (hab rfl)
      | some i => exact dependent_independent_aedisjoint n γ w i
    | some i =>
      cases b with
      | none => exact (dependent_independent_aedisjoint n γ w i).symm
      | some j =>
        have hij : i ≠ j := by
          intro heq
          exact hab (congrArg some heq)
        exact independent_minimum_aedisjoint n γ w i j hij
  have hc : (⋃ o, s o) = sourceSimplex n γ w := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨o, ho⟩
      cases o with
      | none => exact ho.1
      | some i => exact ho.1
    · intro x hx
      rw [minimum_sectors_cover] at hx
      rcases hx with ha | hb
      · exact Set.mem_iUnion.mpr ⟨none, ha⟩
      · rcases Set.mem_iUnion.mp hb with ⟨i, hi⟩
        exact Set.mem_iUnion.mpr ⟨some i, hi⟩
  have hsum :
      (∫ x in sourceSimplex n γ w, f x) =
      ∑ o : Option (Fin (n + 1)), ∫ x in s o, f x := by
    have hh := MeasureTheory.hasSum_integral_iUnion_ae hm hd (by rwa [hc])
    rw [hc] at hh
    exact ((hasSum_fintype
      (fun o : Option (Fin (n + 1)) => ∫ x in s o, f x)).unique hh).symm
  calc
    (∫ x in sourceSimplex n γ w, f x) =
        ∑ o : Option (Fin (n + 1)), ∫ x in s o, f x := hsum
    _ = (n + 2 : ℝ) * (∫ x in dependentMinimumSector n γ w, f x) := by
      rw [Fintype.sum_option]
      change (∫ x in dependentMinimumSector n γ w, f x) +
        (∑ i : Fin (n + 1), ∫ x in independentMinimumSector n γ w i, f x) = _
      dsimp only [f]
      simp_rw [minimum_sector_integral_equality]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

end Green64Analytic.MinDisintegration

/- Transitive Lean-kernel axiom audit: no user-defined axiom, sorryAx or admit allowed. -/

end

/-! ## MultiplierScaling -/

section

namespace Green64SourceC6

/-- Literal source comparison-cell sizes U1,U2 and H'=U1*U2.
The C6 bracket normalized by product-atom squared masses has this exact
four-term expansion, including the second 1/U2. -/
theorem source_minor_arc_scale_identity
    (U1 U2 r t : ℝ) (hU1 : 0 < U1) (hU2 : 0 < U2) (hr : 0 < r) :
    (U1 + (1 + U2/r) * (U1+r*t)) / (U1*U2) =
      2/U2 + 1/r + t/U1 + r*t/(U1*U2) := by
  field_simp
  ring

/-- Swallow the harmless second diagonal contribution into the fixed
source implicit constant, with all denominator and sign conditions. -/
theorem source_minor_arc_scale_bound
    (U1 U2 r t : ℝ) (hU1 : 0 < U1) (hU2 : 0 < U2)
    (hr : 0 < r) (ht : 0 ≤ t) :
    (U1 + (1 + U2/r) * (U1+r*t)) / (U1*U2) ≤
      2 * (1/U2 + 1/r + t/U1 + r*t/(U1*U2)) := by
  rw [source_minor_arc_scale_identity U1 U2 r t hU1 hU2 hr]
  have h1 : (0 : ℝ) ≤ 1/U2 := by positivity
  have h2 : (0 : ℝ) ≤ 1/r := by positivity
  have h3 : (0 : ℝ) ≤ t/U1 := div_nonneg ht hU1.le
  have h4 : (0 : ℝ) ≤ r*t/(U1*U2) := by positivity
  have hsum : (0 : ℝ) ≤ 1/r + t/U1 + r*t/(U1*U2) := by
    linarith [h2,h3,h4]
  calc
    _ ≤ 2/U2 + 2*(1/r+t/U1+r*t/(U1*U2)) := by linarith
    _ = 2*(1/U2+1/r+t/U1+r*t/(U1*U2)) := by ring

end Green64SourceC6

end

/-! ## P2Abel -/

section

open Finset
namespace Green64Analytic.LongPrime

theorem variation_telescope (w : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (w i - w (i+1))) = w 0 - w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem p2_abel_complex_prefix_bound
    (a : ℕ → ℂ) (w : ℕ → ℝ) (n : ℕ) (E : ℝ)
    (hE : 0 ≤ E) (hw0 : 0 ≤ w 0)
    (hmono : ∀ i, i + 1 < n → w (i + 1) ≤ w i)
    (hlast : 0 < n → 0 ≤ w (n - 1))
    (hprefix : ∀ k, k ≤ n → ‖∑ i ∈ Finset.range k, a i‖ ≤ E) :
    ‖∑ i ∈ Finset.range n, (w i : ℂ) * a i‖ ≤ E * w 0 := by
  by_cases hn : n = 0
  · simp [hn, mul_nonneg hE hw0]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hparts :
      (∑ i ∈ Finset.range n, (w i : ℂ) * a i) =
      (w (n - 1) : ℂ) * (∑ i ∈ Finset.range n, a i) -
      ∑ i ∈ Finset.range (n - 1),
        ((w (i + 1) - w i : ℝ) : ℂ) * (∑ j ∈ Finset.range (i+1), a j) := by
    simpa only [smul_eq_mul, Complex.ofReal_sub] using
      (Finset.sum_range_by_parts (fun i => (w i : ℂ)) a n)
  rw [hparts]
  have hlast_bound :
      ‖(w (n - 1) : ℂ) * (∑ i ∈ Finset.range n, a i)‖ ≤ E * w (n - 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hlast hnpos)]
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left (hprefix n le_rfl) (hlast hnpos))
  have hsum_bound :
      ‖∑ i ∈ Finset.range (n - 1),
        ((w (i + 1) - w i : ℝ) : ℂ) * (∑ j ∈ Finset.range (i+1), a j)‖ ≤
      ∑ i ∈ Finset.range (n - 1), E * (w i - w (i + 1)) := by
    apply norm_sum_le_of_le
    intro i hi
    have hiN : i + 1 < n := by
      have : i < n - 1 := Finset.mem_range.mp hi
      omega
    have hwi : w (i + 1) ≤ w i := hmono i hiN
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hwi), neg_sub]
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left
        (hprefix (i + 1) (by omega)) (sub_nonneg.mpr hwi))
  calc
    ‖(w (n - 1) : ℂ) * (∑ i ∈ Finset.range n, a i) -
      ∑ i ∈ Finset.range (n - 1),
        ((w (i + 1) - w i : ℝ) : ℂ) * (∑ j ∈ Finset.range (i+1), a j)‖ ≤
      ‖(w (n - 1) : ℂ) * (∑ i ∈ Finset.range n, a i)‖ +
      ‖∑ i ∈ Finset.range (n - 1),
        ((w (i + 1) - w i : ℝ) : ℂ) * (∑ j ∈ Finset.range (i+1), a j)‖ :=
          norm_sub_le _ _
    _ ≤ E * w (n - 1) +
      ∑ i ∈ Finset.range (n - 1), E * (w i - w (i + 1)) :=
        add_le_add hlast_bound hsum_bound
    _ = E * w 0 := by
      rw [← Finset.mul_sum, variation_telescope]
      ring
end Green64Analytic.LongPrime

end

/-! ## PNTRemainder -/

section

open intervalIntegral MeasureTheory
namespace Green64Analytic.ReciprocalPrimeGrid

/-- A pointwise PNT remainder bound after reciprocal weighting. -/
theorem pnt2_integrand_bound (U t C E : ℝ) (hU : 1 < U)
    (ht : U ≤ t) (hC : 0 ≤ C)
    (he : |E| ≤ C * t / (Real.log t) ^ 2) :
    |E / t ^ 2| ≤ (C / (Real.log U) ^ 2) * t⁻¹ := by
  have ht0 : 0 < t := lt_of_lt_of_le (lt_trans zero_lt_one hU) ht
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have hlogt : 0 < Real.log t := Real.log_pos (lt_of_lt_of_le hU ht)
  have hlog : Real.log U ≤ Real.log t :=
    Real.log_le_log (lt_trans zero_lt_one hU) ht
  have hratio : C / (Real.log t) ^ 2 ≤ C / (Real.log U) ^ 2 := by
    gcongr
  calc
    |E / t ^ 2| = |E| / t ^ 2 := by simp [abs_div, abs_of_pos ht0]
    _ ≤ (C * t / (Real.log t) ^ 2) / t ^ 2 :=
      div_le_div_of_nonneg_right he (sq_nonneg _)
    _ = (C / (Real.log t) ^ 2) * t⁻¹ := by
      field_simp
    _ ≤ (C / (Real.log U) ^ 2) * t⁻¹ :=
      mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr ht0.le)

/-- Quantified remainder integral over a compact prime-counting interval. -/
theorem pnt2_integral_error (E : ℝ → ℝ) (U V C : ℝ)
    (hU : 1 < U) (hUV : U ≤ V) (hC : 0 ≤ C)
    (hE : ∀ t ∈ Set.Icc U V,
       |E t| ≤ C * t / (Real.log t) ^ 2) :
    |∫ t in U..V, E t / t ^ 2| ≤
      (C / (Real.log U) ^ 2) * Real.log (V / U) := by
  have hU0 : 0 < U := lt_trans zero_lt_one hU
  have hV0 : 0 < V := hU0.trans_le hUV
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) MeasureTheory.volume U V := by
    apply intervalIntegrable_inv (f := fun t : ℝ => t)
    · intro t ht
      apply ne_of_gt
      have htu : U ≤ t := by
        have htc : t ∈ Set.Icc U V := (Set.uIcc_of_le hUV) ▸ ht
        exact htc.1
      exact hU0.trans_le htu
    · exact continuousOn_id
  have hg : IntervalIntegrable
      (fun t : ℝ => (C / (Real.log U) ^ 2) * t⁻¹)
      MeasureTheory.volume U V := hinv.const_mul _
  have hbound : |∫ t in U..V, E t / t ^ 2| ≤
      ∫ t in U..V, (C / (Real.log U) ^ 2) * t⁻¹ := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hUV
    · filter_upwards [] with t
      intro ht
      rw [Real.norm_eq_abs]
      apply pnt2_integrand_bound U t C (E t) hU ht.1.le hC
      exact hE t ⟨ht.1.le, ht.2⟩
    · exact hg

  calc
    |∫ t in U..V, E t / t ^ 2| ≤
      ∫ t in U..V, (C / (Real.log U) ^ 2) * t⁻¹ := hbound
    _ = (C / (Real.log U) ^ 2) * (∫ t in U..V, t⁻¹) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (C / (Real.log U) ^ 2) * Real.log (V / U) := by
      rw [integral_inv_of_pos hU0 hV0]

/-- PNT2 gives the normalized boundary error at a fixed endpoint. -/
theorem pnt2_endpoint_error (t C E : ℝ) (ht : 1 < t)
    (he : |E| ≤ C * t / (Real.log t) ^ 2) :
    |E / t| ≤ C / (Real.log t) ^ 2 := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  calc
    |E / t| = |E| / t := by simp [abs_div, abs_of_pos ht0]
    _ ≤ (C * t / (Real.log t) ^ 2) / t :=
      div_le_div_of_nonneg_right he ht0.le
    _ = C / (Real.log t) ^ 2 := by
      field_simp

/-- The PNT2 error contribution to partial summation, quantified uniformly. -/
theorem pnt2_abel_remainder (E : ℝ → ℝ) (U V C : ℝ)
    (hU : 1 < U) (hUV : U ≤ V) (hC : 0 ≤ C)
    (hE : ∀ t ∈ Set.Icc U V,
       |E t| ≤ C * t / (Real.log t) ^ 2) :
    |E V / V - E U / U + ∫ t in U..V, E t / t ^ 2| ≤
      C / (Real.log V) ^ 2 + C / (Real.log U) ^ 2 +
      (C / (Real.log U) ^ 2) * Real.log (V / U) := by
  have hv : 1 < V := hU.trans_le hUV
  have hboundV := pnt2_endpoint_error V C (E V) hv (hE V ⟨hUV, le_rfl⟩)
  have hboundU := pnt2_endpoint_error U C (E U) hU (hE U ⟨le_rfl, hUV⟩)
  have hint := pnt2_integral_error E U V C hU hUV hC hE

  have htri : |E V / V - E U / U + ∫ t in U..V, E t / t ^ 2| ≤
      |E V / V| + |E U / U| + |∫ t in U..V, E t / t ^ 2| := by
    calc
      |E V / V - E U / U + ∫ t in U..V, E t / t ^ 2| ≤
        |E V / V - E U / U| + |∫ t in U..V, E t / t ^ 2| := abs_add_le _ _
      _ ≤ |E V / V| + |E U / U| + |∫ t in U..V, E t / t ^ 2| := by
        have hsub : |E V / V - E U / U| ≤ |E V / V| + |E U / U| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le (E V / V) (-(E U / U)))
        linarith
  linarith

/-- Explicit O(1/L) error of PNT2 after exponential change of coordinates. -/
theorem pnt2_log_window_error (E : ℝ → ℝ) (a M L u v C : ℝ)
    (ha : 0 < a) (hL : 1 ≤ a * L)
    (hau : a ≤ u) (huv : u ≤ v) (hvM : v ≤ M) (hC : 0 ≤ C)
    (hE : ∀ t ∈ Set.Icc (Real.exp (u * L)) (Real.exp (v * L)),
       |E t| ≤ C * t / (Real.log t) ^ 2) :
    |E (Real.exp (v * L)) / Real.exp (v * L) -
      E (Real.exp (u * L)) / Real.exp (u * L) +
      ∫ t in Real.exp (u * L)..Real.exp (v * L), E t / t ^ 2| ≤
      C * (2 + (M - a) * L) / (a * L) ^ 2 := by
  have hLp : 0 < L := by
    by_contra hn
    have hn' : L ≤ 0 := le_of_not_gt hn
    have : a * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hn'
    linarith
  have haLp : 0 < a * L := lt_of_lt_of_le zero_lt_one hL
  have hauL : a * L ≤ u * L := mul_le_mul_of_nonneg_right hau hLp.le
  have huvL : u * L ≤ v * L := mul_le_mul_of_nonneg_right huv hLp.le
  have hU : 1 < Real.exp (u * L) := by
    simpa using (Real.exp_lt_exp.mpr (haLp.trans_le hauL) :
      Real.exp 0 < Real.exp (u * L))
  have hUV : Real.exp (u * L) ≤ Real.exp (v * L) := Real.exp_le_exp.mpr huvL

  have hlog : Real.log (Real.exp (v * L) / Real.exp (u * L)) =
      (v - u) * L := by
    rw [Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp]
    ring
  have hq (z : ℝ) (hz : a ≤ z) : C / (z * L) ^ 2 ≤ C / (a * L) ^ 2 := by
    have hzl : a * L ≤ z * L := mul_le_mul_of_nonneg_right hz hLp.le
    gcongr
  have hwidth : (v - u) * L ≤ (M - a) * L := by
    apply mul_le_mul_of_nonneg_right _ hLp.le
    linarith
  have hwidth0 : 0 ≤ (v - u) * L := mul_nonneg (sub_nonneg.mpr huv) hLp.le
  have hterm :
      C / (u * L) ^ 2 * ((v - u) * L) ≤
      C / (a * L) ^ 2 * ((M - a) * L) := by
    apply mul_le_mul (hq u hau) hwidth hwidth0
    exact div_nonneg hC (sq_nonneg _)
  have hmain := pnt2_abel_remainder E (Real.exp (u * L))
    (Real.exp (v * L)) C hU hUV hC hE
  rw [Real.log_exp, Real.log_exp, hlog] at hmain
  calc
    _ ≤ C / (v * L) ^ 2 + C / (u * L) ^ 2 +
      (C / (u * L) ^ 2) * ((v - u) * L) := hmain
    _ ≤ C / (a * L) ^ 2 + C / (a * L) ^ 2 +
      (C / (a * L) ^ 2) * ((M - a) * L) := by
        linarith [hq v (hau.trans huv), hq u hau, hterm]
    _ = C * (2 + (M - a) * L) / (a * L) ^ 2 := by ring

/-- A single PNT2 bound controls every compact logarithmic subinterval. -/
theorem uniform_pnt2_remainder (E : ℝ → ℝ) (a M L C : ℝ)
    (ha : 0 < a) (hL : 1 ≤ a * L) (hC : 0 ≤ C)
    (hE : ∀ t, Real.exp (a * L) ≤ t →
       |E t| ≤ C * t / (Real.log t) ^ 2) :
    ∀ u v, a ≤ u → u ≤ v → v ≤ M →
    |E (Real.exp (v * L)) / Real.exp (v * L) -
       E (Real.exp (u * L)) / Real.exp (u * L) +
       ∫ t in Real.exp (u * L)..Real.exp (v * L), E t / t ^ 2| ≤
       C * (2 + (M - a) * L) / (a * L) ^ 2 := by
  have hLp : 0 < L := by
    by_contra hn
    have hn' : L ≤ 0 := le_of_not_gt hn
    have : a * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hn'
    linarith
  intro u v hau huv hvM
  apply pnt2_log_window_error E a M L u v C ha hL hau huv hvM hC
  intro t ht
  apply hE t
  have hal : a * L ≤ u * L := mul_le_mul_of_nonneg_right hau hLp.le
  exact (Real.exp_le_exp.mpr hal).trans ht.1

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## PrimeMeasureConvergence -/

section

open scoped BigOperators
open intervalIntegral MeasureTheory
namespace Green64Analytic.ReciprocalPrimeGrid

/-- Simple explicit elementary PNT main term; no Li primitive needed. -/
noncomputable def primeRemainder (t : ℝ) : ℝ :=
    primeCountReal t - t / Real.log t

theorem prime_count_interval_integrable (U V : ℝ)
    (hU : 1 < U) (hUV : U ≤ V) :
    IntervalIntegrable (fun t : ℝ => primeCountReal t / t ^ 2)
      MeasureTheory.volume U V := by
  have hpos (t : ℝ) (ht : t ∈ Set.Icc U V) : 0 < t :=
    (lt_trans zero_lt_one hU).trans_le ht.1
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹)
      (Set.Icc U V) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      exact pow_ne_zero 2 (ne_of_gt (hpos t ht))
  have hbase : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹)
      (Set.Icc U V) := hcont.integrableOn_compact isCompact_Icc
  have hsum : IntegrableOn
      (fun t : ℝ => (t ^ 2)⁻¹ * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeIndicator k))
      (Set.Icc U V) :=
    integrableOn_mul_sum_Icc (m := 0) primeIndicator
      (lt_trans zero_lt_one hU).le hbase
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hUV).2
  apply IntegrableOn.congr_fun hsum
  · intro t ht
    simp only [primeCountReal, div_eq_mul_inv]
    ring
  · exact measurableSet_Icc

theorem reciprocal_density_integrable (U V : ℝ)
    (hU : 1 < U) (hUV : U ≤ V) :
    IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t)
      MeasureTheory.volume U V := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hUV]
  have hpos (t : ℝ) (ht : t ∈ Set.Icc U V) : 1 < t :=
    hU.trans_le ht.1
  have hlog : ContinuousOn Real.log (Set.Icc U V) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (lt_trans zero_lt_one (hpos t ht))
  apply ContinuousOn.div
  · apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    exact ne_of_gt (lt_trans zero_lt_one (hpos t ht))
  · exact hlog
  · intro t ht
    exact ne_of_gt (Real.log_pos (hpos t ht))

/-- Rewrite the error integrand against the exact elementary PNT main term. -/
theorem prime_integral_error_identity (U V : ℝ)
    (hU : 1 < U) (hUV : U ≤ V) :
    (∫ t in U..V, primeRemainder t / t ^ 2) =
      (∫ t in U..V, primeCountReal t / t ^ 2) -
      (∫ t in U..V, t⁻¹ / Real.log t) := by
  have hP := prime_count_interval_integrable U V hU hUV
  have hQ := reciprocal_density_integrable U V hU hUV
  rw [← intervalIntegral.integral_sub hP hQ]
  apply intervalIntegral.integral_congr
  intro t ht
  have hpos : 0 < t := (lt_trans zero_lt_one hU).trans_le
    ((Set.uIcc_of_le hUV).symm ▸ ht).1
  have hlog : Real.log t ≠ 0 := ne_of_gt
    (Real.log_pos (hU.trans_le (((Set.uIcc_of_le hUV).symm ▸ ht).1)))
  simp only [primeRemainder]
  field_simp

/-- Exact Stieltjes/Abel decomposition of reciprocal-prime mass. -/
theorem prime_reciprocal_error_identity (U V : ℝ)
    (hU : 1 < U) (hUV : U ≤ V) :
    (∑ k ∈ Finset.Ioc ⌊U⌋₊ ⌊V⌋₊,
         if k.Prime then (k : ℝ)⁻¹ else 0) -
      Real.log (Real.log V / Real.log U) =
      primeRemainder V / V - primeRemainder U / U +
      (∫ t in U..V, primeRemainder t / t ^ 2) +
      ((Real.log V)⁻¹ - (Real.log U)⁻¹) := by
  have hV : 1 < V := hU.trans_le hUV
  have hP (t : ℝ) (ht : 1 < t) :
      primeCountReal t / t = primeRemainder t / t + (Real.log t)⁻¹ := by
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
    unfold primeRemainder
    field_simp
    ring
  have hAbel := prime_reciprocal_abel U V hU hUV
  have hInt := prime_integral_error_identity U V hU hUV
  have hLog := integral_inv_log U V hU hUV
  rw [hAbel, ← hLog, hP V hV, hP U hU]
  linarith

/-- Quantified PNT2 implies reciprocal-prime interval discrepancy. -/
theorem prime_reciprocal_error_bound (U V C : ℝ)
    (hU : 1 < U) (hUV : U ≤ V) (hC : 0 ≤ C)
    (hPNT : ∀ t ∈ Set.Icc U V,
        |primeRemainder t| ≤ C * t / (Real.log t) ^ 2) :
    |(∑ k ∈ Finset.Ioc ⌊U⌋₊ ⌊V⌋₊,
         if k.Prime then (k : ℝ)⁻¹ else 0) -
      Real.log (Real.log V / Real.log U)| ≤
      C / (Real.log V) ^ 2 + C / (Real.log U) ^ 2 +
      (C / (Real.log U) ^ 2) * Real.log (V / U) +
      (Real.log U)⁻¹ := by
  have hE := pnt2_abel_remainder primeRemainder U V C hU hUV hC hPNT
  have hId := prime_reciprocal_error_identity U V hU hUV
  have hLogU : 0 < Real.log U := Real.log_pos hU
  have hLogV : 0 < Real.log V := Real.log_pos (hU.trans_le hUV)
  have hlogle : Real.log U ≤ Real.log V :=
    Real.log_le_log (lt_trans zero_lt_one hU) hUV
  have hInvLE : (Real.log V)⁻¹ ≤ (Real.log U)⁻¹ :=
    inv_anti₀ hLogU hlogle
  have hInvDiff : |(Real.log V)⁻¹ - (Real.log U)⁻¹| ≤
      (Real.log U)⁻¹ := by
    rw [abs_of_nonpos (sub_nonpos.mpr hInvLE)]
    linarith [inv_nonneg.mpr hLogV.le]
  rw [hId]
  calc
    |primeRemainder V / V - primeRemainder U / U +
      (∫ t in U..V, primeRemainder t / t ^ 2) +
      ((Real.log V)⁻¹ - (Real.log U)⁻¹)| ≤
        |primeRemainder V / V - primeRemainder U / U +
          (∫ t in U..V, primeRemainder t / t ^ 2)| +
        |(Real.log V)⁻¹ - (Real.log U)⁻¹| := abs_add_le _ _
    _ ≤ C / (Real.log V) ^ 2 + C / (Real.log U) ^ 2 +
      (C / (Real.log U) ^ 2) * Real.log (V / U) +
      (Real.log U)⁻¹ := add_le_add hE hInvDiff

/-- A fixed positive logarithmic compact has uniform reciprocal-prime interval error. -/
theorem uniform_prime_reciprocal_log_error (a M L C : ℝ)
    (ha : 0 < a) (hL : 1 ≤ a * L) (hC : 0 ≤ C)
    (hPNT : ∀ t, Real.exp (a * L) ≤ t →
       |primeRemainder t| ≤ C * t / (Real.log t) ^ 2) :
    ∀ u v, a ≤ u → u ≤ v → v ≤ M →
    |(∑ k ∈ Finset.Ioc ⌊Real.exp (u * L)⌋₊ ⌊Real.exp (v * L)⌋₊,
        if k.Prime then (k : ℝ)⁻¹ else 0) - Real.log (v / u)| ≤
      C * (2 + (M - a) * L) / (a * L) ^ 2 + (a * L)⁻¹ := by
  have hLp : 0 < L := by
    by_contra hn
    have hn' : L ≤ 0 := le_of_not_gt hn
    have : a * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hn'
    linarith
  have haLp : 0 < a * L := lt_of_lt_of_le zero_lt_one hL
  intro u v hau huv hvM
  have huLp : 0 < u * L := haLp.trans_le
    (mul_le_mul_of_nonneg_right hau hLp.le)
  have hvLp : 0 < v * L := huLp.trans_le
    (mul_le_mul_of_nonneg_right huv hLp.le)
  have hU : 1 < Real.exp (u * L) := by
    simpa using (Real.exp_lt_exp.mpr huLp : Real.exp 0 < Real.exp (u * L))
  have hUV : Real.exp (u * L) ≤ Real.exp (v * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right huv hLp.le)
  have hratio : (v * L) / (u * L) = v / u := by
    have hu0 : u ≠ 0 := ne_of_gt (ha.trans_le hau)
    have hL0 : L ≠ 0 := ne_of_gt hLp
    field_simp
  have hLog : Real.log (Real.log (Real.exp (v * L)) /
      Real.log (Real.exp (u * L))) = Real.log (v / u) := by
    simp only [Real.log_exp, hratio]
  have hId := prime_reciprocal_error_identity (Real.exp (u * L))
    (Real.exp (v * L)) hU hUV
  rw [hLog] at hId

  simp only [Real.log_exp] at hId
  have hE := uniform_pnt2_remainder primeRemainder a M L C ha hL hC
    hPNT u v hau huv hvM
  have hUleV : u * L ≤ v * L :=
    mul_le_mul_of_nonneg_right huv hLp.le
  have hAleU : a * L ≤ u * L :=
    mul_le_mul_of_nonneg_right hau hLp.le
  have hInv1 : (v * L)⁻¹ ≤ (u * L)⁻¹ :=
    inv_anti₀ huLp hUleV
  have hInv2 : (u * L)⁻¹ ≤ (a * L)⁻¹ :=
    inv_anti₀ haLp hAleU
  have hInv : |(v * L)⁻¹ - (u * L)⁻¹| ≤ (a * L)⁻¹ := by
    rw [abs_of_nonpos (sub_nonpos.mpr hInv1)]
    linarith [inv_nonneg.mpr hvLp.le]
  rw [hId]
  calc
    |primeRemainder (Real.exp (v * L)) / Real.exp (v * L) -
        primeRemainder (Real.exp (u * L)) / Real.exp (u * L) +
        (∫ t in Real.exp (u * L)..Real.exp (v * L),
          primeRemainder t / t ^ 2) +
        ((v * L)⁻¹ - (u * L)⁻¹)| ≤
        |primeRemainder (Real.exp (v * L)) / Real.exp (v * L) -
          primeRemainder (Real.exp (u * L)) / Real.exp (u * L) +
          (∫ t in Real.exp (u * L)..Real.exp (v * L),
            primeRemainder t / t ^ 2)| +
          |(v * L)⁻¹ - (u * L)⁻¹| := abs_add_le _ _
    _ ≤ C * (2 + (M - a) * L) / (a * L) ^ 2 +
          (a * L)⁻¹ := add_le_add hE hInv

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## PrimeGridConvergence -/

section

open scoped BigOperators
namespace Green64Analytic.ReciprocalPrimeGrid

/-- The literal one-cell reciprocal-prime mass, counting each positive prime exactly once. -/
noncomputable def reciprocalPrimeCell (L u v : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc ⌊Real.exp (u * L)⌋₊ ⌊Real.exp (v * L)⌋₊,
    if p.Prime then (p : ℝ)⁻¹ else 0

/-- The exact limiting reciprocal density cell. -/
noncomputable def logCell (u v : ℝ) : ℝ := Real.log (v / u)

theorem reciprocalPrimeCell_nonneg (L u v : ℝ) :
    0 ≤ reciprocalPrimeCell L u v := by
  unfold reciprocalPrimeCell
  apply Finset.sum_nonneg
  intro p hp
  split_ifs <;> positivity

theorem logCell_bounds (a M u v : ℝ)
    (ha : 0 < a) (hau : a ≤ u) (huv : u ≤ v) (hvM : v ≤ M) :
    0 ≤ logCell u v ∧ logCell u v ≤ Real.log (M / a) := by
  have hu0 : 0 < u := ha.trans_le hau
  have hv0 : 0 < v := hu0.trans_le huv
  have hM0 : 0 < M := hv0.trans_le hvM
  have hle1 : Real.log u ≤ Real.log v := Real.log_le_log hu0 huv
  have hle2 : Real.log v ≤ Real.log M := Real.log_le_log hv0 hvM
  have hle3 : Real.log a ≤ Real.log u := Real.log_le_log ha hau
  unfold logCell
  rw [Real.log_div (ne_of_gt hv0) (ne_of_gt hu0),
    Real.log_div (ne_of_gt hM0) (ne_of_gt ha)]
  constructor <;> linarith

/-- Exact PNT2 plus product grid telescoping gives uniform mass on every fixed grid union. -/
theorem prime_grid_uniform_bound (d k : ℕ)
    (a M L C : ℝ) (u v : Fin k → ℝ)
    (ha : 0 < a) (haM : a ≤ M) (hL : 1 ≤ a * L) (hC : 0 ≤ C)
    (hcells : ∀ j, a ≤ u j ∧ u j ≤ v j ∧ v j ≤ M)
    (hPNT : ∀ t, Real.exp (a * L) ≤ t →
       |primeRemainder t| ≤ C * t / (Real.log t) ^ 2)
    (S : Finset (Fin d → Fin k)) :
    |(∑ c ∈ S, ∏ i : Fin d, reciprocalPrimeCell L (u (c i)) (v (c i))) -
      (∑ c ∈ S, ∏ i : Fin d, logCell (u (c i)) (v (c i)))| ≤
    (k : ℝ) ^ d * ((d : ℝ) *
      (C * (2 + (M - a) * L) / (a * L) ^ 2 + (a * L)⁻¹) *
      (Real.log (M / a) +
       (C * (2 + (M - a) * L) / (a * L) ^ 2 + (a * L)⁻¹)) ^ (d - 1)) := by
  let H := Real.log (M / a)
  let ε := C * (2 + (M - a) * L) / (a * L) ^ 2 + (a * L)⁻¹
  have hH : 0 ≤ H := by
    dsimp [H]
    apply Real.log_nonneg
    exact (le_div_iff₀ ha).mpr (by simpa using haM)
  have hLp : 0 < L := by
    by_contra hn
    have hn' : L ≤ 0 := le_of_not_gt hn
    have : a * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hn'
    linarith
  have hε : 0 ≤ ε := by
    dsimp [ε]
    have := sub_nonneg.mpr haM
    positivity
  have hμ0 : ∀ i : Fin d, ∀ j : Fin k,
       0 ≤ reciprocalPrimeCell L (u j) (v j) := by
    intros i j
    exact reciprocalPrimeCell_nonneg L (u j) (v j)
  have hν0 : ∀ i : Fin d, ∀ j : Fin k,
       0 ≤ logCell (u j) (v j) := by
    intros i j
    exact (logCell_bounds a M (u j) (v j) ha
      (hcells j).1 (hcells j).2.1 (hcells j).2.2).1
  have hν : ∀ i : Fin d, ∀ j : Fin k,
       logCell (u j) (v j) ≤ H := by
    intros i j
    exact (logCell_bounds a M (u j) (v j) ha
      (hcells j).1 (hcells j).2.1 (hcells j).2.2).2
  have hgap : ∀ i : Fin d, ∀ j : Fin k,
       |reciprocalPrimeCell L (u j) (v j) - logCell (u j) (v j)| ≤ ε := by
    intro i j
    exact uniform_prime_reciprocal_log_error a M L C ha hL hC
      hPNT (u j) (v j) (hcells j).1 (hcells j).2.1 (hcells j).2.2
  simpa only [H, ε] using
    (fixed_grid_from_interval_errors d k
      (fun _ j => reciprocalPrimeCell L (u j) (v j))
      (fun _ j => logCell (u j) (v j)) H ε hH hε hμ0 hν0 hν hgap S)

end Green64Analytic.ReciprocalPrimeGrid

end

/-! ## PhaseBins -/

section

namespace Green64SourceC6

noncomputable def fracPhase (alpha : ℝ) (d : ℤ) : ℝ :=
  alpha * (d : ℝ) - (⌊alpha * (d : ℝ)⌋ : ℝ)

theorem fracPhase_range (alpha : ℝ) (d : ℤ) :
    0 ≤ fracPhase alpha d ∧ fracPhase alpha d < 1 := by
  have hlow := Int.floor_le (alpha * (d : ℝ))
  have hh := Int.lt_floor_add_one (alpha * (d : ℝ))
  unfold fracPhase
  constructor <;> linarith

/-- Pairwise true fractional-phase separation for indices in a short
integer difference, without assuming that fractional order agrees with
integer order. -/
theorem fracPhase_pair_forward (a r d1 d2 : ℤ) (beta : ℝ)
    (hr : 0 < r) (hd : d1 < d2) (hsmall : 2*(d2-d1) ≤ r)
    (hcop : Int.gcd a r = 1)
    (hbeta : |beta| ≤ 1 / ((r : ℝ)^2)) :
    (1 : ℝ)/(2*(r : ℝ)) ≤
      |fracPhase ((a : ℝ)/(r : ℝ)+beta) d2 -
       fracPhase ((a : ℝ)/(r : ℝ)+beta) d1| := by
  let alpha := (a : ℝ)/(r : ℝ)+beta
  let z := ⌊alpha*(d2 : ℝ)⌋ - ⌊alpha*(d1 : ℝ)⌋
  have hsep := short_rational_arc_separation a r (d2-d1) z beta
      hr (by omega) hsmall hcop hbeta
  have heq : alpha * ((d2-d1 : ℤ) : ℝ) - (z : ℝ) =
      fracPhase alpha d2 - fracPhase alpha d1 := by
    change alpha * ((d2-d1 : ℤ) : ℝ) -
      ((⌊alpha*(d2:ℝ)⌋ - ⌊alpha*(d1:ℝ)⌋ : ℤ) : ℝ) =
      (alpha*(d2:ℝ) - (⌊alpha*(d2:ℝ)⌋:ℝ)) -
      (alpha*(d1:ℝ) - (⌊alpha*(d1:ℝ)⌋:ℝ))
    push_cast
    ring
  rw [heq] at hsep
  exact hsep

/-- All distinct indices in one short block have separated
fractional phases, including reversed index order. -/
theorem fracPhase_pair (a r d1 d2 : ℤ) (beta : ℝ)
    (hr : 0 < r) (hne : d1 ≠ d2) (hsmall : 2*|d2-d1| ≤ r)
    (hcop : Int.gcd a r = 1)
    (hbeta : |beta| ≤ 1 / ((r : ℝ)^2)) :
    (1 : ℝ)/(2*(r : ℝ)) ≤
      |fracPhase ((a : ℝ)/(r : ℝ)+beta) d2 -
       fracPhase ((a : ℝ)/(r : ℝ)+beta) d1| := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply fracPhase_pair_forward a r d1 d2 beta hr hlt _ hcop hbeta
    rw [abs_of_nonneg (by omega : 0 ≤ d2-d1)] at hsmall
    exact hsmall
  · have h := fracPhase_pair_forward a r d2 d1 beta hr hgt
      (by rw [abs_of_nonpos (by omega : d2-d1 ≤ 0)] at hsmall; omega)
      hcop hbeta
    simpa [abs_sub_comm] using h

/-- For three source indices in a short block, three increasing fractional
phase locations cannot occupy a common rational cell of width 1/r.
The hypotheses permit any ordering of the original *integer indices*. -/
theorem no_three_source_phases_in_one_cell
    (a r d1 d2 d3 j : ℤ) (beta : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a r = 1)
    (hbeta : |beta| ≤ 1 / ((r : ℝ)^2))
    (hne12 : d1 ≠ d2) (hne23 : d2 ≠ d3)
    (hwidth12 : 2*|d2-d1| ≤ r) (hwidth23 : 2*|d3-d2| ≤ r)
    (horder12 : fracPhase ((a : ℝ)/(r : ℝ)+beta) d1 ≤
      fracPhase ((a : ℝ)/(r : ℝ)+beta) d2)
    (horder23 : fracPhase ((a : ℝ)/(r : ℝ)+beta) d2 ≤
      fracPhase ((a : ℝ)/(r : ℝ)+beta) d3)
    (hcell1 : (j : ℝ)/(r : ℝ) ≤
      fracPhase ((a : ℝ)/(r : ℝ)+beta) d1)
    (hcell3 : fracPhase ((a : ℝ)/(r : ℝ)+beta) d3 <
      ((j+1 : ℤ) : ℝ)/(r : ℝ)) : False := by
  let alpha := (a : ℝ)/(r : ℝ)+beta
  have hsep12 := fracPhase_pair a r d1 d2 beta hr hne12 hwidth12 hcop hbeta
  have hsep23 := fracPhase_pair a r d2 d3 beta hr hne23 hwidth23 hcop hbeta
  have hgap12 : (1 : ℝ)/(2*(r : ℝ)) ≤ fracPhase alpha d2 - fracPhase alpha d1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr horder12)] at hsep12
    exact hsep12
  have hgap23 : (1 : ℝ)/(2*(r : ℝ)) ≤ fracPhase alpha d3 - fracPhase alpha d2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr horder23)] at hsep23
    exact hsep23
  have hspan : fracPhase alpha d3 - fracPhase alpha d1 <
      (1 : ℝ)/(r : ℝ) := by
    have hratio : ((j+1 : ℤ) : ℝ)/(r : ℝ) - (j : ℝ)/(r : ℝ) =
        (1 : ℝ)/(r : ℝ) := by
      push_cast
      ring
    rw [←hratio]
    linarith [hcell1, hcell3]
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  exact no_three_separated_in_one_cell (r : ℝ)
    (fracPhase alpha d1) (fracPhase alpha d2) (fracPhase alpha d3)
    hrR hgap12 hgap23 hspan

end Green64SourceC6

end

/-! ## BinCardinality -/

section

namespace Green64SourceC6

/-- No three pairwise delta-separated reals fit into a half-open cell
of length at most 2 delta. The ordering is completely arbitrary. -/
theorem no_three_unordered_in_cell (delta L U x y z : ℝ)
    (hwidth : U-L ≤ 2*delta)
    (hx : L ≤ x ∧ x < U) (hy : L ≤ y ∧ y < U)
    (hz : L ≤ z ∧ z < U)
    (hxy : delta ≤ |x-y|) (hxz : delta ≤ |x-z|)
    (hyz : delta ≤ |y-z|) : False := by
  have hgap (u v : ℝ) (huv : u ≤ v) (h : delta ≤ |u-v|) :
      delta ≤ v-u := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr huv)] at h
    exact h
  have hyx : delta ≤ |y-x| := by simpa [abs_sub_comm] using hxy
  have hzx : delta ≤ |z-x| := by simpa [abs_sub_comm] using hxz
  have hzy : delta ≤ |z-y| := by simpa [abs_sub_comm] using hyz
  rcases le_total x y with h1 | h1
  · rcases le_total y z with h2 | h2
    · have h12 := hgap x y h1 hxy
      have h23 := hgap y z h2 hyz
      linarith [hx.1, hz.2, hwidth]
    · rcases le_total x z with h3 | h3
      · have h13 := hgap x z h3 hxz
        have h32 := hgap z y h2 hzy
        linarith [hx.1, hy.2, hwidth]
      · have h31 := hgap z x h3 hzx
        have h12 := hgap x y h1 hxy
        linarith [hz.1, hy.2, hwidth]
  · rcases le_total x z with h2 | h2
    · have h21 := hgap y x h1 hyx
      have h13 := hgap x z h2 hxz
      linarith [hy.1, hz.2, hwidth]
    · rcases le_total y z with h3 | h3
      · have h23 := hgap y z h3 hyz
        have h31 := hgap z x h2 hzx
        linarith [hy.1, hx.2, hwidth]
      · have h32 := hgap z y h3 hzy
        have h21 := hgap y x h1 hyx
        linarith [hz.1, hx.2, hwidth]

end Green64SourceC6

namespace Green64SourceC6

/-- Actual source bin-occupancy cardinality ≤2 for ANY finite subset
of an integer block of diameter ≤ r/2, including sparse subsets. -/
theorem source_rational_phase_bin_card_le_two
    (a r j : ℤ) (beta : ℝ) (s : Finset ℤ)
    (hr : 0 < r) (hcop : Int.gcd a r = 1)
    (hbeta : |beta| ≤ 1 / ((r : ℝ)^2))
    (hshort : ∀ d ∈ s, ∀ e ∈ s, 2*|e-d| ≤ r)
    (hcell : ∀ d ∈ s,
      (j : ℝ)/(r : ℝ) ≤ fracPhase ((a : ℝ)/(r : ℝ)+beta) d ∧
      fracPhase ((a : ℝ)/(r : ℝ)+beta) d < ((j+1 : ℤ) : ℝ)/(r : ℝ)) :
    s.card ≤ 2 := by
  by_contra hbad
  have hcard : 2 < s.card := by omega
  obtain ⟨d1, h1, d2, h2, d3, h3, h12, h13, h23⟩ :=
    Finset.two_lt_card.mp hcard
  let delta : ℝ := 1/(2*(r : ℝ))
  let L : ℝ := (j : ℝ)/(r : ℝ)
  let U : ℝ := ((j+1 : ℤ) : ℝ)/(r : ℝ)
  let alpha : ℝ := (a : ℝ)/(r : ℝ)+beta
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hwidth : U - L ≤ 2*delta := by
    dsimp [U,L,delta]
    push_cast
    field_simp
    norm_num
  have hxy : delta ≤ |fracPhase alpha d1 - fracPhase alpha d2| := by
    have hh := fracPhase_pair a r d1 d2 beta hr h12 (hshort d1 h1 d2 h2) hcop hbeta
    simpa only [delta, alpha, abs_sub_comm] using hh
  have hxz : delta ≤ |fracPhase alpha d1 - fracPhase alpha d3| := by
    have hh := fracPhase_pair a r d1 d3 beta hr h13 (hshort d1 h1 d3 h3) hcop hbeta
    simpa only [delta, alpha, abs_sub_comm] using hh
  have hyz : delta ≤ |fracPhase alpha d2 - fracPhase alpha d3| := by
    have hh := fracPhase_pair a r d2 d3 beta hr h23 (hshort d2 h2 d3 h3) hcop hbeta
    simpa only [delta, alpha, abs_sub_comm] using hh
  exact no_three_unordered_in_cell delta L U
    (fracPhase alpha d1) (fracPhase alpha d2) (fracPhase alpha d3)
    hwidth (hcell d1 h1) (hcell d2 h2) (hcell d3 h3)
    hxy hxz hyz

end Green64SourceC6

end

/-! ## C6BinMass -/

section

namespace Green64SourceC6

/-- Finite weighted phase-bin lemma: every index belongs to exactly
one bin and every bin carries at most two indices. Neither coefficients
nor weights must be constant across the original support. -/
theorem sum_le_two_bin_weights (r : ℕ) (s : Finset ℤ)
    (bin : ℤ → ℕ) (f : ℤ → ℝ) (w : ℕ → ℝ)
    (hin : ∀ d ∈ s, bin d < r)
    (hcap : ∀ j ∈ Finset.range r,
      (s.filter (fun d => bin d = j)).card ≤ 2)
    (hf : ∀ d ∈ s, f d ≤ w (bin d))
    (hw : ∀ j ∈ Finset.range r, 0 ≤ w j) :
    (∑ d ∈ s, f d) ≤
      2 * (∑ j ∈ Finset.range r, w j) := by
  classical
  have hpart : (∑ d ∈ s, f d) =
      ∑ j ∈ Finset.range r,
        ∑ d ∈ s.filter (fun d => bin d = j), f d := by
    calc
      _ = ∑ d ∈ s, ∑ j ∈ Finset.range r,
            if bin d = j then f d else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_ite_eq]
        simp [hin d hd]
      _ = ∑ j ∈ Finset.range r, ∑ d ∈ s,
            if bin d = j then f d else 0 := Finset.sum_comm
      _ = ∑ j ∈ Finset.range r,
            ∑ d ∈ s.filter (fun d => bin d = j), f d := by
        simp_rw [Finset.sum_filter]
  calc
    (∑ d ∈ s, f d) =
        ∑ j ∈ Finset.range r,
          ∑ d ∈ s.filter (fun d => bin d = j), f d := hpart
    _ ≤ ∑ j ∈ Finset.range r, 2 * w j := by
      apply Finset.sum_le_sum
      intro j hj
      have hpoint : ∀ d ∈ s.filter (fun d => bin d = j),
          f d ≤ w j := by
        intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hds, heq⟩
        simpa [heq] using hf d hds
      have hsum := Finset.sum_le_card_nsmul
        (s.filter (fun d => bin d = j)) f (w j) hpoint
      rw [nsmul_eq_mul] at hsum
      have hcount : (((s.filter (fun d => bin d = j)).card : ℕ) : ℝ) ≤ 2 := by
        exact_mod_cast hcap j hj
      exact hsum.trans (mul_le_mul_of_nonneg_right hcount (hw j hj))
    _ = 2 * (∑ j ∈ Finset.range r, w j) := by
      rw [Finset.mul_sum]

/-- The actual fractional-frequency bin, with no chosen phase center. -/
noncomputable def sourcePhaseBin (r : ℕ) (alpha : ℝ) (d : ℤ) : ℕ :=
  ⌊(r : ℝ) * fracPhase alpha d⌋₊

theorem sourcePhaseBin_lt (r : ℕ) (alpha : ℝ) (d : ℤ)
    (hr : 0 < r) : sourcePhaseBin r alpha d < r := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hfr := fracPhase_range alpha d
  have hnonneg : 0 ≤ (r : ℝ) * fracPhase alpha d :=
    mul_nonneg hrR.le hfr.1
  rw [sourcePhaseBin, Nat.floor_lt hnonneg]
  exact (mul_lt_mul_of_pos_left hfr.2 hrR).trans_eq (mul_one _)

theorem sourcePhaseBin_cell (r : ℕ) (alpha : ℝ) (d : ℤ)
    (hr : 0 < r) :
    ((sourcePhaseBin r alpha d : ℕ) : ℝ) / (r : ℝ) ≤ fracPhase alpha d ∧
    fracPhase alpha d <
      (((sourcePhaseBin r alpha d + 1 : ℕ) : ℝ)) / (r : ℝ) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hnonneg : 0 ≤ (r : ℝ) * fracPhase alpha d :=
    mul_nonneg hrR.le (fracPhase_range alpha d).1
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one ((r : ℝ) * fracPhase alpha d)
  constructor
  · apply (div_le_iff₀ hrR).2
    simpa only [sourcePhaseBin, mul_comm] using hlo
  · apply (lt_div_iff₀ hrR).2
    simpa only [sourcePhaseBin, Nat.cast_add, Nat.cast_one, mul_comm] using hhi

/-- Every literal rational phase bin in a short shifted integer block
contains at most two indices, including sparse or negative-index sets. -/
theorem sourcePhaseBin_card_le_two
    (a : ℤ) (r : ℕ) (beta : ℝ) (s : Finset ℤ)
    (hr : 0 < r) (hcop : Int.gcd a (r : ℤ) = 1)
    (hbeta : |beta| ≤ 1 / ((r : ℝ)^2))
    (hshort : ∀ d ∈ s, ∀ e ∈ s,
       2 * |e - d| ≤ (r : ℤ)) (j : ℕ) :
    (s.filter (fun d =>
      sourcePhaseBin r ((a : ℝ)/(r : ℝ)+beta) d = j)).card ≤ 2 := by
  classical
  let alpha : ℝ := (a : ℝ)/(r : ℝ)+beta
  let t := s.filter (fun d => sourcePhaseBin r alpha d = j)
  have hshortT : ∀ d ∈ t, ∀ e ∈ t, 2 * |e-d| ≤ (r : ℤ) := by
    intro d hd e he
    exact hshort d (Finset.mem_filter.mp hd).1 e (Finset.mem_filter.mp he).1
  have hcell : ∀ d ∈ t,
    (j : ℝ)/(r : ℝ) ≤ fracPhase alpha d ∧
    fracPhase alpha d < ((j + 1 : ℕ) : ℝ)/(r : ℝ) := by
    intro d hd
    have hbin := (Finset.mem_filter.mp hd).2
    simpa [alpha, hbin] using sourcePhaseBin_cell r alpha d hr
  exact source_rational_phase_bin_card_le_two a (r : ℤ) (j : ℤ)
    beta t (by exact_mod_cast hr) hcop
    (by simpa using hbeta) hshortT (by
      intro d hd
      have hh := hcell d hd
      simpa only [alpha, Int.cast_natCast, Nat.cast_add, Nat.cast_one,
        Int.cast_add, Int.cast_one] using hh)

end Green64SourceC6

end

/-! ## C6HarmonicBins -/

section

namespace Green64SourceC6

/-- Real harmonic sum indexed by zero-based phase bins. -/
noncomputable def harmonicReal (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ)⁻¹)

theorem harmonicReal_eq (n : ℕ) :
    harmonicReal n = (harmonic n : ℝ) := by
  induction n with
  | zero => simp [harmonicReal]
  | succ n ih =>
      unfold harmonicReal
      rw [Finset.sum_range_succ]
      change (∑ k ∈ Finset.range n, (↑(k+1) : ℝ)⁻¹) +
        (↑(n+1) : ℝ)⁻¹ = ↑(harmonic (n+1))
      rw [← harmonicReal, ih, harmonic_succ]
      push_cast
      ring

theorem harmonicReal_reflect (n : ℕ) :
    (∑ k ∈ Finset.range n, (((n-k : ℕ) : ℝ)⁻¹)) = harmonicReal n := by
  calc
    _ = ∑ k ∈ Finset.range n, ((((n-1-k)+1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro k hk
      have h : n-k = n-1-k+1 := by
        have hk' := Finset.mem_range.mp hk
        omega
      rw [h]
    _ = harmonicReal n := by
      simpa [harmonicReal] using
        (Finset.sum_range_reflect
           (fun k : ℕ => (((k+1 : ℕ) : ℝ)⁻¹)) n)

theorem harmonicReal_symmetric (n : ℕ) :
    (∑ k ∈ Finset.range n,
      ((↑(k+1 : ℕ) : ℝ)⁻¹ + ((↑(n-k : ℕ) : ℝ)⁻¹))) =
      2 * harmonicReal n := by
  rw [Finset.sum_add_distrib, harmonicReal_reflect]
  simp only [harmonicReal]
  ring

theorem harmonicReal_log (n : ℕ) :
    harmonicReal n ≤ 2 * Real.log (2 * ((n+2 : ℕ) : ℝ)) := by
  rcases eq_or_lt_of_le (Nat.zero_le n) with hz | hn
  · subst n
    have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    have hh : (0 : ℝ) ≤ 2 * Real.log (4 : ℝ) :=
      mul_nonneg (by norm_num) hlog
    simpa [harmonicReal, show (2 : ℝ) * 2 = 4 by norm_num] using hh
  · have h := source_harmonic_log_budget n (by omega)
    rw [harmonicReal_eq]
    have hnn : (0 : ℝ) < 2 * (n : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
    have hle : (2 * (n : ℝ)) ≤ 2 * ((n+2 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hlog := Real.log_le_log hnn hle
    linarith

/-- Weight for the two terminal phase bins and harmonic interior. -/
noncomputable def harmonicBinWeight (n : ℕ) (P : ℝ) (j : ℕ) : ℝ :=
  if j = 0 ∨ j = n+1 then P else
    (((n+2 : ℕ) : ℝ)/2) *
      (((j : ℝ)⁻¹) + (((n+1-j : ℕ) : ℝ)⁻¹))
theorem harmonicBinWeight_nonneg (n : ℕ) (P : ℝ)
    (hP : 0 ≤ P) (j : ℕ) : 0 ≤ harmonicBinWeight n P j := by
  unfold harmonicBinWeight
  split_ifs
  · exact hP
  · positivity

theorem harmonicBinWeight_zero (n : ℕ) (P : ℝ) :
    harmonicBinWeight n P 0 = P := by
  simp [harmonicBinWeight]

theorem harmonicBinWeight_last (n : ℕ) (P : ℝ) :
    harmonicBinWeight n P (n+1) = P := by
  simp [harmonicBinWeight]

theorem harmonicBinWeight_inner (n k : ℕ) (P : ℝ)
    (hk : k < n) :
    harmonicBinWeight n P (k+1) =
      (((n+2 : ℕ) : ℝ)/2) *
         ((↑(k+1 : ℕ) : ℝ)⁻¹ + (↑(n-k : ℕ) : ℝ)⁻¹) := by
  unfold harmonicBinWeight
  have h1 : k+1 ≠ 0 := by omega
  have h2 : k+1 ≠ n+1 := by omega
  simp only [h1, h2, or_self, ite_false]
  congr 1
  have h : n+1-(k+1) = n-k := by omega
  rw [h]

theorem harmonicBinWeight_sum (n : ℕ) (P : ℝ) :
    (∑ j ∈ Finset.range (n+2), harmonicBinWeight n P j) =
      2*P + ((n+2 : ℕ) : ℝ) * harmonicReal n := by
  rw [show n+2 = (n+1)+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ']
  rw [harmonicBinWeight_zero, harmonicBinWeight_last]
  have hinner : (∑ k ∈ Finset.range n, harmonicBinWeight n P (k+1)) =
      (((n+2 : ℕ) : ℝ)/2) *
      (∑ k ∈ Finset.range n,
        ((↑(k+1 : ℕ) : ℝ)⁻¹ + (↑(n-k : ℕ) : ℝ)⁻¹)) := by
    calc
      _ = ∑ k ∈ Finset.range n,
            (((n+2 : ℕ) : ℝ)/2) *
              ((↑(k+1 : ℕ) : ℝ)⁻¹ +
                (↑(n-k : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact harmonicBinWeight_inner n k P (Finset.mem_range.mp hk)
      _ = _ := by rw [Finset.mul_sum]
  rw [hinner, harmonicReal_symmetric]
  ring

theorem harmonicBinWeight_sum_bound (n : ℕ) (P : ℝ) (hP : 0 ≤ P) :
    2 * (∑ j ∈ Finset.range (n+2), harmonicBinWeight n P j) ≤
      4 * (P + ((n+2 : ℕ) : ℝ) * Real.log (2*((n+2 : ℕ) : ℝ))) := by
  rw [harmonicBinWeight_sum]
  have hn : (0 : ℝ) ≤ ((n+2 : ℕ) : ℝ) := by positivity
  have hlog := harmonicReal_log n
  nlinarith

end Green64SourceC6

end

