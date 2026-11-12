module

public import Mathlib
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Sups
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

@[expose] public section

/-!
# Analysis / PrimeNumberTheorem / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PrimeNumberTheoremAnd.ZetaConj -/

section

open scoped Complex ComplexConjugate

















theorem deriv_conj_conj' (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  trans deriv (conj ∘ f ∘ conj) (conj p)
  · rfl
  simp











theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp [← deriv_conj_conj']

theorem logDerivZeta_conj (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp [deriv_riemannZeta_conj, riemannZeta_conj]

theorem logDerivZeta_conj' (s : ℂ) :
    (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := logDerivZeta_conj s














theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  exact intervalIntegral.intervalIntegral_conj

end

/-! ## GramExpansion -/

section

namespace Green64SourceC6

/-- Exact finite Gram expansion, with all endpoints and coefficients complex. -/
theorem complex_square_sum {κ : Type*} (t : Finset κ) (f : κ → ℂ) :
    ((‖∑ j ∈ t, f j‖^2 : ℝ) : ℂ) =
    ∑ j ∈ t, ∑ k ∈ t, f j * star (f k) := by
  classical
  calc
    _ = (∑ j ∈ t, f j) * star (∑ k ∈ t, f k) := by
      simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.ofReal_pow]
    _ = _ := by
      simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

end Green64SourceC6

namespace Green64SourceC6

/-- Exact complex Gram expansion with arbitrary translated finite supports. -/
theorem finite_bilinear_gram_identity {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (B : κ → ℂ) (E : ι → κ → ℂ) :
    (((∑ i ∈ s, ‖∑ j ∈ t, B j * E i j‖^2 : ℝ) : ℝ) : ℂ) =
      ∑ j ∈ t, ∑ k ∈ t,
        (∑ i ∈ s, E i j * star (E i k)) * B j * star (B k) := by
  classical
  let Z := fun i => ∑ j ∈ t, B j * E i j
  have hcast : (((∑ i ∈ s, ‖Z i‖^2 : ℝ) : ℝ) : ℂ) =
      ∑ i ∈ s, ((‖Z i‖^2 : ℝ) : ℂ) := by push_cast; rfl
  calc
    _ = ∑ i ∈ s, ((‖Z i‖^2 : ℝ) : ℂ) := hcast
    _ = ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ t,
        (B j * E i j) * star (B k * E i k) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact complex_square_sum t (fun j => B j * E i j)
    _ = ∑ j ∈ t, ∑ i ∈ s, ∑ k ∈ t,
        (B j * E i j) * star (B k * E i k) := Finset.sum_comm
    _ = ∑ j ∈ t, ∑ k ∈ t, ∑ i ∈ s,
        (B j * E i j) * star (B k * E i k) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = ∑ j ∈ t, ∑ k ∈ t,
        (∑ i ∈ s, E i j * star (E i k)) * B j * star (B k) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      simp only [star_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end Green64SourceC6

end

/-! ## MemoryFiniteConditioningCS -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

/-- Source finite-fibre Cauchy inequality for complex physical test
functions, counting every original indexed state with multiplicity. -/
theorem memory_finite_fibre_cauchy
    {X : Type} [Fintype X] (s : Finset X) (w : X → ℂ) :
    ‖∑ x ∈ s, w x‖^2 ≤
      (s.card : ℝ) * (∑ x ∈ s, ‖w x‖^2) := by
  have hn := norm_sum_le s w
  have hh : 0 ≤ ∑ x ∈ s, ‖w x‖ :=
    Finset.sum_nonneg (fun x _ => norm_nonneg _)
  have hp := mul_nonneg
    (sub_nonneg.mpr hn) (add_nonneg hh (norm_nonneg (∑ x ∈ s, w x)))
  have hsq : ‖∑ x ∈ s, w x‖^2 ≤
      (∑ x ∈ s, ‖w x‖)^2 := by nlinarith
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := s)
    (r := fun x => ‖w x‖)
    (f := fun _ => (1:ℝ))
    (g := fun x => ‖w x‖^2)
    (fun _ _ => zero_le_one)
    (fun x _ => sq_nonneg _)
    (fun x _ => by simp)
  calc
    _ ≤ (∑ x ∈ s, ‖w x‖)^2 := hsq
    _ ≤ (s.card : ℝ) * (∑ x ∈ s, ‖w x‖^2) := by
      simpa only [one_mul, one_pow, Finset.sum_const,
        nsmul_eq_mul, mul_one] using hcs
end Green64FullPhysicalE

end

end

/-! ## MemoryFiniteConditioningPartition -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {X D Y : Type} [Fintype X] [Fintype D] [Fintype Y]

/-- An EXACT partition of a genuine finite state carrier by the
shared-label tuple d and its full Haar residue y. -/
def memoryFiniteConditionalFibre (label : X → D) (residue : X → Y)
    (d : D) (y : Y) : Finset X :=
  Finset.univ.filter (fun x => label x = d ∧ residue x = y)

/-- Every original state occurs in ONE and only one (d,y) fibre.
The result counts repeated numerical labels as separate states. -/
theorem memory_finite_conditional_partition
    (label : X → D) (residue : X → Y) (w : X → ℝ) :
    (∑ d : D, ∑ y : Y,
       ∑ x ∈ memoryFiniteConditionalFibre label residue d y,
          w x) = ∑ x : X, w x := by
  simp_rw [memoryFiniteConditionalFibre, Finset.sum_filter]
  calc
    _ = ∑ y : Y, ∑ d : D, ∑ x : X,
        if label x = d ∧ residue x = y then w x else 0 :=
          Finset.sum_comm
    _ = ∑ y : Y, ∑ x : X, ∑ d : D,
        if label x = d ∧ residue x = y then w x else 0 := by
          apply Finset.sum_congr rfl; intro y _
          exact Finset.sum_comm
    _ = ∑ x : X, ∑ y : Y, ∑ d : D,
        if label x = d ∧ residue x = y then w x else 0 :=
          Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      have hinner (y : Y) :
          (∑ d : D, if label x = d ∧ residue x = y then w x else 0) =
          (if residue x = y then w x else 0) := by
        by_cases hy : residue x = y <;> simp [hy]
      simp_rw [hinner]
      simp
end Green64FullPhysicalE

end

end

/-! ## MemoryFiniteConditioningNorm -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {X D Y : Type} [Fintype X] [Fintype D] [Fintype Y]

/-- An exact finite conditioning-map L² estimate, with the original
partition into shared-label data and genuine residue fibres. Unlike
an abstract estimate on arbitrary kernels, the source map uses the
exact zero/one incidence of the physical (d,y)-fibre. -/
theorem memory_finite_conditioning_norm_sq
    (label : X → D) (residue : X → Y)
    (a : Y → ℝ) (ha : ∀ y, 0 ≤ a y)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ d y,
      a y * ((memoryFiniteConditionalFibre label residue d y).card : ℝ) ≤ C)
    (w : X → ℂ) :
    (∑ d : D, ∑ y : Y,
      a y * ‖∑ x ∈ memoryFiniteConditionalFibre label residue d y,
        w x‖^2) ≤
      C * (∑ x : X, ‖w x‖^2) := by
  let T := fun d y => memoryFiniteConditionalFibre label residue d y
  have hterm (d : D) (y : Y) :
      a y * ‖∑ x ∈ T d y, w x‖^2 ≤
      C * (∑ x ∈ T d y, ‖w x‖^2) := by
    have hcs := memory_finite_fibre_cauchy (T d y) w
    have hn : 0 ≤ ∑ x ∈ T d y, ‖w x‖^2 :=
      Finset.sum_nonneg (fun x _ => sq_nonneg _)
    calc
      _ ≤ a y * ((T d y).card * (∑ x ∈ T d y, ‖w x‖^2)) :=
        mul_le_mul_of_nonneg_left hcs (ha y)
      _ = (a y * (T d y).card) * (∑ x ∈ T d y, ‖w x‖^2) := by
        ring
      _ ≤ C * (∑ x ∈ T d y, ‖w x‖^2) :=
        mul_le_mul_of_nonneg_right (hbound d y) hn
  calc
    _ ≤ ∑ d : D, ∑ y : Y,
      C * (∑ x ∈ T d y, ‖w x‖^2) := by
        apply Finset.sum_le_sum; intro d _
        apply Finset.sum_le_sum; intro y _
        exact hterm d y
    _ = C * (∑ d : D, ∑ y : Y,
      ∑ x ∈ T d y, ‖w x‖^2) := by
        simp_rw [Finset.mul_sum]
    _ = _ := by
      rw [memory_finite_conditional_partition label residue (fun x => ‖w x‖^2)]
end Green64FullPhysicalE

end

end

/-! ## MemoryFiniteRectangularSchur -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

/-- True finite weighted rectangular Schur: distinct source and target measures. -/
theorem memory_finite_rectangular_schur_sq
    {X Y : Type} [Fintype X] [DecidableEq Y]
    (S : Finset Y) (mx : X → ℝ) (my : Y → ℝ)
    (wx : X → ℝ) (wy : Y → ℝ)
    (K : X → Y → ℂ) (f : Y → ℂ) (R C : ℝ)
    (hmx : ∀ x, 0 ≤ mx x) (hwy : ∀ y ∈ S, 0 < wy y)
    (hR : ∀ x, (∑ y ∈ S, ‖K x y‖ * wy y) ≤ R * wx x)
    (hC : ∀ y ∈ S, (∑ x, mx x * wx x * ‖K x y‖) ≤ C * my y * wy y)
    (hRn : 0 ≤ R) :
    (∑ x : X, mx x * ‖∑ y ∈ S, K x y * f y‖ ^ 2) ≤
      R*C*(∑ y ∈ S, my y * ‖f y‖ ^ 2) := by
  let b := fun (x : X) (y : Y) => ‖K x y‖ * ‖f y‖^2 / wy y
  let a := fun (x : X) (y : Y) => ‖K x y‖ * wy y
  let r := fun (x : X) (y : Y) => ‖K x y‖ * ‖f y‖
  have hb_nonneg (x : X) (y : Y) (hy : y ∈ S) : 0 ≤ b x y := by
    dsimp [b]
    exact div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (hwy y hy).le
  have ha_nonneg (x : X) (y : Y) (hy : y ∈ S) : 0 ≤ a x y := by
    dsimp [a]; exact mul_nonneg (norm_nonneg _) (hwy y hy).le
  have hsq (x : X) (y : Y) (hy : y ∈ S) :
      (r x y)^2 ≤ (a x y) * (b x y) := by
    have hn : wy y ≠ 0 := (hwy y hy).ne'
    dsimp [r, a, b]
    apply le_of_eq
    field_simp [hn]
  have hpoint (x : X) :
      ‖∑ y ∈ S, K x y * f y‖ ^ 2 ≤
        (R*wx x) * (∑ y ∈ S, b x y) := by
    have hnorm : ‖∑ y ∈ S, K x y * f y‖ ≤ ∑ y ∈ S, r x y := by
      calc
        _ ≤ ∑ y ∈ S, ‖K x y * f y‖ := norm_sum_le _ _
        _ = _ := by simp only [r, norm_mul]
    have hn0 : 0 ≤ ∑ y ∈ S, r x y := by
      apply Finset.sum_nonneg; intro y hy
      dsimp [r]; positivity
    have hp : ‖∑ y ∈ S, K x y * f y‖ ^ 2 ≤ (∑ y ∈ S, r x y)^2 := by
      nlinarith [norm_nonneg (∑ y ∈ S, K x y * f y)]
    have hcs : (∑ y ∈ S, r x y)^2 ≤
        (∑ y ∈ S, a x y) * (∑ y ∈ S, b x y) := by
      exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
        (fun y hy => ha_nonneg x y hy)
        (fun y hy => hb_nonneg x y hy)
        (fun y hy => hsq x y hy)
    have hb0 : 0 ≤ ∑ y ∈ S, b x y := by
      exact Finset.sum_nonneg (fun y hy => hb_nonneg x y hy)
    calc
      _ ≤ (∑ y ∈ S, r x y)^2 := hp
      _ ≤ (∑ y ∈ S, a x y) * (∑ y ∈ S, b x y) := hcs
      _ ≤ (R*wx x) * (∑ y ∈ S, b x y) := by
        exact mul_le_mul_of_nonneg_right (by simpa only [a] using hR x) hb0
  have hswap :
      (∑ x : X, mx x * ((R*wx x) * (∑ y ∈ S, b x y))) =
      R * ∑ y ∈ S, (‖f y‖^2 / wy y) * (∑ x : X, mx x * wx x * ‖K x y‖) := by
    calc
      _ = ∑ x : X, ∑ y ∈ S,
          R * (‖f y‖^2 / wy y) * (mx x * wx x * ‖K x y‖) := by
        apply Finset.sum_congr rfl; intro x hx
        calc
          _ = (mx x * R * wx x) * (∑ y ∈ S, b x y) := by ring
          _ = ∑ y ∈ S, (mx x * R * wx x) * b x y := Finset.mul_sum ..
          _ = _ := by
            apply Finset.sum_congr rfl; intro y hy
            dsimp [b]; ring
      _ = ∑ y ∈ S, ∑ x : X,
          R * (‖f y‖^2 / wy y) * (mx x * wx x * ‖K x y‖) := Finset.sum_comm
      _ = ∑ y ∈ S,
          R * (‖f y‖^2 / wy y) * (∑ x : X, mx x * wx x * ‖K x y‖) := by
        apply Finset.sum_congr rfl; intro y hy
        rw [Finset.mul_sum]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro y hy
        ring
  calc
    _ ≤ ∑ x : X, mx x * ((R*wx x) * (∑ y ∈ S, b x y)) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hpoint x) (hmx x)
    _ = R * ∑ y ∈ S, (‖f y‖^2 / wy y) *
        (∑ x : X, mx x * wx x * ‖K x y‖) := hswap
    _ ≤ R * ∑ y ∈ S, (‖f y‖^2 / wy y) * (C * my y * wy y) := by
      apply mul_le_mul_of_nonneg_left _ hRn
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left (hC y hy)
        (div_nonneg (sq_nonneg _) (hwy y hy).le)
    _ = R * ∑ y ∈ S, C * (my y * ‖f y‖^2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      have hn : wy y ≠ 0 := (hwy y hy).ne'
      field_simp [hn]
    _ = R*C*(∑ y ∈ S, my y * ‖f y‖^2) := by
      rw [← Finset.mul_sum]
      ring
end Green64FullPhysicalE

end

end

/-! ## FiniteSchur -/

section

open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- The existing exact finite rectangular Schur theorem specialized to
Euclidean counting coordinates. No equality of vector norms or positivity
of the complex matrix is required. -/
theorem b661_finite_matrix_schur_norm434 {X : Type} [Fintype X] [DecidableEq X]
    (K : Matrix X X ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ x, (∑ y, ‖K x y‖) ≤ C)
    (hcol : ∀ y, (∑ x, ‖K x y‖) ≤ C)
    (g : EuclideanSpace ℂ X) :
    ‖K.toEuclideanLin g‖ ≤ C*‖g‖ := by
  have hr (x : X) : (∑ y ∈ (Finset.univ : Finset X), ‖K x y‖*(1:ℝ)) ≤ C*1 := by
    simpa only [mul_one] using hrow x
  have hc (y : X) (_hy : y ∈ (Finset.univ : Finset X)) :
      (∑ x : X, (1:ℝ)*1*‖K x y‖) ≤ C*1*1 := by
    simpa only [mul_one,one_mul] using hcol y
  have hs := memory_finite_rectangular_schur_sq Finset.univ
    (fun _ : X => (1:ℝ)) (fun _ : X => (1:ℝ))
    (fun _ : X => (1:ℝ)) (fun _ : X => (1:ℝ))
    K (fun y => g y) C C (fun _ => by norm_num)
    (fun _ _ => by norm_num) hr hc hC
  have hsq : ‖K.toEuclideanLin g‖^2 ≤ C*C*‖g‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
    change (∑ x : X, ‖∑ y : X, K x y*g y‖^2) ≤ C*C*(∑ y : X, ‖g y‖^2)
    simpa only [one_mul] using hs
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg g))).mp
  nlinarith only [hsq]

/-- Full bilinear form of the exact finite Schur bound, with arbitrary
complex endpoint vectors. This is an absolute error budget, not a saving. -/
theorem b661_finite_matrix_schur_pairing434 {X : Type} [Fintype X] [DecidableEq X]
    (K : Matrix X X ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ x, (∑ y, ‖K x y‖) ≤ C)
    (hcol : ∀ y, (∑ x, ‖K x y‖) ≤ C)
    (f g : EuclideanSpace ℂ X) :
    ‖inner ℂ f (K.toEuclideanLin g)‖ ≤ C*‖f‖*‖g‖ := by
  calc
    _ ≤ ‖f‖*‖K.toEuclideanLin g‖ := norm_inner_le_norm _ _
    _ ≤ ‖f‖*(C*‖g‖) := mul_le_mul_of_nonneg_left
      (b661_finite_matrix_schur_norm434 K C hC hrow hcol g) (norm_nonneg f)
    _ = _ := by ring
end Green64FullPhysicalE

end

end

/-! ## MemoryFiniteTwoEndpointConditioning -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

/-- Exact simultaneous partition of any TWO finite endpoint sets
by a common labelled source pattern and a translated residue.
This keeps arbitrary signed complex coefficients H(x,z) inside
the original fibre. Unlike an independent-kernel approximation,
there is no equality-of-auxiliary-draws assumption. -/
theorem memory_finite_two_endpoint_conditioning
    {X Z D Y : Type}
    [Fintype X] [Fintype Z] [Fintype D] [Fintype Y]
    (a : X → D) (b : Z → D)
    (r : X → Y) (s : Z → Y)
    (tr : Y → Y) (H : X → Z → ℂ) :
    (∑ x : X, ∑ z : Z,
      if a x = b z ∧ s z = tr (r x) then H x z else 0) =
    (∑ d : D, ∑ y : Y,
      ∑ x ∈ memoryFiniteConditionalFibre a r d y,
        ∑ z ∈ memoryFiniteConditionalFibre b s d (tr y),
          H x z) := by
  classical
  let F : D → Y → X → Z → ℂ := fun d y x z =>
    if a x = d ∧ r x = y then
      (if b z = d ∧ s z = tr y then H x z else 0)
    else 0
  have hExpand :
      (∑ d : D, ∑ y : Y,
        ∑ x ∈ memoryFiniteConditionalFibre a r d y,
          ∑ z ∈ memoryFiniteConditionalFibre b s d (tr y),
            H x z) =
      ∑ d : D, ∑ y : Y, ∑ x : X, ∑ z : Z, F d y x z := by
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro y _
    simp only [memoryFiniteConditionalFibre, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : a x = d ∧ r x = y
    · simp [F, hx]
    · simp [F, hx]
  have hSwap :
      (∑ d : D, ∑ y : Y, ∑ x : X, ∑ z : Z, F d y x z) =
      ∑ x : X, ∑ z : Z, ∑ d : D, ∑ y : Y, F d y x z := by
    calc
      _ = ∑ d : D, ∑ x : X, ∑ y : Y, ∑ z : Z, F d y x z := by
        apply Finset.sum_congr rfl
        intro d _
        exact Finset.sum_comm
      _ = ∑ x : X, ∑ d : D, ∑ y : Y, ∑ z : Z, F d y x z :=
        Finset.sum_comm
      _ = ∑ x : X, ∑ d : D, ∑ z : Z, ∑ y : Y, F d y x z := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro d _
        exact Finset.sum_comm
      _ = ∑ x : X, ∑ z : Z, ∑ d : D, ∑ y : Y, F d y x z := by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm
  have hCell (x : X) (z : Z) :
      (∑ d : D, ∑ y : Y, F d y x z) =
        if a x = b z ∧ s z = tr (r x) then H x z else 0 := by
    calc
      _ = ∑ d : D, if a x = d then
            (∑ y : Y, if r x = y then
              (if b z = d ∧ s z = tr y then H x z else 0)
             else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro d _
            by_cases ha : a x = d
            · simp only [ha, ite_true, F]
              apply Finset.sum_congr rfl
              intro y _
              by_cases hr : r x = y <;> simp [ha, hr]
            · simp [F, ha]
      _ = _ := by simp [eq_comm]
  rw [hExpand, hSwap]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  exact (hCell x z).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryFiniteMovingStepFibre -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

/-- Source EXACT two-endpoint Fubini where the translation of
the original output residue depends on the source SHARED tuple d.
This resolves the genuine moving-D obstruction, not by fixing an
independent D but by conditioning on exactly the shared source
labels which determine D. All signed complex tests are preserved. -/
theorem memory_finite_moving_step_two_endpoint_fibres
    {X Z D Y : Type}
    [Fintype X] [Fintype Z] [Fintype D] [Fintype Y]
    (a : X → D) (b : Z → D)
    (r : X → Y) (s : Z → Y)
    (tr : D → Y → Y) (H : X → Z → ℂ) :
    (∑ x : X, ∑ z : Z,
      if a x = b z ∧ s z = tr (a x) (r x)
        then H x z else 0) =
    (∑ d : D, ∑ y : Y,
      ∑ x ∈ memoryFiniteConditionalFibre a r d y,
        ∑ z ∈ memoryFiniteConditionalFibre b s d (tr d y),
          H x z) := by
  classical
  let F : D → Y → X → Z → ℂ := fun d y x z =>
    if a x = d ∧ r x = y then
      (if b z = d ∧ s z = tr d y then H x z else 0)
    else 0
  have hExpand :
      (∑ d : D, ∑ y : Y,
        ∑ x ∈ memoryFiniteConditionalFibre a r d y,
          ∑ z ∈ memoryFiniteConditionalFibre b s d (tr d y),
            H x z) =
      ∑ d : D, ∑ y : Y, ∑ x : X, ∑ z : Z, F d y x z := by
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro y _
    simp only [memoryFiniteConditionalFibre, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : a x = d ∧ r x = y
    · simp [F, hx]
    · simp [F, hx]
  have hSwap :
      (∑ d : D, ∑ y : Y, ∑ x : X, ∑ z : Z, F d y x z) =
      ∑ x : X, ∑ z : Z, ∑ d : D, ∑ y : Y, F d y x z := by
    calc
      _ = ∑ d : D, ∑ x : X, ∑ y : Y, ∑ z : Z, F d y x z := by
        apply Finset.sum_congr rfl
        intro d _
        exact Finset.sum_comm
      _ = ∑ x : X, ∑ d : D, ∑ y : Y, ∑ z : Z, F d y x z :=
        Finset.sum_comm
      _ = ∑ x : X, ∑ d : D, ∑ z : Z, ∑ y : Y, F d y x z := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro d _
        exact Finset.sum_comm
      _ = ∑ x : X, ∑ z : Z, ∑ d : D, ∑ y : Y, F d y x z := by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm
  have hCell (x : X) (z : Z) :
      (∑ d : D, ∑ y : Y, F d y x z) =
      if a x = b z ∧ s z = tr (a x) (r x)
        then H x z else 0 := by
    calc
      _ = ∑ d : D, if a x = d then
           (∑ y : Y, if r x = y then
             (if b z = d ∧ s z = tr d y then H x z else 0)
            else 0)
          else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        by_cases ha : a x = d
        · simp only [ha, ite_true, F]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hr : r x = y <;> simp [ha, hr]
        · simp [F, ha]
      _ = _ := by simp [eq_comm]
  rw [hExpand, hSwap]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  exact (hCell x z).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryFiniteOriginalTwoEndpointTensor -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

/-- Exact two endpoint source fibre factorization for a
separable signed complex test, with arbitrary finite fibres,
two source endpoint half weights and one fixed source K.
This is the elementary Fubini kernel identity reused inside
the actual permuted SMALL physical E sum, not an ideal
operator-norm hypothesis. -/
theorem memory_finite_original_two_endpoint_tensor
    {X Z : Type} [Fintype X] [Fintype Z]
    (s : Finset X) (t : Finset Z)
    (u : X → ℂ) (v : Z → ℂ) (K A B : ℂ) :
    (∑ x ∈ s, ∑ z ∈ t, K * (A * B) * u x * v z) =
      K * (A * ∑ x ∈ s, u x) *
        (B * ∑ z ∈ t, v z) := by
  calc
    _ = ∑ x ∈ s,
      (K * (A * B) * u x) * ∑ z ∈ t, v z := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
    _ = (∑ x ∈ s, K * (A * B) * u x) *
        ∑ z ∈ t, v z := by rw [Finset.sum_mul]
    _ = (K * (A * B) * ∑ x ∈ s, u x) *
        ∑ z ∈ t, v z := by
      have he : (∑ x ∈ s, K * (A * B) * u x) =
          K * (A * B) * ∑ x ∈ s, u x := by
        rw [Finset.mul_sum]
      rw [he]
    _ = _ := by ring
end Green64FullPhysicalE

end

end

/-! ## MemoryGhostTupleSplit -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64Fock
set_option maxHeartbeats 0
variable {I U : Type} [Fintype I] [Fintype U]

/-- Indexed tuple as a bag; repeated values retain their full multiplicities. -/
def memoryTupleBag (x : I → U) : Multiset U := ∑ i : I, {x i}

/-- A source ordered tuple and its indexed bag are literally the same multiset. -/
theorem memory_tuple_bag_ofFn {n : ℕ} (x : Fin n → U) :
    memoryTupleBag x = (List.ofFn x : Multiset U) := by
  induction n with
  | zero => simp [memoryTupleBag]
  | succ n ih =>
    simp only [memoryTupleBag, Fin.sum_univ_succ, List.ofFn_succ]
    change {x 0} + memoryTupleBag (fun i : Fin n => x i.succ) =
      {x 0} + (List.ofFn (fun i : Fin n => x i.succ) : Multiset U)
    rw [ih]

/-- Splitting selected OLD indices is a partition of the full multiset, not of
its distinct-value support. -/
theorem memory_tuple_bag_split (p : I → Prop) [DecidablePred p] (x : I → U) :
    memoryTupleBag (fun i : {i // p i} => x i) +
      memoryTupleBag (fun i : {i // ¬p i} => x i) = memoryTupleBag x := by
  exact Fintype.sum_subtype_add_sum_subtype p (fun i => ({x i} : Multiset U))

/-- Exact finite tensor disintegration along the selected OLD positions.
The inverse map inserts both indexed tuples into their original positions. -/
theorem memory_source_old_tuple_split (p : I → Prop) [DecidablePred p]
    (mu : U → ℂ)
    (G : ({i // p i} → U) → ({i // ¬p i} → U) → ℂ) :
    (∑ old : I → U, (∏ i, mu (old i)) *
      G (fun i => old i) (fun i => old i)) =
    ∑ a : {i // p i} → U, ∑ u : {i // ¬p i} → U,
      ((∏ i, mu (a i)) * (∏ i, mu (u i))) * G a u := by
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => U)
  calc
    _ = ∑ z : ({i // p i} → U) × ({i // ¬p i} → U),
        ((∏ i, mu (z.1 i)) * (∏ i, mu (z.2 i))) * G z.1 z.2 := by
      apply Fintype.sum_equiv e
      intro old
      dsimp [e, Equiv.piEquivPiSubtypeProd]
      have hp := Fintype.prod_subtype_mul_prod_subtype p (fun i => mu (old i))
      exact congrArg (fun z : ℂ => z * G (fun i => old i) (fun i => old i)) hp.symm
    _ = _ := Fintype.sum_prod_type _

/-- Cardinality of selected index positions; there is no loss for repeated atoms. -/
theorem memory_deleted_positions_card {n : ℕ} (A : Finset (Fin n)) :
    Fintype.card {i : Fin n // i ∈ A} = A.card ∧
      Fintype.card {i : Fin n // i ∉ A} = n-A.card := by
  constructor
  · exact Fintype.card_coe A
  · simp only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
end Green64Fock

end

end

/-! ## MemoryIndEndpointFinsetGeneric -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- A source vertex with M marked zero coordinates has precisely the
remaining zero coordinates charged by q_t. This is the finite
combinatorial identity behind the original BIG Haar frozen factor,
independent of any stochastic approximation or source-specific
bound. -/
theorem memory_generic_marked_zero_power_product
    {P : Type} [Fintype P] [DecidableEq P]
    (zeros active : Finset P) (hsub : active ⊆ zeros)
    (M : ℕ) (hM : active.card = M) (q : ℝ) :
    q ^ (zeros.card - M) =
      ∏ p : P, if p ∈ active then (1 : ℝ)
        else if p ∈ zeros then q else 1 := by
  have hc : (zeros \ active).card = zeros.card - M := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hM]
  rw [← hc]
  have hprod : q ^ ((zeros \ active).card) =
      ∏ p ∈ zeros \ active, q := by
    simp only [Finset.prod_const]
  rw [hprod]
  calc
    (∏ p ∈ zeros \ active, q) =
      ∏ p : P, if p ∈ zeros \ active then q else 1 := by
        have hset : (zeros \ active) =
            (Finset.univ : Finset P).filter (fun p => p ∈ zeros ∧ p ∉ active) := by
          ext p
          simp
        rw [hset, Finset.prod_filter]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      by_cases ha : p ∈ active
      · simp [ha]
      · by_cases hz : p ∈ zeros
        · simp [ha,hz]
        · simp [ha,hz]
end Green64FullPhysicalE

end

end

/-! ## MemoryIndGenericDoubleEndpoint -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- A TRUE N+1-visit endpoint-product identity, N=n+1>0.
A nonterminal visit occurs at both ends of consecutive Markov rows,
whereas each genuine endpoint occurs exactly once. This preserves
all factors even when the weight is zero; no inverse or cancellation. -/
theorem memory_ind_adjacent_endpoint_product
    {α : Type} [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    (∏ i ∈ Finset.range (n+1), f i * f (i+1)) =
    ∏ t ∈ Finset.range (n+2),
      if t = 0 ∨ t = n+1 then f t else f t * f t := by
  let h : ℕ → α := fun t => if t = 0 ∨ t = n+1 then f t else f t * f t
  have hleft :
      (∏ i ∈ Finset.range (n+1), f i * f (i+1)) =
      f 0 * ((∏ i ∈ Finset.range n, f (i+1)) *
        (∏ i ∈ Finset.range n, f (i+1))) * f (n+1) := by
    rw [Finset.prod_mul_distrib]
    rw [Finset.prod_range_succ' f n]
    rw [Finset.prod_range_succ (fun i => f (i+1)) n]
    ac_rfl
  have hprefix :
      (∏ t ∈ Finset.range n, h (t+1)) =
      ∏ t ∈ Finset.range n, f (t+1)*f (t+1) := by
    apply Finset.prod_congr rfl
    intro t ht
    have hlt : t<n := Finset.mem_range.mp ht
    have hnz : t+1 ≠ 0 := Nat.succ_ne_zero t
    have hneq : t+1 ≠ n+1 := by omega
    change (if t+1=0 ∨ t+1=n+1 then f (t+1) else f (t+1)*f (t+1)) = _
    rw [if_neg (by omega : ¬ (t+1=0 ∨ t+1=n+1))]
  have hright :
      (∏ t ∈ Finset.range (n+2), h t) =
      f 0 * (∏ t ∈ Finset.range n, f (t+1)*f (t+1)) *
        f (n+1) := by
    rw [show n+2=(n+1)+1 by omega]
    rw [Finset.prod_range_succ]
    rw [Finset.prod_range_succ' h n]
    rw [hprefix]
    have h0 : h 0 = f 0 := by simp [h]
    have hlast : h (n+1) = f (n+1) := by simp [h]
    rw [h0, hlast]
    ac_rfl
  calc
    _ = f 0 * ((∏ i ∈ Finset.range n, f (i+1)) *
        (∏ i ∈ Finset.range n, f (i+1))) * f (n+1) := hleft
    _ = f 0 * (∏ i ∈ Finset.range n, f (i+1)*f (i+1)) *
        f (n+1) := by rw [Finset.prod_mul_distrib]
    _ = _ := by
      change _ = ∏ t ∈ Finset.range (n+2), h t
      exact hright.symm
end Green64FullPhysicalE

end

/-! ## MemoryIndGenericSevenfoldFubini -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Exact sevenfold source-pattern finite Fubini for the shape
Nu, dependent original auxiliary choice, two BIG endpoint
permutations, two SMALL endpoint permutations, and a target state.
The dependent Sigma index retains every one of these choices,
including its ordered multiplicities. This purely finite lemma
does not assume an independent Markov kernel or Haar factor. -/
theorem memory_ind_dependent_sevenfold_Fubini
    {Nu : Type} [Fintype Nu]
    (Aux : Nu → Type) [∀ nu, Fintype (Aux nu)]
    {Bs Bt Ss St Y : Type}
    [Fintype Bs] [Fintype Bt] [Fintype Ss] [Fintype St]
    [Fintype Y]
    (f : (Σ nu : Nu, Aux nu × Bs × Bt × Ss × St × Y) → ℂ) :
    (∑ nu : Nu, ∑ aux : Aux nu, ∑ bs : Bs, ∑ bt : Bt,
      ∑ ss : Ss, ∑ st : St, ∑ y : Y,
        f ⟨nu,aux,bs,bt,ss,st,y⟩) =
    (∑ a : (Σ nu : Nu, Aux nu × Bs × Bt × Ss × St × Y),
      f a) := by
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
end Green64FullPhysicalE

end

end

/-! ## MemoryIndSupportedSum -/

section

open scoped BigOperators
namespace Green64FullPhysicalE

/-- A support bijection preserves full sums, including every omitted zero term. -/
theorem memory_generic_supported_sum_equiv
    {A B : Type} [Fintype A] [Fintype B]
    (P : A → Prop) (Q : B → Prop)
    [DecidablePred P] [DecidablePred Q]
    (e : {a // P a} ≃ {b // Q b}) (f : A → ℂ) (g : B → ℂ)
    (hf : ∀ a, ¬ P a → f a = 0) (hg : ∀ b, ¬ Q b → g b = 0)
    (he : ∀ a : {a // P a}, f a.val = g (e a).val) :
    (∑ a : A, f a) = ∑ b : B, g b := by
  classical
  calc
    _ = ∑ a : {a // P a}, f a.val :=
      Finset.sum_congr_set {a | P a} f (fun a => f a.val) (by intros; rfl) hf
    _ = ∑ b : {b // Q b}, g b.val := Fintype.sum_equiv e _ _ he
    _ = _ := (Finset.sum_congr_set {b | Q b} g (fun b => g b.val)
      (by intros; rfl) hg).symm
end Green64FullPhysicalE

end

/-! ## MemoryOriginalPrimitiveCellGramSchur -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

/-- Original primitive-character global log-cell GRAM frame:
for the exact finite family C of primitive characters and one
true global source product-cell I_j, any uniform normalized
pairwise off-diagonal bound eps transfers to an L2 operator
estimate on ARBITRARY conditional character coefficients.
This is the missing frame step after actual prime Siegel-Walfisz,
not an assumption that the output test is independent of p.
The coefficient is 1+card(C)*eps, independent of cell count. -/
theorem memory_original_finite_cell_gram_schur
    {C : Type} [Fintype C] [DecidableEq C]
    (G : C → C → ℂ) (eps : ℝ)
    (heps : 0 ≤ eps)
    (hdiag : ∀ c, ‖G c c‖ ≤ 1)
    (hoff : ∀ c d, c ≠ d → ‖G c d‖ ≤ eps)
    (a : C → ℂ) :
    (∑ c : C, ‖∑ d : C, G c d * a d‖ ^ 2) ≤
      (1 + (Fintype.card C:ℝ)*eps)^2 *
        (∑ d : C, ‖a d‖ ^ 2) := by
  let N : ℝ := (Fintype.card C : ℝ)
  let R : ℝ := 1 + N*eps
  have hR : 0 ≤ R := by dsimp [R,N]; positivity
  have hpoint (c d : C) :
      ‖G c d‖ ≤ eps + if d = c then 1 else 0 := by
    by_cases h : d = c
    · subst d
      simp only [ite_true]
      linarith [hdiag c]
    · simp only [if_neg h, add_zero]
      exact hoff c d (Ne.symm h)
  have hrow (c : C) :
      (∑ d : C, ‖G c d‖) ≤ R := by
    calc
      _ ≤ ∑ d : C, (eps + if d = c then (1:ℝ) else 0) :=
        Finset.sum_le_sum (fun d _ => hpoint c d)
      _ = R := by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
        simp [R,N]
        ring
  have hcol (d : C) :
      (∑ c : C, ‖G c d‖) ≤ R := by
    calc
      _ ≤ ∑ c : C, (eps + if d = c then (1:ℝ) else 0) :=
        Finset.sum_le_sum (fun c _ => hpoint c d)
      _ = R := by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
        simp [R,N]
        ring
  have h := memory_finite_rectangular_schur_sq
    (X:=C) (Y:=C) (S:=Finset.univ)
    (mx:=fun _ => (1:ℝ)) (my:=fun _ => (1:ℝ))
    (wx:=fun _ => (1:ℝ)) (wy:=fun _ => (1:ℝ))
    G a R R
    (fun _ => zero_le_one)
    (fun _ _ => zero_lt_one)
    (fun c => by simpa only [one_mul, mul_one] using hrow c)
    (fun d _ => by simpa only [one_mul, mul_one] using hcol d)
    hR
  simpa [R,N,pow_two] using h
end Green64FullPhysicalE

end

end

/-! ## P1CanonicalTruncation -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- A single canonical natural cutoff works simultaneously for the
support of the smoothing and the exact original finite prime range. -/
theorem p1_canonical_truncation
    (N : ℝ) (hN : 1 ≤ N) :
    3*N ≤ ((⌈3*N⌉₊ : ℕ) : ℝ) ∧
      ((⌈3*N⌉₊ : ℕ) : ℝ) ≤ 4*N := by
  have hNpos : 0 ≤ 3*N := by positivity
  have hlo := Nat.le_ceil (3*N)
  have hhi := Nat.ceil_lt_add_one hNpos
  constructor
  · exact hlo
  · calc
      ((⌈3*N⌉₊ : ℕ) : ℝ) ≤ 3*N + 1 := le_of_lt hhi
      _ ≤ 4*N := by nlinarith only [hN]
end Green64Analytic.LongPrime

end

/-! ## P1CanonicalPrimePower -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Prime-power contribution at the canonical support cutoff is
O(log(4N)/sqrt(N)), uniformly in the short interval and character. -/
theorem p1_canonical_prime_power_bound
    (N : ℝ) (hN : 1 ≤ N) :
    (2*Real.sqrt (((⌈3*N⌉₊:ℕ):ℝ)) *
      Real.log (((⌈3*N⌉₊:ℕ):ℝ)))/N ≤
      (4*Real.log (4*N))/Real.sqrt N := by
  have hNp : 0 < N := by linarith
  have hK := (p1_canonical_truncation N hN).2
  have hKpos : 0 ≤ (((⌈3*N⌉₊:ℕ):ℝ)) := Nat.cast_nonneg _
  have hKsqrt : Real.sqrt (((⌈3*N⌉₊:ℕ):ℝ)) ≤ 2*Real.sqrt N := by
    calc
      Real.sqrt (((⌈3*N⌉₊:ℕ):ℝ)) ≤ Real.sqrt (4*N) :=
        Real.sqrt_le_sqrt hK
      _ = 2*Real.sqrt N := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        norm_num
  have hKlog : Real.log (((⌈3*N⌉₊:ℕ):ℝ)) ≤ Real.log (4*N) := by
    exact Real.log_le_log (by linarith [(p1_canonical_truncation N hN).1]) hK
  have hLog : 0 ≤ Real.log (4*N) :=
    Real.log_nonneg (by linarith : (1:ℝ) ≤ 4*N)
  have hSqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNp
  have hSq : Real.sqrt N*Real.sqrt N = N := Real.mul_self_sqrt hNp.le
  have hcomb : 2*Real.sqrt (((⌈3*N⌉₊:ℕ):ℝ)) *
      Real.log (((⌈3*N⌉₊:ℕ):ℝ)) ≤
      4*Real.sqrt N*Real.log (4*N) := by
    calc
      _ ≤ 2*(2*Real.sqrt N)*Real.log (4*N) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hKsqrt (by norm_num)
        · exact hKlog
        · exact Real.log_nonneg (by
            have ht : (1:ℝ) ≤ (((⌈3*N⌉₊:ℕ):ℝ)) := by
              linarith [(p1_canonical_truncation N hN).1]
            exact ht)
        · positivity
      _ = _ := by ring
  apply (div_le_div_of_nonneg_right hcomb hNp.le).trans
  apply le_of_eq
  field_simp
  nlinarith [hSq]
end Green64Analytic.LongPrime

end

/-! ## PhysicalSigmaPrimeDisintegration -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {G : Type} [Fintype G] [DecidableEq G]
variable (P : G → Type) [∀ g, Fintype (P g)]
variable [∀ g, DecidableEq (P g)]
variable (prime : (g : G) → P g → ℕ)

/-- Original disjoint numerical prime groups provide an injective
Sigma-group index map. This is a genuine source property, not
an assumption that distinct arbitrary Fock atoms share no prime. -/
def globalSigmaPrime : (Σ g : G, P g) → ℕ :=
  fun x => prime x.1 x.2

/-- With the source's distinct numerical prime groups, restricting
a GLOBAL numerical batch to one BIG group recovers exactly that
group's original witness-level prime set. -/
theorem global_big_numeric_batch_group_fibre
    (batch : (g : G) → Finset (P g))
    (hinj : Function.Injective (globalSigmaPrime P prime))
    (g : G) :
    (Finset.univ : Finset (P g)).filter
      (fun p => prime g p ∈
        (Finset.univ : Finset G).biUnion
          (fun h => (batch h).image (prime h))) =
      batch g := by
  classical
  ext p
  constructor
  · intro hp
    have hn : prime g p ∈ (Finset.univ : Finset G).biUnion
        (fun h => (batch h).image (prime h)) :=
      (Finset.mem_filter.mp hp).2
    rcases Finset.mem_biUnion.mp hn with ⟨h, _, hval⟩
    rcases Finset.mem_image.mp hval with ⟨q, hq, hqnum⟩
    have heq : (⟨g, p⟩ : Σ h : G, P h) = ⟨h,q⟩ := by
      apply hinj
      simpa only [globalSigmaPrime] using hqnum.symm
    have hgh : g = h := (Sigma.mk.inj heq).1
    subst h
    have hpq : p = q := eq_of_heq (Sigma.mk.inj heq).2
    simpa only [hpq] using hq
  · intro hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨g, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩

end Green64FullPhysicalE

end

/-! ## PhysicalSourceOrderedSlotPartition -/

section

open Classical

namespace Green64FullPhysicalE

/-- A source physical edge uses a COMMON pattern index before both
independent endpoint permutations. Every target slot is either
shared, filled from one OLD pending index, or genuinely fresh. -/
theorem source_oriented_active_slot_partition
    {P : Type} [DecidableEq P] {M j : ℕ}
    (source target : Fin M → P) (old : Fin j → P)
    (sigma tau : Equiv.Perm (Fin M))
    (shared promoted : Finset (Fin M))
    (chooseOld : ↥promoted ↪ Fin j)
    (hshared : ∀ i ∈ shared, source (sigma i) = target (tau i))
    (hpromoted : ∀ i : ↥promoted,
      target (tau i.val) = old (chooseOld i)) :
    (Finset.univ : Finset (Fin M)).image target =
      shared.image (fun i => source (sigma i)) ∪
      promoted.attach.image (fun i => old (chooseOld i)) ∪
      ((Finset.univ \ (shared ∪ promoted)).image
        (fun i => target (tau i))) := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, hvalue⟩
    subst v
    let t := tau.symm i
    have hti : tau t = i := tau.apply_symm_apply _
    by_cases hs : t ∈ shared
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨t, hs,
        by rw [hshared t hs, hti]⟩
    · by_cases hp : t ∈ promoted
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr
          ⟨⟨t, hp⟩, by simp, by rw [← hpromoted ⟨t,hp⟩, hti]⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr
          ⟨t, by simp [hs,hp], by rw [hti]⟩
  · intro h
    rcases Finset.mem_union.mp h with h | hf
    · rcases Finset.mem_union.mp h with hs | hp
      · rcases Finset.mem_image.mp hs with ⟨i, hi, rfl⟩
        exact Finset.mem_image.mpr
          ⟨tau i, Finset.mem_univ _, (hshared i hi).symm⟩
      · rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩
        exact Finset.mem_image.mpr
          ⟨tau i.val, Finset.mem_univ _, hpromoted i⟩
    · rcases Finset.mem_image.mp hf with ⟨i, _, rfl⟩
      exact Finset.mem_image.mpr ⟨tau i, Finset.mem_univ _, rfl⟩

end Green64FullPhysicalE

end

/-! ## SourceActualCanonicalYSupport -/

section

open Filter
namespace Green64Analytic.CorrelationMellin

/-! The source size Y=x^(1+o(1)) is used as the honest
natural coefficient support ceiling. Fixed log-frequency shifts
are negligible compared to x²; no high-U1 range input is assumed. -/
theorem eventually_source_ceil_Y_shift_below_exp_two_L
    (s1 : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (Y sigma1 : ℝ),
      4 ≤ Y → Y ≤ Real.exp (3*L/2) →
      |sigma1| ≤ L^s1 →
      ((⌈Y⌉₊:ℝ) + |sigma1|) ≤ Real.exp (2*L) := by
  have hE1 : Tendsto (fun L : ℝ => Real.exp (L/2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_div_const_atTop_of_pos (by norm_num : (0:ℝ)<2)).2 tendsto_id)
  have hE2 : Tendsto (fun L : ℝ => Real.exp (2*L)/L^s1)
      atTop atTop := by
    simpa only [Real.rpow_natCast] using
      (tendsto_exp_mul_div_rpow_atTop (s1:ℝ) 2 (by norm_num))
  filter_upwards [hE1.eventually (eventually_ge_atTop (3:ℝ)),
    hE2.eventually (eventually_ge_atTop (3:ℝ)),
    eventually_ge_atTop (3:ℝ)] with L hExpHalf hExpRatio hL
  intro Y sigma1 hY hYupper hShift
  have hYnat : (⌈Y⌉₊:ℝ) < Y+1 :=
    Nat.ceil_lt_add_one (by linarith)
  have hExpPos : 0 < Real.exp (3*L/2) := Real.exp_pos _
  have hExpTwo : 0 < Real.exp (2*L) := Real.exp_pos _
  have hExpOne : 3 * Real.exp (3*L/2) ≤ Real.exp (2*L) := by
    calc
      _ ≤ Real.exp (L/2) * Real.exp (3*L/2) :=
        mul_le_mul_of_nonneg_right hExpHalf hExpPos.le
      _ = Real.exp (2*L) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hLpos : 0 < L := by linarith
  have hPowPos : 0 < L^s1 := pow_pos hLpos _
  have hExpLog : 3*L^s1 ≤ Real.exp (2*L) := by
    have hh := (le_div_iff₀ hPowPos).mp hExpRatio
    nlinarith
  have hExpConst : (3:ℝ) ≤ Real.exp (2*L) := by
    have hh := Real.add_one_le_exp (2*L)
    linarith
  nlinarith
end Green64Analytic.CorrelationMellin

end

/-! ## SourceD61RatioFiberGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- The complex Gram on any EXACT arithmetic equivalence fibres is a
sum of squared fibre sums, not a sum of individual absolute values.
It retains all off-diagonal complex cross terms WITHIN each fibre. -/
theorem exact_complex_diagonal_key_fibres434
    {ι κ : Type} [DecidableEq κ]
    (S : Finset ι) (key : ι → κ) (B : ι → ℂ) :
    (∑ i ∈ S, ∑ j ∈ S,
      if key i = key j then B i * star (B j) else 0) =
    ∑ c ∈ S.image key,
      (∑ i ∈ S.filter (fun i => key i = c), B i) *
      star (∑ j ∈ S.filter (fun j => key j = c), B j) := by
  classical
  have hInner (i : ι) :
      (∑ j ∈ S,
        if key i = key j then B i * star (B j) else 0) =
      B i * star (∑ j ∈ S.filter (fun j => key j = key i), B j) := by
    rw [star_sum, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : key i = key j
    · simp [h, eq_comm]
    · simp [h, eq_comm]
  simp_rw [hInner]
  have hFibre := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := S.image key) (g := key)
    (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    (fun i => B i * star
      (∑ j ∈ S.filter (fun j => key j = key i), B j))
  rw [←hFibre]
  apply Finset.sum_congr rfl
  intro c hc
  have hval : ∀ i ∈ S.filter (fun i => key i = c),
      (∑ j ∈ S.filter (fun j => key j = key i), B j) =
      ∑ j ∈ S.filter (fun j => key j = c), B j := by
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  calc
    _ = ∑ i ∈ S.filter (fun i => key i=c),
        B i * star (∑ j ∈ S.filter (fun j => key j=c), B j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hval i hi]
    _ = (∑ i ∈ S.filter (fun i => key i=c), B i) *
        star (∑ j ∈ S.filter (fun j => key j=c), B j) := by
      rw [Finset.sum_mul]


/-- The precise rational-slope fibres of the integer D61 cofactor
diagonal mt'=m't. All t_i are positive on the actual rough source
cofactor support. Within each fibre we retain the complex signed sum,
rather than replacing it by an absolute majorant. -/
theorem integer_ratio_complex_diagonal_fibres434
    {ι : Type} (S : Finset ι) (m t : ι → ℕ) (B : ι → ℂ)
    (ht : ∀ i ∈ S, 0 < t i) :
    (∑ i ∈ S, ∑ j ∈ S,
      if (m i:ℤ)*(t j:ℤ) = (m j:ℤ)*(t i:ℤ)
      then B i * star (B j) else 0) =
    ∑ q ∈ S.image (fun i => (m i:ℚ)/(t i:ℚ)),
      (∑ i ∈ S.filter (fun i => (m i:ℚ)/(t i:ℚ)=q), B i) *
      star (∑ j ∈ S.filter (fun j => (m j:ℚ)/(t j:ℚ)=q), B j) := by
  classical
  let slope : ι → ℚ := fun i => (m i:ℚ)/(t i:ℚ)
  have hRel (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      ((m i:ℤ)*(t j:ℤ) = (m j:ℤ)*(t i:ℤ)) ↔
      slope i = slope j := by
    have hti : (t i:ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (ht i hi))
    have htj : (t j:ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (ht j hj))
    dsimp [slope]
    rw [div_eq_div_iff hti htj]
    norm_cast
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S,
        if slope i = slope j then B i * star (B j) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases he : slope i = slope j
      · have heq := (hRel i hi j hj).mpr he
        simp [he, heq]
      · have hneq : ¬ (m i:ℤ)*(t j:ℤ) = (m j:ℤ)*(t i:ℤ) := by
          exact fun hz => he ((hRel i hi j hj).mp hz)
        simp [he, hneq]
    _ = _ := exact_complex_diagonal_key_fibres434 S slope B

/-- The rational-ratio diagonal is positive semidefinite, even with
arbitrary signed complex physical coefficients. Small-k residue
orthogonality therefore has an exact, potentially dominant diagonal
cost; it cannot be discarded with an unsigned majorant. -/
theorem integer_ratio_complex_diagonal_nonneg434
    {ι : Type} (S : Finset ι) (m t : ι → ℕ) (B : ι → ℂ)
    (ht : ∀ i ∈ S, 0 < t i) :
    0 ≤ (∑ i ∈ S, ∑ j ∈ S,
      if (m i:ℤ)*(t j:ℤ) = (m j:ℤ)*(t i:ℤ)
      then B i * star (B j) else 0).re := by
  rw [integer_ratio_complex_diagonal_fibres434 S m t B ht, Complex.re_sum]
  apply Finset.sum_nonneg
  intro q hq
  let z : ℂ := ∑ i ∈ S.filter (fun i => (m i:ℚ)/(t i:ℚ)=q), B i
  change 0 ≤ (z * (starRingEnd ℂ) z).re
  rw [Complex.mul_conj]
  exact Complex.normSq_nonneg z
end Green64ComparisonPartial

end

end

/-! ## SourceD61SmallModulusGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- At source k=±2, the character modulus q=|k| is two. On W-rough
long-cofactor support all m,t are odd; the congruence
2|(m*t'-m'*t) is automatic for every pair, not just diagonal ones. -/
theorem q_two_congruence_automatic_for_odd_cofactors434
    (m t m' t' : ℤ)
    (hm : Odd m) (ht : Odd t)
    (hm' : Odd m') (ht' : Odd t') :
    (2:ℤ) ∣ m*t' - m'*t := by
  exact even_iff_two_dvd.mp
    ((hm.mul ht').sub_odd (hm'.mul ht))

/-- Full complex residue Gram restricted to the true off-integer-diagonal
mt'≠m't, without discarding conjugate cross terms. -/
theorem q_two_residue_gram_exact434
    {ι : Type} (S : Finset ι)
    (m t : ι → ℤ) (B : ι → ℂ)
    (hm : ∀ i ∈ S, Odd (m i))
    (ht : ∀ i ∈ S, Odd (t i)) :
    (∑ i ∈ S, ∑ j ∈ S,
      if (2:ℤ) ∣ (m i*t j - m j*t i) ∧
          m i*t j ≠ m j*t i
      then B i * star (B j) else 0) =
      (∑ i ∈ S, B i) * star (∑ i ∈ S, B i) -
      ∑ i ∈ S, ∑ j ∈ S,
        if m i*t j = m j*t i then B i * star (B j) else 0 := by
  classical
  have hCong (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      (2:ℤ) ∣ m i*t j - m j*t i :=
    q_two_congruence_automatic_for_odd_cofactors434
      (m i) (t i) (m j) (t j)
      (hm i hi) (ht i hi) (hm j hj) (ht j hj)
  have hpoint (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      (if (2:ℤ) ∣ (m i*t j - m j*t i) ∧
          m i*t j ≠ m j*t i
       then B i * star (B j) else 0) =
        B i * star (B j) -
        (if m i*t j = m j*t i then B i * star (B j) else 0) := by
    by_cases heq : m i*t j = m j*t i
    · simp [heq]
    · simp [hCong i hi j hj, heq]
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S,
          (B i * star (B j) -
          (if m i*t j = m j*t i then B i * star (B j) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hpoint i hi j hj
    _ = (∑ i ∈ S, ∑ j ∈ S, B i * star (B j)) -
        ∑ i ∈ S, ∑ j ∈ S,
          (if m i*t j = m j*t i then B i * star (B j) else 0) := by
      simp_rw [Finset.sum_sub_distrib]
    _ = (∑ i ∈ S, B i) * star (∑ i ∈ S, B i) -
        ∑ i ∈ S, ∑ j ∈ S,
          (if m i*t j = m j*t i then B i * star (B j) else 0) := by
      congr 1
      calc
        (∑ i ∈ S, ∑ j ∈ S, B i * star (B j)) =
          ∑ i ∈ S, B i * (∑ j ∈ S, star (B j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
        _ = (∑ i ∈ S, B i) * (∑ j ∈ S, star (B j)) := by
            rw [Finset.sum_mul]
        _ = (∑ i ∈ S, B i) * star (∑ j ∈ S, B j) := by
            rw [star_sum]
end Green64ComparisonPartial

end

end

/-! ## SourceOriginalCenteredGramSchur -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- A centered Gram operator is small in Hilbert norm: this is
the quantitative *difference from the ideal identity* required
for comparison, not merely a bound on the original frame norm.
The diagonal is exactly nu, and each offdiagonal entry is eps.
Works with arbitrary complex coefficient tests, no factorization. -/
theorem source_original_centered_finite_gram_schur434
    {C : Type} [Fintype C] [DecidableEq C]
    (G : C → C → ℂ) (nu eps : ℝ) (heps : 0 ≤ eps)
    (hdiag : ∀ c, G c c = (nu:ℂ))
    (hoff : ∀ c d, c ≠ d → ‖G c d‖ ≤ eps)
    (a : C → ℂ) :
    (∑ c : C,
      ‖∑ d : C,
        (G c d - if c=d then (nu:ℂ) else 0)*a d‖^2) ≤
      ((Fintype.card C:ℝ)*eps)^2 *
        (∑ d : C, ‖a d‖^2) := by
  let H : C → C → ℂ := fun c d =>
    G c d - if c=d then (nu:ℂ) else 0
  let R : ℝ := (Fintype.card C:ℝ)*eps
  have hR : 0 ≤ R :=
    mul_nonneg (Nat.cast_nonneg _) heps
  have hentry (c d : C) : ‖H c d‖ ≤ eps := by
    by_cases h : c = d
    · subst d
      simp [H, hdiag, heps]
    · simp only [H, if_neg h, sub_zero]
      exact hoff c d h
  have hrow (c : C) : (∑ d : C, ‖H c d‖) ≤ R := by
    calc
      _ ≤ ∑ _d : C, eps := Finset.sum_le_sum (fun d _ => hentry c d)
      _ = R := by simp [R]
  have hcol (d : C) : (∑ c : C, ‖H c d‖) ≤ R := by
    calc
      _ ≤ ∑ _c : C, eps := Finset.sum_le_sum (fun c _ => hentry c d)
      _ = R := by simp [R]
  have hSchur :=
    Green64FullPhysicalE.memory_finite_rectangular_schur_sq
      (X:=C) (Y:=C) (S:=Finset.univ)
      (mx:=fun _ => (1:ℝ)) (my:=fun _ => (1:ℝ))
      (wx:=fun _ => (1:ℝ)) (wy:=fun _ => (1:ℝ))
      H a R R
      (fun _ => zero_le_one)
      (fun _ _ => zero_lt_one)
      (fun c => by simpa only [mul_one] using hrow c)
      (fun d _ => by simpa only [one_mul, mul_one] using hcol d)
      hR
  simpa only [H, R, one_mul, mul_one, pow_two] using hSchur
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteSignedRawKnuMinorCombine -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The EXACT original signed RAW-minus-primitive-Knu
residual under two genuine Hilbert operator C6 squared-norm
bounds, with NO assumption of cancellation between RAW and
Knu. The factor 2 is exactly the triangle-square cost, and
the common physical source/target inverse-atom energies are
retained unchanged, including all original sign conventions. -/
theorem source_original_finite_signed_RAW_minus_Knu_L2_combine434
    (Knu SignedRaw : ℂ)
    (EA EB BK BR : ℝ)
    (hEA : 0 ≤ EA) (hEB : 0 ≤ EB)
    (hBK : 0 ≤ BK) (hBR : 0 ≤ BR)
    (hK : ‖Knu‖^2 ≤ BK*EA*EB)
    (hR : ‖SignedRaw‖^2 ≤ BR*EA*EB) :
    ‖Knu-SignedRaw‖^2 ≤
      2*(BK+BR)*EA*EB := by
  have hTri := norm_sub_le Knu SignedRaw
  have hTriSq :
      ‖Knu-SignedRaw‖^2 ≤
      (‖Knu‖+‖SignedRaw‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hTri 2
  have hCore : ‖Knu-SignedRaw‖^2 ≤
      2*(‖Knu‖^2+‖SignedRaw‖^2) := by
    nlinarith [hTriSq,sq_nonneg (‖Knu‖-‖SignedRaw‖)]
  have hKB : ‖Knu‖^2 ≤ BK*(EA*EB) := by
    simpa only [mul_assoc] using hK
  have hRB : ‖SignedRaw‖^2 ≤ BR*(EA*EB) := by
    simpa only [mul_assoc] using hR
  calc
    _ ≤ 2*(‖Knu‖^2+‖SignedRaw‖^2) := hCore
    _ ≤ 2*(BK*(EA*EB)+BR*(EA*EB)) := by
      gcongr
    _ = 2*(BK+BR)*EA*EB := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalCollarGeometry -/

section

namespace Green64Analytic.CorrelationSquare

/-- A quadratic logarithmic remainder with explicit constant, valid on
    the union of the source collar kernels. No Taylor theorem is assumed. -/
theorem source_collar_log_remainder434 (w v : ℝ) (hv : 0 < v)
    (hclose : |w-v| ≤ v/2) :
    |(w-v)-v*Real.log (w/v)| ≤ 2*(w-v)^2/v := by
  have hw : 0 < w := by
    have := (abs_le.mp hclose).1
    linarith
  have hx : 0 < w/v := div_pos hw hv
  have hup := Real.add_one_le_exp (Real.log (w/v))
  rw [Real.exp_log hx] at hup
  have hlo := Real.add_one_le_exp (-Real.log (w/v))
  rw [Real.exp_neg,Real.exp_log hx] at hlo
  have hu : v*Real.log (w/v) ≤ w-v := by
    have := (mul_le_mul_of_nonneg_left hup hv.le)
    field_simp at this
    nlinarith
  have hl' : w*((w-v)-v*Real.log (w/v)) ≤ (w-v)^2 := by
    have h := mul_le_mul_of_nonneg_left hlo (mul_pos hv hw).le
    have hid : v*w*(w/v)⁻¹ = v^2 := by field_simp
    rw [hid] at h
    nlinarith
  have hwv : v ≤ 2*w := by
    have := (abs_le.mp hclose).1
    linarith
  rw [abs_of_nonneg (sub_nonneg.mpr hu)]
  apply (le_div_iff₀ hv).2
  have hmul := mul_le_mul_of_nonneg_right hwv (sub_nonneg.mpr hu)
  nlinarith


/-- The source log kernel can be nonzero only in an additive collar.
This uses the actual log kernel argument, not an assumed support bound. -/
theorem source_collar_log_support434 (w v E : ℝ) (hw : 0 < w)
    (hv : 0 < v) (hE : 0 ≤ E) (hsmall : E ≤ v/2)
    (hlog : |v*Real.log (w/v)| ≤ E) : |w-v| ≤ 2*E := by
  have hx := div_pos hw hv
  have hup := Real.add_one_le_exp (Real.log (w/v))
  rw [Real.exp_log hx] at hup
  have hu := mul_le_mul_of_nonneg_left hup hv.le
  have hu' : v*Real.log (w/v) ≤ w-v := by
    field_simp at hu
    nlinarith
  have hlo := Real.add_one_le_exp (-Real.log (w/v))
  rw [Real.exp_neg,Real.exp_log hx] at hlo
  have hl := mul_le_mul_of_nonneg_left hlo (mul_pos hv hw).le
  have hid : v*w*(w/v)⁻¹ = v^2 := by field_simp
  rw [hid] at hl
  obtain ⟨hlower,hupper⟩ := abs_le.mp hlog
  apply abs_le.mpr
  constructor
  · linarith
  · have hh := mul_le_mul_of_nonneg_left hupper hw.le
    by_cases hd : 0 ≤ w-v
    · have hp := mul_nonneg (show 0 ≤ v/2-E by linarith) hd
      nlinarith
    · linarith

/-- Explicit source collar argument perturbation. -/
theorem source_collar_argument_difference434 (w v H Y A δ : ℝ)
    (hv : 0 < v) (hH : 0 < H) (hY : 0 < Y) (hA : 0 < A)
    (hδ : 0 ≤ δ) (hvY : Y/(2*A) ≤ v)
    (hclose : |w-v| ≤ 2*δ*H) (hsmall : 2*δ*H ≤ v/2) :
    |(w-v)/H-v*Real.log (w/v)/H| ≤ 16*A*δ^2*H/Y := by
  have hq := source_collar_log_remainder434 w v hv (hclose.trans hsmall)
  have hsquare : (w-v)^2 ≤ (2*δ*H)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hclose
  have hvY' : Y ≤ 2*A*v := by
    have := (div_le_iff₀ (by positivity : 0 < 2*A)).mp hvY
    nlinarith
  rw [← sub_div,abs_div,abs_of_pos hH]
  apply (div_le_iff₀ hH).2
  have hq' := (le_div_iff₀ hv).mp hq
  have hFinal : |(w-v)-v*Real.log (w/v)| *Y ≤ 16*A*δ^2*H^2 := by
    calc
      _ ≤ |(w-v)-v*Real.log (w/v)| *(2*A*v) :=
        mul_le_mul_of_nonneg_left hvY' (abs_nonneg _)
      _ = 2*A*(|(w-v)-v*Real.log (w/v)| *v) := by ring
      _ ≤ 2*A*(2*(w-v)^2) := mul_le_mul_of_nonneg_left hq' (by positivity)
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ 4*A)
        nlinarith
  have hFin := (le_div_iff₀ hY).2 hFinal
  convert hFin using 1 <;> ring

end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalCollarKernel -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

noncomputable def sourceCollarKernelDifference434
    (K : ℝ → ℂ) (H : ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  K (((n:ℝ)-v)/H) - K (v*Real.log ((n:ℝ)/v)/H)

/-- True physical collar kernel support and perturbation bound.
Auxiliary bump hypotheses are regularity, never energy hypotheses. -/
theorem source_collar_kernel_difference434
    (K : ℝ → ℂ) (M δ H Y A v : ℝ) (n : ℕ)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hH : 0 < H) (hY : 0 < Y) (hA : 0 < A)
    (hvY : Y/(2*A) ≤ v) (hHcap : H ≤ Y/(8*A)) (hn : 0 < n)
    (hSupport : ∀ z, K z ≠ 0 → |z| ≤ δ)
    (hLip : ∀ z z', ‖K z-K z'‖ ≤ M*|z-z'|) :
    (sourceCollarKernelDifference434 K H n v ≠ 0 → |(n:ℝ)-v| ≤ 2*δ*H) ∧
    ‖sourceCollarKernelDifference434 K H n v‖ ≤ 16*A*δ^2*M*H/Y := by
  have hv : 0 < v := (div_pos hY (by positivity)).trans_le hvY
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hHv : H ≤ v/4 := by
    have hYv := (div_le_iff₀ (by positivity : 0 < 2*A)).mp hvY
    have hHY := (le_div_iff₀ (by positivity : 0 < 8*A)).mp hHcap
    nlinarith
  have hsmall : 2*δ*H ≤ v/2 := by
    have := mul_le_mul_of_nonneg_right hδ1 hH.le
    nlinarith
  have hUnion : sourceCollarKernelDifference434 K H n v ≠ 0 →
      |(n:ℝ)-v| ≤ 2*δ*H := by
    intro hNZ
    by_cases hAdd : K (((n:ℝ)-v)/H) = 0
    · have hLog : K (v*Real.log ((n:ℝ)/v)/H) ≠ 0 := by
        intro hZero
        exact hNZ (by simp [sourceCollarKernelDifference434,hAdd,hZero])
      have hb := hSupport _ hLog
      rw [abs_div,abs_of_pos hH] at hb
      have hb' := (div_le_iff₀ hH).mp hb
      simpa only [mul_assoc] using source_collar_log_support434 (n:ℝ) v (δ*H) hnR hv
        (by positivity) (by linarith) hb'
    · have hb := hSupport _ hAdd
      rw [abs_div,abs_of_pos hH] at hb
      have hb' := (div_le_iff₀ hH).mp hb
      nlinarith
  refine ⟨hUnion,?_⟩
  by_cases hNZ : sourceCollarKernelDifference434 K H n v = 0
  · rw [hNZ,norm_zero]
    positivity
  · have hc := hUnion hNZ
    have hArg := source_collar_argument_difference434 (n:ℝ) v H Y A δ
      hv hH hY hA hδ hvY hc hsmall
    have hK := hLip (((n:ℝ)-v)/H) (v*Real.log ((n:ℝ)/v)/H)
    calc
      _ ≤ M*|((n:ℝ)-v)/H-v*Real.log ((n:ℝ)/v)/H| := hK
      _ ≤ M*(16*A*δ^2*H/Y) := mul_le_mul_of_nonneg_left hArg hM
      _ = _ := by ring

/-- Integer collar occupancy, including nonintegral boundary centers. -/
theorem source_collar_integer_count434 (F : Finset ℕ) (v E : ℝ)
    (hE : 0 ≤ E) (hEv : E ≤ v) :
    (((F.filter (fun n : ℕ => |(n:ℝ)-v| ≤ E)).card:ℕ):ℝ) ≤ 2*E+1 := by
  classical
  let J := F.filter (fun n : ℕ => |(n:ℝ)-v| ≤ E)
  have hSub : J ⊆ Finset.Icc ⌈v-E⌉₊ ⌊v+E⌋₊ := by
    intro n hn
    have hb := (Finset.mem_filter.mp hn).2
    obtain ⟨hl,hu⟩ := abs_le.mp hb
    exact Finset.mem_Icc.mpr ⟨(Nat.ceil_le).mpr (by linarith),
      (Nat.le_floor_iff (by linarith : 0 ≤ v+E)).mpr (by linarith)⟩
  by_cases hJ : J.Nonempty
  · obtain ⟨n,hn⟩ := hJ
    have hbounds := Finset.mem_Icc.mp (hSub hn)
    have hOrder : ⌈v-E⌉₊ ≤ ⌊v+E⌋₊ := hbounds.1.trans hbounds.2
    have hCard := Finset.card_le_card hSub
    rw [Nat.card_Icc] at hCard
    have hNat : ⌊v+E⌋₊ + 1 - ⌈v-E⌉₊ = ⌊v+E⌋₊ + 1 - ⌈v-E⌉₊ := rfl
    have hcast := Nat.cast_le (α:=ℝ).mpr hCard
    rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one] at hcast
    have hf := Nat.floor_le (show 0 ≤ v+E by linarith)
    have hc := Nat.le_ceil (v-E)
    change (J.card:ℝ) ≤ _
    linarith
  · have hz : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    change (J.card:ℝ) ≤ _
    rw [hz]
    simp only [Finset.card_empty,Nat.cast_zero]
    linarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalCollarError -/

section

open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.CorrelationSquare

/-- The actual source collar replacement error with both occupancy
factors integrated. This is NOT an additive-to-Mellin energy premise. -/
theorem source_physical_collar_replacement_error434
    (F : Finset ℕ) (a : ℕ → ℂ) (K : ℝ → ℂ) (M δ H Y A : ℝ)
    (hF : ∀ n ∈ F, 0 < n) (hK : Continuous K)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hH : 1 ≤ H) (hY : 0 < Y) (hA : 0 < A)
    (hHcap : H ≤ Y/(8*A))
    (hSupport : ∀ z, K z ≠ 0 → |z| ≤ δ)
    (hLip : ∀ z z', ‖K z-K z'‖ ≤ M*|z-z'|) :
    (H^2)⁻¹ * (∫ v in Set.Icc (Y/(2*A)) (2*A*Y),
      ‖∑ n ∈ F, a n * sourceCollarKernelDifference434 K H n v‖^2) ≤
    4*δ*(4*δ+1)*(16*A*δ^2*M)^2*(H/Y)^2 * ∑ n ∈ F, ‖a n‖^2 := by
  classical
  let V := Set.Icc (Y/(2*A)) (2*A*Y)
  let B := 16*A*δ^2*M*H/Y
  let R := (4*δ+1)*H*B^2
  let g : ℕ → ℝ → ℝ := fun n v =>
    (Set.Icc ((n:ℝ)-2*δ*H) ((n:ℝ)+2*δ*H)).indicator (fun _ => ‖a n‖^2) v
  have hHp : 0 < H := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD (n : ℕ) (hn : n ∈ F) : ContinuousOn
      (sourceCollarKernelDifference434 K H n) V := by
    intro v hvV
    have hv : 0 < v := (div_pos hY (by positivity)).trans_le hvV.1
    have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (hF n hn)
    have hr : ContinuousAt (fun v : ℝ => (n:ℝ)/v) v :=
      continuousAt_const.div continuousAt_id hv.ne'
    have hl := (Real.continuousAt_log (div_pos hnR hv).ne').comp hr
    have hx : ContinuousAt (fun v : ℝ => ((n:ℝ)-v)/H) v := by fun_prop
    have hy : ContinuousAt (fun v : ℝ => v*Real.log ((n:ℝ)/v)/H) v :=
      (continuousAt_id.mul hl).div_const H
    exact ((hK.continuousAt.comp hx).sub (hK.continuousAt.comp hy)).continuousWithinAt
  have hInt : IntegrableOn (fun v =>
      ‖∑ n ∈ F, a n * sourceCollarKernelDifference434 K H n v‖^2) V := by
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.pow
    apply ContinuousOn.norm
    apply continuousOn_finset_sum
    intro n hn
    exact continuousOn_const.mul (hD n hn)
  have hgInt (n : ℕ) : Integrable (g n) :=
    (integrableOn_const (s:=Set.Icc ((n:ℝ)-2*δ*H) ((n:ℝ)+2*δ*H)) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hgNonneg (n : ℕ) (v : ℝ) : 0 ≤ g n v := by
    simp only [g,Set.indicator_apply]
    split_ifs <;> positivity
  have hgV (n : ℕ) : IntegrableOn (g n) V := (hgInt n).integrableOn
  have hSumInt : IntegrableOn (fun v => ∑ n ∈ F, g n v) V :=
    integrable_finset_sum F (fun n _ => hgV n)
  have hPoint (v : ℝ) (hvV : v ∈ V) :
      ‖∑ n ∈ F, a n * sourceCollarKernelDifference434 K H n v‖^2 ≤
        R * ∑ n ∈ F, g n v := by
    let J := F.filter (fun n : ℕ => |(n:ℝ)-v| ≤ 2*δ*H)
    have hv : 0 < v := (div_pos hY (by positivity)).trans_le hvV.1
    have hYv := (div_le_iff₀ (by positivity : 0 < 2*A)).mp hvV.1
    have hHY := (le_div_iff₀ (by positivity : 0 < 8*A)).mp hHcap
    have hsmall : 2*δ*H ≤ v := by
      have hh := mul_le_mul_of_nonneg_right hδ1 hHp.le
      nlinarith
    have hCount := source_collar_integer_count434 F v (2*δ*H) (by positivity) hsmall
    have hCard : (J.card:ℝ) ≤ (4*δ+1)*H := by
      change (J.card:ℝ) ≤ _ at hCount
      nlinarith
    have heq : (∑ n ∈ F, a n * sourceCollarKernelDifference434 K H n v) =
        ∑ n ∈ J, a n * sourceCollarKernelDifference434 K H n v := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hn hNot
      have hc := (source_collar_kernel_difference434 K M δ H Y A v n
        hM hδ hδ1 hHp hY hA hvV.1 hHcap (hF n hn) hSupport hLip).1
      have hz : sourceCollarKernelDifference434 K H n v = 0 := by
        by_contra hNZ
        exact hNot (Finset.mem_filter.mpr ⟨hn,hc hNZ⟩)
      simp [hz]
    have hNorm : ‖∑ n ∈ J, a n * sourceCollarKernelDifference434 K H n v‖ ≤
        B * ∑ n ∈ J, ‖a n‖ := by
      calc
        _ ≤ ∑ n ∈ J, ‖a n * sourceCollarKernelDifference434 K H n v‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ J, B*‖a n‖ := by
          apply Finset.sum_le_sum
          intro n hn
          have hb := (source_collar_kernel_difference434 K M δ H Y A v n
            hM hδ hδ1 hHp hY hA hvV.1 hHcap
            (hF n (Finset.mem_filter.mp hn).1) hSupport hLip).2
          rw [norm_mul,mul_comm]
          exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ = _ := by rw [Finset.mul_sum]
    have hCS : (∑ n ∈ J, ‖a n‖)^2 ≤ (J.card:ℝ) * ∑ n ∈ J, ‖a n‖^2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => (1:ℝ)) (fun n => ‖a n‖)
    have hSq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ B*∑ n ∈ J, ‖a n‖)).mpr hNorm
    have hCoeffEq : (∑ n ∈ J, ‖a n‖^2) = ∑ n ∈ F, g n v := by
      simp only [J,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      have hi : |(n:ℝ)-v| ≤ 2*δ*H ↔ v ∈ Set.Icc ((n:ℝ)-2*δ*H) ((n:ℝ)+2*δ*H) := by
        rw [abs_le,Set.mem_Icc]
        constructor <;> intro hh <;> constructor <;> linarith [hh.1,hh.2]
      simp only [g,Set.indicator_apply,hi]
    rw [heq]
    calc
      _ ≤ B^2*(∑ n ∈ J, ‖a n‖)^2 := by simpa only [mul_pow] using hSq
      _ ≤ B^2*((J.card:ℝ)*∑ n ∈ J, ‖a n‖^2) :=
        mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
      _ ≤ B^2*(((4*δ+1)*H)*∑ n ∈ J, ‖a n‖^2) := by gcongr
      _ = R * ∑ n ∈ F, g n v := by rw [hCoeffEq]; dsimp [R]; ring
  have hIntegral := setIntegral_mono_on hInt (hSumInt.const_mul R) measurableSet_Icc hPoint
  rw [integral_const_mul,integral_finset_sum F (fun n _ => hgV n)] at hIntegral
  have hgBound (n : ℕ) : (∫ v in V, g n v) ≤ 4*δ*H*‖a n‖^2 := by
    have hmono : (∫ v in V, g n v) ≤ ∫ v, g n v := by
      apply setIntegral_le_integral (hgInt n) (by exact Filter.Eventually.of_forall (hgNonneg n))
    calc
      _ ≤ ∫ v, g n v := hmono
      _ = 4*δ*H*‖a n‖^2 := by
        dsimp [g]
        rw [integral_indicator measurableSet_Icc,integral_const]
        simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ ((n:ℝ)+2*δ*H)-((n:ℝ)-2*δ*H))]
        ring
  have hS := Finset.sum_le_sum (fun n (hn : n ∈ F) => hgBound n)
  rw [← Finset.mul_sum] at hS
  have hTotal := mul_le_mul_of_nonneg_left hS hR
  have hEnd : (∫ v in V, ‖∑ n ∈ F, a n * sourceCollarKernelDifference434 K H n v‖^2) ≤
      R*(4*δ*H*(∑ n ∈ F, ‖a n‖^2)) := hIntegral.trans hTotal
  have hScaled := mul_le_mul_of_nonneg_left hEnd (by positivity : 0 ≤ (H^2)⁻¹)
  change (H^2)⁻¹ * (∫ v in V, ‖∑ n ∈ F, a n * sourceCollarKernelDifference434 K H n v‖^2) ≤ _
  convert hScaled using 1
  dsimp [R,B]
  field_simp
  <;> ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalLinearFourierShift -/

section

open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare

/-- Exact real Fourier transformation of an additive translate:
the ORIGINAL ordinary collar is a sum of genuine translates,
not the logarithmic collar. The source endpoint n is unchanged. -/
theorem source_linear_collar_fourier_translation434
    (f : ℝ → ℂ) (n s : ℝ) :
    (𝓕 (fun v : ℝ => f (v-n))) s =
      Complex.exp ((((-2*Real.pi*(n*s):ℝ):ℂ)*Complex.I)) *
        (𝓕 f) s := by
  have h := VectorFourier.fourierIntegral_comp_add_right
    (e := Real.fourierChar) (μ := volume)
    (L := innerₗ ℝ) f (-n)
  have hs := congrFun h s
  change (𝓕 (fun v : ℝ => f (v-n))) s =
      Real.fourierChar (⟪-n,s⟫) • (𝓕 f) s at hs
  rw [hs]
  simp only [Real.inner_apply, Real.fourierChar_apply, Circle.smul_def]
  rw [show (-n)*s = -(n*s) by ring]
  simp only [smul_eq_mul]
  congr 1
  push_cast
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalLinearFourierDilation -/

section

open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 500000

/-- Exact ORIGINAL one-dimensional Fourier scaling for the linear
physical collar (n-v)/H. The reflection inverts frequency, and
the Jacobian is exactly H, not 1/H or an altered Fourier convention. -/
theorem source_linear_collar_fourier_dilation434
    (K : ℝ → ℂ) (H : ℝ) (hH : 0 < H) (s : ℝ) :
    (𝓕 (fun v : ℝ => K ((-v)/H))) s =
      (H:ℂ)*(𝓕 K) (-H*s) := by
  let a : ℝ := -(1/H)
  let g : ℝ → ℂ := fun u =>
    Complex.exp (((-2*Real.pi*((-H)*u*s):ℝ):ℂ)*Complex.I)*K u
  have ha : a ≠ 0 := by
    dsimp [a]
    simp [hH.ne']
  have haH : a⁻¹ = -H := by
    dsimp [a]
    field_simp
  have hChange :
      (∫ v : ℝ, Complex.exp
          (((-2*Real.pi*(v*s):ℝ):ℂ)*Complex.I) * K ((-v)/H)) =
      ∫ v : ℝ, g (a*v) := by
    apply integral_congr_ae
    filter_upwards with v
    dsimp [g,a]
    have hv : (-H)*(-(1/H)*v) = v := by
      field_simp
    rw [hv]
    congr 1
    field_simp
  have hInt := Measure.integral_comp_mul_left g a
  have hInvAbs : |a⁻¹| = H := by
    rw [haH]
    simpa only [abs_neg,abs_of_pos hH]
  rw [Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply,smul_eq_mul]
  calc
    (∫ v : ℝ, Complex.exp (((-2*Real.pi*(v*s):ℝ):ℂ)*Complex.I) *
      K ((-v)/H)) =
        ∫ v : ℝ, g (a*v) := hChange
    _ = (H:ℂ)*(∫ u : ℝ, g u) := by
      rw [hInt,hInvAbs]
      simp only [smul_eq_mul, Complex.real_smul]
    _ = (H:ℂ)*(∫ u : ℝ,
      Complex.exp (((-2*Real.pi*(u*(-H*s)):ℝ):ℂ)*Complex.I)*K u) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with u
      dsimp [g]
      congr 2 <;> ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalLinearFourierOneTerm -/

section

open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 400000

/-- Exact Fourier image of one actual ordinary ADDITIVE physical collar:
the Jacobian is H, time frequency is -H*s and the n-dependent
phase is exp(-2*pi*i*n*s). Valid for arbitrary K because the
integral Fourier definition retains its default-zero convention. -/
theorem source_linear_collar_fourier_one_term434
    (K : ℝ → ℂ) (H : ℝ) (hH : 0 < H) (n s : ℝ) :
    (𝓕 (fun v : ℝ => K ((n-v)/H))) s =
      Complex.exp ((((-2*Real.pi*(n*s):ℝ):ℂ)*Complex.I)) *
        (H:ℂ)*(𝓕 K) (-H*s) := by
  let f : ℝ → ℂ := fun v => K ((-v)/H)
  have heq : (fun v : ℝ => K ((n-v)/H)) =
      (fun v : ℝ => f (v-n)) := by
    funext v
    dsimp [f]
    congr 1
    ring
  rw [heq, source_linear_collar_fourier_translation434 f n s,
    source_linear_collar_fourier_dilation434 K H hH s]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalLinearFourierFinite -/

section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 950000

/-- Fubini for an ACTUAL finite ordinary linear collar sum:
there is no default-zero integrability gap. Complex Fourier phases
use the exact -2*pi*I convention. -/
theorem source_linear_collar_finite_fourier434
    (K : ℝ → ℂ) (hK : Integrable K) (hKcont : Continuous K)
    (F : Finset ℕ) (a : ℕ → ℂ)
    (H : ℝ) (hH : 0 < H) (s : ℝ) :
    (𝓕 (fun v : ℝ =>
        ∑ n ∈ F, a n * K (((n:ℝ)-v)/H))) s =
      ((H:ℂ) * (𝓕 K) (-H*s)) *
        ∑ n ∈ F, a n *
          Complex.exp ((((-2*Real.pi*((n:ℝ)*s):ℝ):ℂ)*Complex.I)) := by
  classical
  have hH0 : H ≠ 0 := hH.ne'
  have hf : Integrable (fun v : ℝ => K ((-v)/H)) := by
    have ha : -(1/H) ≠ 0 := by simp [hH0]
    have hh := hK.comp_mul_left' ha
    convert hh using 1
    ext v
    congr 1
    ring
  have hN (n : ℕ) :
      Integrable (fun v : ℝ => K (((n:ℝ)-v)/H)) := by
    have hh := hf.comp_add_right (-(n:ℝ))
    convert hh using 1
    ext v
    congr 1
    ring
  have hTerm (n : ℕ) :
      Integrable (fun v : ℝ =>
        a n * K (((n:ℝ)-v)/H)) :=
    (hN n).const_mul (a n)
  have hExpTerm (n : ℕ) :
      Integrable (fun v : ℝ =>
        Complex.exp (((-2*Real.pi*(v*s):ℝ):ℂ)*Complex.I) *
          (a n * K (((n:ℝ)-v)/H))) := by
    have hc : Continuous (fun v : ℝ =>
        Complex.exp (((-2*Real.pi*(v*s):ℝ):ℂ)*Complex.I) *
          (a n * K (((n:ℝ)-v)/H))) := by
      fun_prop
    apply (hTerm n).mono hc.aestronglyMeasurable
    filter_upwards with v
    rw [norm_mul]
    have hh := Complex.norm_exp_ofReal_mul_I (-2*Real.pi*(v*s))
    rw [hh, one_mul]
  have hOne (n : ℕ) :
      (∫ v : ℝ,
        Complex.exp (((-2*Real.pi*(v*s):ℝ):ℂ)*Complex.I) *
          (a n*K (((n:ℝ)-v)/H))) =
      a n*(𝓕 (fun v : ℝ => K (((n:ℝ)-v)/H))) s := by
    rw [Real.fourier_eq']
    simp only [Real.inner_apply, smul_eq_mul]
    calc
      _ = ∫ v : ℝ,
        a n * (Complex.exp (((-2*Real.pi*(v*s):ℝ):ℂ)*Complex.I) *
          K (((n:ℝ)-v)/H)) := by
            apply integral_congr_ae
            filter_upwards with v
            ring
      _ = a n * ∫ v : ℝ,
        Complex.exp (((-2*Real.pi*(v*s):ℝ):ℂ)*Complex.I) *
          K (((n:ℝ)-v)/H) := integral_const_mul _ _
  rw [Real.fourier_eq']
  simp only [Real.inner_apply, smul_eq_mul]
  conv_lhs => simp only [Finset.mul_sum]
  rw [integral_finset_sum F (fun n hn => hExpTerm n)]
  calc
    _ = ∑ n ∈ F,
        a n*(𝓕 (fun v : ℝ => K (((n:ℝ)-v)/H))) s := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hOne n
    _ = ∑ n ∈ F,
        a n * (Complex.exp
          ((((-2*Real.pi*((n:ℝ)*s):ℝ):ℂ)*Complex.I)) *
          (H:ℂ) * (𝓕 K) (-H*s)) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [source_linear_collar_fourier_one_term434 K H hH (n:ℝ) s]
    _ = ((H:ℂ) * (𝓕 K) (-H*s)) *
        ∑ n ∈ F, a n *
          Complex.exp ((((-2*Real.pi*((n:ℝ)*s):ℝ):ℂ)*Complex.I)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring
  all_goals rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSparseGramSchur -/

section

/-!
The real nonnegative Schur row bound underlying the source sparse-time
Gram argument.  This is the analytic linear-algebra component, not
the oscillatory estimate for sums of actual `n ^ (I*t)` phases.
-/

namespace Green64Analytic.CorrelationMellin

variable {α : Type*}

/-- Schur's inequality for symmetric finite nonnegative Gram majorants. -/
theorem sparse_gram_quadratic_schur
    (s : Finset α) (K : α → α → ℝ) (z : α → ℝ) (B : ℝ)
    (hK : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ K i j)
    (hSym : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, K i j ≤ B) :
    (∑ i ∈ s, ∑ j ∈ s, K i j * z i * z j) ≤
      B * ∑ i ∈ s, (z i)^2 := by
  classical
  let q : ℝ := ∑ i ∈ s, ∑ j ∈ s, K i j * (z i)^2
  let q' : ℝ := ∑ i ∈ s, ∑ j ∈ s, K i j * (z j)^2
  have hswap : q' = q := by
    dsimp [q, q']
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hSym j hj i hi]
  have hpair (i : α) (hi : i ∈ s) (j : α) (hj : j ∈ s) :
      K i j * z i * z j ≤
        (K i j * (z i)^2 + K i j * (z j)^2) / 2 := by
    have hz := sq_nonneg (z i - z j)
    have hki := hK i hi j hj
    nlinarith [mul_nonneg hki hz]
  have hsum :
      (∑ i ∈ s, ∑ j ∈ s, K i j * z i * z j) ≤ (q + q') / 2 := by
    calc
      _ ≤ ∑ i ∈ s, ∑ j ∈ s,
          (K i j * (z i)^2 + K i j * (z j)^2) / 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.sum_le_sum (fun j hj => hpair i hi j hj)
      _ = (q + q') / 2 := by
        dsimp [q, q']
        simp_rw [add_div, Finset.sum_add_distrib, Finset.sum_div]
  have hq : q ≤ B * ∑ i ∈ s, (z i)^2 := by
    calc
      q = ∑ i ∈ s, (∑ j ∈ s, K i j) * (z i)^2 := by
        dsimp [q]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
      _ ≤ ∑ i ∈ s, B * (z i)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _)
      _ = B * ∑ i ∈ s, (z i)^2 := by rw [Finset.mul_sum]
  have hresult : (∑ i ∈ s, ∑ j ∈ s, K i j * z i * z j) ≤ q := by
    convert hsum using 1
    rw [hswap]
    ring
  exact hresult.trans hq

/-- Complex Gram quadratic form controlled by a symmetric nonnegative
row-majorant. No bounded-cardinality replacement is used. -/
theorem sparse_gram_complex_schur
    (s : Finset α) (G : α → α → ℂ) (z : α → ℂ)
    (K : α → α → ℝ) (B : ℝ)
    (hG : ∀ i ∈ s, ∀ j ∈ s, ‖G i j‖ ≤ K i j)
    (hK : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ K i j)
    (hSym : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, K i j ≤ B) :
    ‖∑ i ∈ s, ∑ j ∈ s, G i j * z i * star (z j)‖ ≤
      B * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ i ∈ s, ‖∑ j ∈ s, G i j * z i * star (z j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖G i j * z i * star (z j)‖ := by
      exact Finset.sum_le_sum (fun i hi => norm_sum_le _ _)
    _ = ∑ i ∈ s, ∑ j ∈ s, ‖G i j‖ * ‖z i‖ * ‖z j‖ := by
      simp [norm_mul, norm_star]
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, K i j * ‖z i‖ * ‖z j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hG i hi j hj) (norm_nonneg _)) (norm_nonneg _)
    _ ≤ B * ∑ i ∈ s, ‖z i‖ ^ 2 :=
      sparse_gram_quadratic_schur s K (fun i => ‖z i‖) B hK hSym hrow

end Green64Analytic.CorrelationMellin

end

/-! ## WeightedSchur -/

section

namespace Green64SourceC6

/-! A fully quantitative Schur step for the actual nonnegative Gram majorant. -/
variable {ι : Type*} [DecidableEq ι]

theorem symm_schur_bound (s : Finset ι) (K : ι → ι → ℝ)
    (b : ι → ℝ) (R : ℝ)
    (hK : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ K i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, K i j) ≤ R) :
    (∑ i ∈ s, ∑ j ∈ s, K i j * (b i * b j)) ≤
    R * (∑ i ∈ s, (b i)^2) := by
  have hterm (i j : ι) (hi : i ∈ s) (hj : j ∈ s) :
      K i j * (b i * b j) ≤
      (K i j * (b i)^2 + K i j * (b j)^2) / 2 := by
    have hAM : b i * b j ≤ ((b i)^2 + (b j)^2)/2 := by
      nlinarith [sq_nonneg (b i - b j)]
    have h := mul_le_mul_of_nonneg_left hAM (hK i hi j hj)
    nlinarith [h]
  have hswap :
      (∑ i ∈ s, ∑ j ∈ s, K i j * (b j)^2) =
      (∑ i ∈ s, ∑ j ∈ s, K i j * (b i)^2) := by
    calc
      _ = ∑ j ∈ s, ∑ i ∈ s, K i j * (b j)^2 := Finset.sum_comm
      _ = ∑ j ∈ s, ∑ i ∈ s, K j i * (b j)^2 := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsym i hi j hj]
      _ = ∑ i ∈ s, ∑ j ∈ s, K i j * (b i)^2 := rfl
  have hpair : (∑ i ∈ s, ∑ j ∈ s, K i j * (b i * b j)) ≤
      (∑ i ∈ s, ∑ j ∈ s, K i j * (b i)^2) := by
    calc
      _ ≤ ∑ i ∈ s, ∑ j ∈ s,
             (K i j * (b i)^2 + K i j * (b j)^2)/2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hterm i j hi hj
      _ = ((∑ i ∈ s, ∑ j ∈ s, K i j * (b i)^2) +
           (∑ i ∈ s, ∑ j ∈ s, K i j * (b j)^2))/2 := by
        simp_rw [add_div]
        simp [Finset.sum_add_distrib, ← Finset.sum_div]
      _ = ∑ i ∈ s, ∑ j ∈ s, K i j * (b i)^2 := by rw [hswap]; ring
  have hrows :
      (∑ i ∈ s, ∑ j ∈ s, K i j * (b i)^2) ≤
      R * (∑ i ∈ s, (b i)^2) := by
    calc
      _ = ∑ i ∈ s, (∑ j ∈ s, K i j) * (b i)^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
      _ ≤ ∑ i ∈ s, R * (b i)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg (b i))
      _ = R * ∑ i ∈ s, (b i)^2 := by rw [Finset.mul_sum]
  exact hpair.trans hrows

end Green64SourceC6

namespace Green64SourceC6

/-- Complex Gram-Schur: no positivity or support regularity of coefficients. -/
theorem complex_gram_schur {ι : Type*} (s : Finset ι)
    (G : ι → ι → ℂ) (K : ι → ι → ℝ)
    (b : ι → ℂ) (R : ℝ)
    (hK : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ K i j)
    (hsym : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i)
    (hdom : ∀ i ∈ s, ∀ j ∈ s, ‖G i j‖ ≤ K i j)
    (hrow : ∀ i ∈ s, (∑ j ∈ s, K i j) ≤ R) :
    ‖∑ i ∈ s, ∑ j ∈ s, G i j * b i * star (b j)‖ ≤
    R * (∑ i ∈ s, ‖b i‖^2) := by
  classical
  have hentry (i j : ι) (hi : i ∈ s) (hj : j ∈ s) :
      ‖G i j * b i * star (b j)‖ ≤ K i j * (‖b i‖ * ‖b j‖) := by
    simp only [norm_mul, norm_star]
    calc
      ‖G i j‖ * ‖b i‖ * ‖b j‖ = ‖G i j‖ * (‖b i‖ * ‖b j‖) := by ring
      _ ≤ K i j * (‖b i‖ * ‖b j‖) :=
        mul_le_mul_of_nonneg_right (hdom i hi j hj)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    ‖∑ i ∈ s, ∑ j ∈ s, G i j * b i * star (b j)‖ ≤
        ∑ i ∈ s, ‖∑ j ∈ s, G i j * b i * star (b j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖G i j * b i * star (b j)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, K i j * (‖b i‖ * ‖b j‖) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hentry i j hi hj
    _ ≤ R * (∑ i ∈ s, ‖b i‖^2) :=
      symm_schur_bound s K (fun i => ‖b i‖) R hK hsym hrow

end Green64SourceC6

namespace Green64SourceC6

/-- First Cauchy–Schwarz stage of the exact finite bilinear sum. -/
theorem bilinear_first_cauchy {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (A : ι → ℂ) (B : κ → ℂ) (E : ι → κ → ℂ) :
    ‖∑ i ∈ s, A i * (∑ j ∈ t, B j * E i j)‖^2 ≤
      (∑ i ∈ s, ‖A i‖^2) *
      (∑ i ∈ s, ‖∑ j ∈ t, B j * E i j‖^2) := by
  classical
  let Z := fun i => ∑ j ∈ t, B j * E i j
  have htri : ‖∑ i ∈ s, A i * Z i‖ ≤
      ∑ i ∈ s, ‖A i‖ * ‖Z i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖A i * Z i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖A i‖ * ‖Z i‖ := by simp [norm_mul]
  have hpos : 0 ≤ ∑ i ∈ s, ‖A i‖ * ‖Z i‖ := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : ‖∑ i ∈ s, A i * Z i‖^2 ≤
      (∑ i ∈ s, ‖A i‖ * ‖Z i‖)^2 := by
    nlinarith [sq_nonneg (‖∑ i ∈ s, A i * Z i‖ -
      ∑ i ∈ s, ‖A i‖ * ‖Z i‖), norm_nonneg (∑ i ∈ s, A i * Z i)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s
      (fun i => ‖A i‖) (fun i => ‖Z i‖)
  exact hsq.trans hCS

end Green64SourceC6

end

/-! ## ChenTheorem.Analysis.AnalyticLogBranch -/

section

open Set Metric Filter
open scoped Topology

namespace Chen
/-- A continuous lift through the complex exponential is holomorphic whenever
its exponential is holomorphic. The local logarithm is taken near one. -/
theorem differentiableAt_of_cexp (g : ℂ → ℂ) (z : ℂ)
    (hc : ContinuousAt g z) (hd : DifferentiableAt ℂ (fun w => Complex.exp (g w)) z) :
    DifferentiableAt ℂ g z := by
  have hsub : ContinuousAt (fun w => (g w - g z).im) z := by fun_prop
  have hnear : ∀ᶠ w in 𝓝 z, -(Real.pi) < (g w - g z).im ∧ (g w - g z).im < Real.pi := by
    simpa only [sub_self, Complex.zero_im] using hsub.eventually
      (Ioo_mem_nhds (by simpa using neg_neg_of_pos Real.pi_pos) (by simpa using Real.pi_pos))
  have he : DifferentiableAt ℂ (fun w => Complex.exp (g w - g z)) z := by
    simpa only [Complex.exp_sub] using hd.div_const (Complex.exp (g z))
  have hl : DifferentiableAt ℂ (fun w => Complex.log (Complex.exp (g w - g z)) + g z) z :=
    (he.clog (by simp [Complex.slitPlane])).add_const _
  apply hl.congr_of_eventuallyEq
  filter_upwards [hnear] with w hw
  rw [Complex.log_exp hw.1 hw.2.le]
  exact (sub_add_cancel _ _).symm
/-- A holomorphic nonvanishing function on a disk admits a holomorphic
logarithm of its ratio to the center value, normalized to vanish at the center. -/
theorem exists_normalized_analyticLog_on_ball (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hne : ∀ z ∈ ball c R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ g c = 0 ∧
      ∀ z ∈ ball c R, Complex.exp (g z) = f z / f c := by
  have hc : c ∈ ball c R := mem_ball_self hR
  haveI : ContractibleSpace (ball c R) := (convex_ball c R).contractibleSpace ⟨c, hc⟩
  have hsimply : IsSimplyConnected (ball c R) := by
    change SimplyConnectedSpace (ball c R)
    infer_instance
  obtain ⟨g, hgc, hge⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsimply isOpen_ball
    ((hf.div_const (f c)).continuousOn) (by
      rintro ⟨z, hz, he⟩
      exact div_ne_zero (hne z hz) (hne c hc) he)
  change ∀ z ∈ ball c R, Complex.exp (g z) = f z / f c at hge
  have hgd : DifferentiableOn ℂ g (ball c R) := by
    intro z hz
    have heq : (fun w => Complex.exp (g w)) =ᶠ[𝓝 z] (fun w => f w / f c) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact hge w hw
    exact (differentiableAt_of_cexp g z
      (hgc.continuousAt (isOpen_ball.mem_nhds hz))
      (((hf z hz).differentiableAt (isOpen_ball.mem_nhds hz)).div_const (f c) |>.congr_of_eventuallyEq heq)).differentiableWithinAt
  refine ⟨fun z => g z - g c, hgd.sub_const _, sub_self _, ?_⟩
  intro z hz
  rw [Complex.exp_sub, hge z hz, hge c hc, div_self (hne c hc), div_one]
/-- The derivative of a normalized logarithm is the logarithmic derivative
of the original function on its domain. -/
theorem deriv_analyticLog_eq_logDeriv {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (c : ℂ) (hc : f c ≠ 0) (he : ∀ z ∈ U, Complex.exp (g z) = f z / f c)
    (z : ℂ) (hz : z ∈ U) : deriv g z = deriv f z / f z := by
  have hgf := (hg z hz).differentiableAt (hU.mem_nhds hz)
  have hff := (hf z hz).differentiableAt (hU.mem_nhds hz)
  have heq : (fun w => Complex.exp (g w)) =ᶠ[𝓝 z] (fun w => f w / f c) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hz, he⟩
  have hd := heq.deriv_eq
  rw [hgf.hasDerivAt.cexp.deriv, (hff.hasDerivAt.div_const (f c)).deriv, he z hz] at hd
  have hz0 : f z ≠ 0 := by
    intro hzero
    have := he z hz
    rw [hzero, zero_div] at this
    exact Complex.exp_ne_zero (g z) this
  field_simp [hc, hz0] at hd ⊢
  linear_combination hd
end Chen

end

