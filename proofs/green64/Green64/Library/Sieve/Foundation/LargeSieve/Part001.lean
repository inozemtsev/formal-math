module

public import Green64.Library.ChenTheorem.LargeSieve.Gallagher
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Green64.Library.Sieve.Foundation.Analysis.Part001
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Sieve / Foundation / LargeSieve / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.LargeSieve.Additive -/

section

/-
The additive large sieve (inequality (4) of Chen's paper):

  `∑_{q ≤ X} ∑_{1 ≤ b ≤ q, (b,q) = 1} |S(b/q)|² ≤ (X² + πN) ∑ |aₙ|²`

for `S(α) = ∑_{n=M+1}^{M+N} aₙ e(nα)`, together with its trigonometric
Parseval inputs. The proof follows the paper: Gallagher's centered inequality
(`LargeSieve/Gallagher.lean`) applied to arcs of radius `δ/2 = 1/(2X²)` about
the Farey points, whose sum of integrals is bounded by one full period using
disjointness (after lifting the arcs into a common window `(ρ, ρ+1)` chosen in
the gap between the largest and smallest point), and the AM–GM bound
`2‖T‖‖T'‖ ≤ λ‖T‖² + λ⁻¹‖T'‖` with `λ = πN` on the cross term.

The coefficient shift `n ↦ n - (M + ⌈N/2⌉)` centers the frequencies in
`[-N/2, N/2]`, giving `∫₀¹ |T'|² ≤ π²N² ∑|aₙ|²`.
-/

open Set MeasureTheory intervalIntegral Finset
open scoped RealInnerProductSpace ComplexConjugate

namespace Chen.LargeSieve

/-! ### The exponential `α ↦ exp (2πiα)` -/

/-- The complex exponential `e(α) = exp (2πiα)`. -/
noncomputable def fexp (α : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * α)

@[simp] lemma fexp_zero : fexp 0 = 1 := by simp [fexp]

lemma fexp_add (α β : ℝ) : fexp (α + β) = fexp α * fexp β := by
  simp only [fexp]
  push_cast
  rw [mul_add, Complex.exp_add]

@[simp] lemma fexp_norm (α : ℝ) : ‖fexp α‖ = 1 := by
  rw [fexp, show 2 * Real.pi * Complex.I * α = ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

lemma fexp_one_eq_one : fexp 1 = 1 := by
  rw [fexp, show 2 * Real.pi * Complex.I * (1 : ℝ) = 2 * Real.pi * Complex.I by simp]
  exact Complex.exp_eq_one_iff.mpr ⟨1, by simp⟩

lemma fexp_periodic : Function.Periodic fexp 1 := fun α => by
  rw [fexp_add, fexp_one_eq_one, mul_one]

lemma fexp_int_one (k : ℤ) : fexp k = 1 := by
  rw [fexp]
  exact Complex.exp_eq_one_iff.mpr ⟨k, by push_cast; ring⟩

lemma star_fexp (β : ℝ) : star (fexp β) = fexp (-β) := by
  have h1 : fexp β * fexp (-β) = 1 := by rw [← fexp_add, add_neg_cancel, fexp_zero]
  have h2 : fexp β * star (fexp β) = 1 := by
    rw [show star (fexp β) = conj (fexp β) from rfl, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, fexp_norm, one_pow, Complex.ofReal_one]
  rw [← inv_eq_of_mul_eq_one_right h1, ← inv_eq_of_mul_eq_one_right h2]

lemma fexp_periodic_mul (k : ℤ) : Function.Periodic (fun α => fexp (k * α)) 1 := by
  intro α
  show fexp ((k : ℝ) * (α + 1)) = fexp ((k : ℝ) * α)
  have h : (k : ℝ) * (α + 1) = k * α + k := by ring
  rw [h, fexp_add, fexp_int_one, mul_one]

lemma fexp_mul_continuous (c : ℝ) : Continuous fun α => fexp (c * α) := by
  have h : Continuous fun α : ℝ => 2 * Real.pi * Complex.I * ((c : ℂ) * α) := by fun_prop
  have h2 := h.cexp
  rw [show (fun α : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((c : ℂ) * α))) =
      (fun α => fexp (c * α)) from ?_] at h2
  · exact h2
  · funext α
    rw [fexp]
    push_cast
    ring_nf

lemma hasDerivAt_fexp (c : ℝ) (α : ℝ) :
    HasDerivAt (fun α => fexp (c * α)) (fexp (c * α) * (2 * Real.pi * Complex.I * c)) α := by
  have h1 : HasDerivAt (fun α : ℝ => 2 * Real.pi * Complex.I * ((c : ℂ) * α))
      (2 * Real.pi * Complex.I * c) α := by
    have h2 : (fun α : ℝ => 2 * Real.pi * Complex.I * ((c : ℂ) * α)) =
        fun α : ℝ => (2 * Real.pi * Complex.I * c) * α := by
      funext β
      ring_nf
    rw [h2]
    have hbase : HasDerivAt (fun α : ℝ => ((α : ℝ) : ℂ)) (1 : ℂ) α := by
      change HasDerivAt (⇑Complex.ofRealCLM) (Complex.ofRealCLM 1) α
      exact Complex.ofRealCLM.hasDerivAt
    simpa using hbase.const_mul (2 * Real.pi * Complex.I * c)
  have h3 := h1.cexp
  convert h3 using 1
  · funext β
    rw [fexp]
    push_cast
    ring
  · rw [fexp]
    push_cast
    ring

/-! ### The kernel integral -/

/-- `∫₀¹ e(kα) dα = δ_{k,0}` for `k : ℤ`. -/
lemma integral_fexp_int_mul (k : ℤ) :
    ∫ α in (0:ℝ)..1, fexp ((k : ℝ) * α) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk, fexp]
  · have hk' : (2 * Real.pi * Complex.I * k) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero, hk]
    have hanti : ∀ α : ℝ, HasDerivAt (fun α => fexp ((k : ℝ) * α) / (2 * Real.pi * Complex.I * k))
        (fexp ((k : ℝ) * α)) α := by
      intro α
      have hcast : (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ)) = 2 * Real.pi * Complex.I * k := by
        push_cast
        ring
      have h := (hasDerivAt_fexp ((k : ℝ)) α).div_const (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ))
      rw [hcast, mul_div_cancel_right₀ _ hk'] at h
      exact h
    have hcont : Continuous fun α : ℝ => fexp ((k : ℝ) * α) / (2 * Real.pi * Complex.I * k) :=
      (fexp_mul_continuous _).div_const _
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1)
      (fun α _ => hanti α) ((fexp_mul_continuous _).intervalIntegrable _ _)
    rw [hftc]
    have he1 : fexp ((k : ℝ) * (1 : ℝ)) = 1 := by
      rw [mul_one]
      exact fexp_int_one k
    rw [he1, mul_zero, fexp_zero, if_neg hk, sub_self]

/-! ### Trigonometric polynomials and Parseval -/

/-- The trigonometric sum `S(α) = ∑_{n ∈ s} aₙ e(nα)`. -/
noncomputable def trigSum (a : ℕ → ℂ) (s : Finset ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ s, a n * fexp (n * α)

lemma hasDerivAt_trigTerm (a : ℕ → ℂ) (n : ℕ) (α : ℝ) :
    HasDerivAt (fun α => a n * fexp ((n : ℝ) * α))
      (a n * (fexp ((n : ℝ) * α) * (2 * Real.pi * Complex.I * n))) α := by
  simpa using (hasDerivAt_fexp ((n : ℝ)) α).const_mul (a n)

lemma trigSum_hasDerivAt (a : ℕ → ℂ) (s : Finset ℕ) (α : ℝ) :
    HasDerivAt (trigSum a s)
      (∑ n ∈ s, a n * (fexp ((n : ℝ) * α) * (2 * Real.pi * Complex.I * n))) α := by
  change HasDerivAt (fun β => ∑ n ∈ s, a n * fexp ((n : ℝ) * β)) _ α
  apply HasDerivAt.fun_sum
  intro n hn
  exact hasDerivAt_trigTerm a n α

lemma trigSum_continuous (a : ℕ → ℂ) (s : Finset ℕ) : Continuous (trigSum a s) := by
  apply continuous_finsetSum
  intro n _
  exact (fexp_mul_continuous _).const_mul _

lemma trigSum_deriv_continuous (a : ℕ → ℂ) (s : Finset ℕ) :
    Continuous fun α => ∑ n ∈ s, a n * (fexp ((n : ℝ) * α) * (2 * Real.pi * Complex.I * n)) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul ((fexp_mul_continuous _).mul continuous_const)

/-- The product expansion: `S·star S = ∑_{n,m} aₙ (star aₘ) e((n-m)α)`. -/
lemma trigSum_mul_star (a : ℕ → ℂ) (s : Finset ℕ) (α : ℝ) :
    (trigSum a s α) * star (trigSum a s α) =
      ∑ n ∈ s, ∑ m ∈ s, (a n * star (a m)) * fexp (((n : ℤ) - m : ℝ) * α) := by
  rw [trigSum, star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [star_mul, star_fexp]
  calc (a n * fexp ((n : ℝ) * α)) * (fexp (-((m : ℝ) * α)) * star (a m))
      = (a n * star (a m)) * (fexp ((n : ℝ) * α) * fexp (-((m : ℝ) * α))) := by ring_nf
    _ = (a n * star (a m)) * fexp (((n : ℤ) - m : ℝ) * α) := by
        rw [← fexp_add]
        congr 1
        push_cast
        ring_nf

/-- Parseval for trigonometric polynomials: `∫₀¹ S·star S = ∑ aₙ (star aₙ)`. -/
lemma integral_trigSum_mul_star (a : ℕ → ℂ) (s : Finset ℕ) :
    ∫ α in (0:ℝ)..1, (trigSum a s α) * star (trigSum a s α) =
      ∑ n ∈ s, a n * star (a n) := by
  have hterm : ∀ n m : ℕ, IntervalIntegrable
      (fun α => (a n * star (a m)) * fexp (((n : ℤ) - m : ℝ) * α)) MeasureTheory.volume 0 1 := by
    intro n m
    exact ((fexp_mul_continuous _).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun α _ => trigSum_mul_star a s α)]
  rw [intervalIntegral.integral_finsetSum (fun n _ =>
    (continuous_finsetSum _ fun m _ => ((fexp_mul_continuous _).const_mul _)).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_finsetSum fun m _ => hterm n m]
  rw [Finset.sum_eq_single n]
  · rw [intervalIntegral.integral_const_mul]
    rw [show (↑(n : ℤ) - ↑n : ℝ) = 0 by norm_num]
    simp
  · intro m _ hm
    rw [intervalIntegral.integral_const_mul]
    have hmn : (n : ℤ) - m ≠ 0 := by omega
    rw [show ((n : ℤ) - m : ℝ) = (((n : ℤ) - m : ℤ) : ℝ) by norm_num,
      integral_fexp_int_mul, if_neg hmn]
    simp
  · intro hn'
    exact (hn' hn).elim

/-- Parseval (real form): `∫₀¹ ‖S‖² = ∑ ‖aₙ‖²`. -/
lemma integral_trigSum_norm_sq (a : ℕ → ℂ) (s : Finset ℕ) :
    ∫ α in (0:ℝ)..1, ‖trigSum a s α‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have h1 : ∀ α : ℝ, ‖trigSum a s α‖ ^ 2 = ((trigSum a s α) * star (trigSum a s α)).re := by
    intro α
    rw [show star (trigSum a s α) = conj (trigSum a s α) from rfl,
      ← Complex.normSq_eq_norm_sq, Complex.mul_conj, Complex.ofReal_re]
  have hint : IntervalIntegrable (fun α => (trigSum a s α) * star (trigSum a s α))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.mul _ (continuous_star.comp _)
    all_goals
      apply continuous_finsetSum
      intro n _
      exact (fexp_mul_continuous _).const_mul _
  have h2 : (∑ n ∈ s, a n * star (a n)) = ((∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [show star (a n) = conj (a n) from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h3 : ∫ α in (0:ℝ)..1, ((trigSum a s α) * star (trigSum a s α)).re =
      (∫ α in (0:ℝ)..1, (trigSum a s α) * star (trigSum a s α)).re := by
    exact Complex.reCLM.intervalIntegral_comp_comm hint
  rw [intervalIntegral.integral_congr (fun α _ => h1 α), h3, integral_trigSum_mul_star, h2,
    Complex.ofReal_re]

/-! ### Arc machinery: separated arcs in a period window -/

/-- The arcs of radius `δ/2` about pairwise `δ`-separated centers, all contained
in the window `Ioc ρ (ρ+1)`, have total `g`-mass at most that of one period. -/
lemma sum_integral_arcs_le {ι : Type*} {s : Finset ι} {c : ι → ℝ} {δ : ℝ} (_hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |c i - c j|)
    {ρ : ℝ} (harc : ∀ i ∈ s, ρ + δ / 2 ≤ c i ∧ c i ≤ ρ + 1 - δ / 2)
    {g : ℝ → ℝ} (hg : Continuous g) (hgn : ∀ x, 0 ≤ g x) (hper : Function.Periodic g 1) :
    ∑ i ∈ s, ∫ t in Set.Ioc (c i - δ / 2) (c i + δ / 2), g t ≤ ∫ t in Set.Ioc 0 1, g t := by
  classical
  set W := Set.Ioc ρ (ρ + 1) with hW
  have hJW : ∀ i ∈ s, Set.Ioc (c i - δ / 2) (c i + δ / 2) ⊆ W := by
    intro i hi
    apply Set.Ioc_subset_Ioc
    · linarith [(harc i hi).1]
    · linarith [(harc i hi).2]
  have hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Set.Ioc (c i - δ / 2) (c i + δ / 2)) (Set.Ioc (c j - δ / 2) (c j + δ / 2)) := by
    intro i hi j hj hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases le_total (c i) (c j) with hle | hle
    · have h := hsep i hi j hj hij
      rw [abs_of_nonpos (sub_nonpos.mpr hle)] at h
      linarith [hxi.2, hxj.1]
    · have h := hsep i hi j hj hij
      rw [abs_of_nonneg (sub_nonneg.mpr hle)] at h
      linarith [hxi.1, hxj.2]
  have hInt : ∀ i ∈ s, ∫ t in Set.Ioc (c i - δ / 2) (c i + δ / 2), g t =
      ∫ t in W, (Set.Ioc (c i - δ / 2) (c i + δ / 2)).indicator g t := by
    intro i hi
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_self_of_subset_right (hJW i hi)]
  have hsumint : IntegrableOn (fun x => ∑ i ∈ s,
      (Set.Ioc (c i - δ / 2) (c i + δ / 2)).indicator g x) W := by
    apply MeasureTheory.integrable_finsetSum
    intro i _
    exact (hg.integrableOn_Ioc.indicator measurableSet_Ioc)
  have hpoint : ∀ x ∈ W, (∑ i ∈ s, (Set.Ioc (c i - δ / 2) (c i + δ / 2)).indicator g x) ≤ g x := by
    intro x hx
    by_cases h : ∃ i ∈ s, x ∈ Set.Ioc (c i - δ / 2) (c i + δ / 2)
    · obtain ⟨i, hi, hxi⟩ := h
      rw [Finset.sum_eq_single i
        (fun j hj hjne => Set.indicator_of_notMem
          (Set.disjoint_left.mp (hdisj i hi j hj hjne.symm) hxi) g)
        (fun hi' => (hi' hi).elim)]
      exact (Set.indicator_of_mem hxi g).le
    · push Not at h
      rw [Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (h i hi) g]
      exact hgn x
  calc ∑ i ∈ s, ∫ t in Set.Ioc (c i - δ / 2) (c i + δ / 2), g t
      = ∑ i ∈ s, ∫ t in W, (Set.Ioc (c i - δ / 2) (c i + δ / 2)).indicator g t :=
        Finset.sum_congr rfl fun i hi => hInt i hi
    _ = ∫ t in W, ∑ i ∈ s, (Set.Ioc (c i - δ / 2) (c i + δ / 2)).indicator g t := by
        exact (MeasureTheory.integral_finsetSum s
          (fun i _ => (hg.integrableOn_Ioc.indicator measurableSet_Ioc))).symm
    _ ≤ ∫ t in W, g t :=
        MeasureTheory.setIntegral_mono_on hsumint hg.integrableOn_Ioc measurableSet_Ioc hpoint
    _ = ∫ t in Set.Ioc 0 1, g t := by
        rw [← intervalIntegral.integral_of_le (by linarith : ρ ≤ ρ + 1),
          hper.intervalIntegral_add_eq ρ 0, zero_add,
          intervalIntegral.integral_of_le (zero_le_one)]

/-- The window shift: for a `1`-periodic `g`, the integral over an arc of radius
`δ/2` equals that over the arc shifted by `1`. -/
lemma integral_arc_shift {g : ℝ → ℝ} (hper : Function.Periodic g 1) (y δ : ℝ)
    (hδ : 0 ≤ δ) :
    ∫ t in Set.Ioc (y - δ / 2) (y + δ / 2), g t =
      ∫ t in Set.Ioc (y + 1 - δ / 2) (y + 1 + δ / 2), g t := by
  rw [← intervalIntegral.integral_of_le (by linarith : y - δ / 2 ≤ y + δ / 2),
    ← intervalIntegral.integral_of_le (by linarith : y + 1 - δ / 2 ≤ y + 1 + δ / 2)]
  calc
    ∫ x in (y - δ / 2)..(y + δ / 2), g x =
        ∫ x in (y - δ / 2)..(y + δ / 2), g (x + 1) := by
          apply intervalIntegral.integral_congr
          intro x _
          exact (hper x).symm
    _ = ∫ x in (y - δ / 2 + 1)..(y + δ / 2 + 1), g x :=
      intervalIntegral.integral_comp_add_right g 1
    _ = ∫ x in (y + 1 - δ / 2)..(y + 1 + δ / 2), g x := by
      congr 1 <;> ring

/-- If a finite set of points of `[0,1)` is pairwise at distance in `[δ, 1-δ]`,
then all arcs of radius `δ/2` about the points shifted by `1` fit inside a
common window `(ρ, ρ+1)` (the `ρ` is the midpoint of the wrap-around gap). -/
lemma exists_window {s : Finset ℝ} (hs : s.Nonempty) {δ : ℝ} (_hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y| ∧ |x - y| ≤ 1 - δ) :
    ∃ ρ : ℝ, ∀ x ∈ s, ρ + δ / 2 ≤ x + 1 ∧ x + 1 ≤ ρ + 1 - δ / 2 := by
  classical
  set ymin := s.min' hs
  set ymax := s.max' hs
  have hgap : ymax - ymin ≤ 1 - δ := by
    rcases eq_or_ne ymin ymax with heq | hne
    · linarith [heq, hδ1]
    · have h1 := hsep ymin (s.min'_mem hs) ymax (s.max'_mem hs) hne
      have h2 : |ymax - ymin| = ymax - ymin := abs_of_nonneg (by
        have := s.min'_le ymax (s.max'_mem hs); linarith)
      rw [abs_sub_comm, h2] at h1
      exact h1.2
  refine ⟨(ymax + ymin + 1) / 2, fun x hx => ?_⟩
  have hmin := s.min'_le x hx
  have hmax := s.le_max' x hx
  constructor <;> linarith

/-! ### Farey separation -/

/-- Reduced fractions are unique: coprime `bᵢ/qᵢ` with equal values coincide. -/
lemma farey_inj {q₁ q₂ b₁ b₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hb₁ : b₁.Coprime q₁) (hb₂ : b₂.Coprime q₂)
    (h : (b₁ : ℝ) / q₁ = (b₂ : ℝ) / q₂) :
    q₁ = q₂ ∧ b₁ = b₂ := by
  have hcross : (b₁ : ℤ) * q₂ = (b₂ : ℤ) * q₁ := by
    have hq₁' : (q₁ : ℝ) ≠ 0 := by positivity
    have hq₂' : (q₂ : ℝ) ≠ 0 := by positivity
    have h1 : (b₁ : ℝ) * q₂ = (b₂ : ℝ) * q₁ := by
      field_simp at h
      linarith [h]
    exact_mod_cast h1
  have hq1q2 : q₁ ∣ q₂ := by
    have : q₁ ∣ b₁ * q₂ := by
      have h2 : (b₂ : ℤ) * q₁ = (b₁ : ℤ) * q₂ := hcross.symm
      have h3 : (b₂ : ℕ) * q₁ = b₁ * q₂ := by exact_mod_cast h2
      rw [← h3]
      exact dvd_mul_left q₁ b₂
    exact hb₁.symm.dvd_of_dvd_mul_left this
  have hq2q1 : q₂ ∣ q₁ := by
    have : q₂ ∣ b₂ * q₁ := by
      have h3 : (b₁ : ℕ) * q₂ = b₂ * q₁ := by exact_mod_cast hcross
      rw [← h3]
      exact dvd_mul_left q₂ b₁
    exact hb₂.symm.dvd_of_dvd_mul_left this
  have hqq : q₁ = q₂ := Nat.dvd_antisymm hq1q2 hq2q1
  refine ⟨hqq, ?_⟩
  have h3 : (b₁ : ℕ) * q₂ = b₂ * q₁ := by exact_mod_cast hcross
  rw [hqq] at h3
  exact Nat.eq_of_mul_eq_mul_right hq₂ h3

/-- Farey fractions of order `X` are `1/X²`-separated, also across `0`. -/
lemma farey_sep {X : ℕ} (hX : 1 ≤ X) {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁ ∧ q₁ ≤ X)
    (hq₂ : 1 ≤ q₂ ∧ q₂ ≤ X) {b₁ b₂ : ℕ} (_hb₁ : b₁.Coprime q₁) (_hb₂ : b₂.Coprime q₂)
    (hb₁' : b₁ < q₁) (hb₂' : b₂ < q₂)
    (hne : (b₁ : ℝ) / q₁ ≠ (b₂ : ℝ) / q₂) :
    1 / (X : ℝ) ^ 2 ≤ |(b₁ : ℝ) / q₁ - (b₂ : ℝ) / q₂| ∧
      |(b₁ : ℝ) / q₁ - (b₂ : ℝ) / q₂| ≤ 1 - 1 / (X : ℝ) ^ 2 := by
  have hq₁0 : (0:ℝ) < q₁ := by exact_mod_cast hq₁.1
  have hq₂0 : (0:ℝ) < q₂ := by exact_mod_cast hq₂.1
  have hqprod : (0:ℝ) < (q₁ : ℝ) * q₂ := mul_pos hq₁0 hq₂0
  have hcross : (b₁ : ℝ) / q₁ - (b₂ : ℝ) / q₂ =
      ((b₁ : ℝ) * q₂ - (b₂ : ℝ) * q₁) / ((q₁ : ℝ) * q₂) := by field_simp
  have hne_int : (b₁ : ℤ) * q₂ - (b₂ : ℤ) * q₁ ≠ 0 := by
    intro h
    apply hne
    have h1 : ((b₁ : ℝ) * q₂ - (b₂ : ℝ) * q₁) = 0 := by exact_mod_cast h
    have h2 : (b₁ : ℝ) / q₁ - (b₂ : ℝ) / q₂ = 0 := by
      rw [hcross, h1, zero_div]
    linarith
  have habs1 : (1:ℝ) ≤ |(b₁ : ℝ) * q₂ - (b₂ : ℝ) * q₁| := by
    have h1 : (1:ℤ) ≤ |(b₁ : ℤ) * q₂ - (b₂ : ℤ) * q₁| := by
      exact Int.one_le_abs hne_int
    exact_mod_cast h1
  have hub_int : |(b₁ : ℤ) * q₂ - (b₂ : ℤ) * q₁| ≤ (q₁ : ℤ) * q₂ - 1 := by
    have hb1nat : b₁ * q₂ < q₁ * q₂ :=
      Nat.mul_lt_mul_of_pos_right hb₁' (by omega)
    have hb2nat : b₂ * q₁ < q₁ * q₂ := by
      simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hb₂' (by omega : 0 < q₁)
    have hb1 : (b₁ : ℤ) * q₂ < (q₁ : ℤ) * q₂ := by exact_mod_cast hb1nat
    have hb2 : (b₂ : ℤ) * q₁ < (q₁ : ℤ) * q₂ := by exact_mod_cast hb2nat
    have hpos1 : (0 : ℤ) ≤ (b₁ : ℤ) * q₂ := by positivity
    have hpos2 : (0 : ℤ) ≤ (b₂ : ℤ) * q₁ := by positivity
    rw [abs_le]
    constructor <;> omega
  have hub : |(b₁ : ℝ) * q₂ - (b₂ : ℝ) * q₁| ≤ (q₁ : ℝ) * q₂ - 1 := by
    exact_mod_cast hub_int
  have hqX : (q₁ : ℝ) * q₂ ≤ (X : ℝ) ^ 2 := by
    rw [sq]
    exact mul_le_mul (by exact_mod_cast hq₁.2) (by exact_mod_cast hq₂.2)
      (by positivity) (by positivity)
  rw [hcross, abs_div, abs_of_pos hqprod]
  constructor
  · rw [le_div_iff₀ hqprod]
    calc 1 / (X : ℝ) ^ 2 * ((q₁ : ℝ) * q₂) ≤ 1 / (X : ℝ) ^ 2 * (X : ℝ) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hqX (by positivity)
      _ = 1 := by field_simp
      _ ≤ |(b₁ : ℝ) * q₂ - (b₂ : ℝ) * q₁| := habs1
  · rw [div_le_iff₀ hqprod]
    calc |(b₁ : ℝ) * q₂ - (b₂ : ℝ) * q₁| ≤ (q₁ : ℝ) * q₂ - 1 := hub
      _ ≤ (1 - 1 / (X : ℝ) ^ 2) * ((q₁ : ℝ) * q₂) := by
          have h3 : (q₁ : ℝ) * q₂ / (X : ℝ) ^ 2 ≤ 1 := by
            rw [div_le_one (by positivity : (0:ℝ) < (X:ℝ)^2)]
            exact hqX
          have h4 : (1 - 1 / (X : ℝ) ^ 2) * ((q₁ : ℝ) * q₂) =
              (q₁ : ℝ) * q₂ - (q₁ : ℝ) * q₂ / (X : ℝ) ^ 2 := by
            field_simp
          rw [h4]
          linarith [h3, hqprod]

/-! ### The additive large sieve (inequality (4) of the paper) -/

lemma trigSum_periodic (a : ℕ → ℂ) (s : Finset ℕ) : Function.Periodic (trigSum a s) 1 := by
  intro α
  rw [trigSum, trigSum]
  apply Finset.sum_congr rfl
  intro n _
  have h : (n : ℝ) * (α + 1) = n * α + n := by ring
  rw [h, fexp_add]
  have hn : fexp (n : ℝ) = 1 := by
    simpa using fexp_int_one (n : ℤ)
  rw [hn, mul_one]

/-- **The additive large sieve** (inequality (4) of Chen's paper):
`∑_{q ≤ X} ∑_{(b,q)=1} |S(b/q)|² ≤ (X² + πN) ∑|aₙ|²`. -/
theorem additive_large_sieve (X M N : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 X, ∑ b ∈ (Finset.range q).filter (·.Coprime q),
        ‖trigSum a (Finset.Ioc M (M + N)) ((b : ℝ) / q)‖ ^ 2
      ≤ ((X : ℝ) ^ 2 + Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  set s := Finset.Ioc M (M + N)
  set Z := ∑ n ∈ s, ‖a n‖ ^ 2
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun n _ => by positivity
  rcases eq_zero_or_pos X with rfl | hX
  · simp only [Finset.Icc_eq_empty (by omega : ¬1 ≤ 0), Finset.sum_empty]
    positivity
  rcases eq_zero_or_pos N with rfl | hN
  · have : s = ∅ := by simp [s]
    simp [this, Z, trigSum]
  -- The shifted sum and its derivative.
  set c := M + (N + 1) / 2 with hc_def
  set S := trigSum a s with hS_def
  set b : ℕ → ℂ := fun n => (2 * Real.pi * Complex.I * ((n : ℤ) - c)) * a n
    with hb_def
  set U := trigSum b s with hU_def
  set g : ℝ → ℂ := fun α => fexp (-(c : ℝ) * α) with hg_def
  set T : ℝ → ℂ := fun α =>
    ∑ n ∈ s, a n * fexp ((((n : ℤ) - c : ℤ) : ℝ) * α) with hT_def
  set T' : ℝ → ℂ := fun α =>
    ∑ n ∈ s, a n * (fexp ((((n : ℤ) - c : ℤ) : ℝ) * α) *
      (2 * Real.pi * Complex.I * (((n : ℤ) - c : ℤ) : ℝ))) with hT'_def
  have hTderiv : ∀ α, HasDerivAt T (T' α) α := by
    intro α
    rw [hT_def, hT'_def]
    apply HasDerivAt.fun_sum
    intro n hn
    simpa using
      (hasDerivAt_fexp ((((n : ℤ) - c : ℤ) : ℝ)) α).const_mul (a n)
  have hT'cont : Continuous T' := by
    rw [hT'_def]
    apply continuous_finsetSum
    intro n hn
    exact continuous_const.mul ((fexp_mul_continuous _).mul continuous_const)
  have hTcont : Continuous T := by
    rw [hT_def]
    apply continuous_finsetSum
    intro n hn
    exact (fexp_mul_continuous _).const_mul _
  have hTfactor : ∀ α, T α = g α * S α := by
    intro α
    rw [hT_def, hg_def, hS_def, trigSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hphase : fexp ((((n : ℤ) - c : ℤ) : ℝ) * α) =
        fexp (-(c : ℝ) * α) * fexp ((n : ℝ) * α) := by
      rw [← fexp_add]
      congr 1
      push_cast
      ring
    rw [hphase]
    ring
  have hT'factor : ∀ α, T' α = g α * U α := by
    intro α
    rw [hT'_def, hg_def, hU_def, trigSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hphase : fexp ((((n : ℤ) - c : ℤ) : ℝ) * α) =
        fexp (-(c : ℝ) * α) * fexp ((n : ℝ) * α) := by
      rw [← fexp_add]
      congr 1
      push_cast
      ring
    rw [hb_def, hphase]
    push_cast
    ring
  have hTper : Function.Periodic T 1 := by
    intro α
    change (∑ n ∈ s, a n * fexp ((((n : ℤ) - c : ℤ) : ℝ) * (α + 1))) =
      ∑ n ∈ s, a n * fexp ((((n : ℤ) - c : ℤ) : ℝ) * α)
    apply Finset.sum_congr rfl
    intro n hn
    exact congrArg (fun z => a n * z) (fexp_periodic_mul ((n : ℤ) - c) α)
  have hT'per : Function.Periodic T' 1 := by
    intro α
    change (∑ n ∈ s, a n * (fexp ((((n : ℤ) - c : ℤ) : ℝ) * (α + 1)) *
      (2 * Real.pi * Complex.I * (((n : ℤ) - c : ℤ) : ℝ)))) =
      ∑ n ∈ s, a n * (fexp ((((n : ℤ) - c : ℤ) : ℝ) * α) *
        (2 * Real.pi * Complex.I * (((n : ℤ) - c : ℤ) : ℝ)))
    apply Finset.sum_congr rfl
    intro n hn
    exact congrArg (fun z => a n * (z *
      (2 * Real.pi * Complex.I * (((n : ℤ) - c : ℤ) : ℝ))))
      (fexp_periodic_mul ((n : ℤ) - c) α)
  have hTnorm : ∀ α, ‖T α‖ = ‖S α‖ := by
    intro α
    rw [hTfactor, norm_mul, hg_def, fexp_norm, one_mul]
  have hT'norm : ∀ α, ‖T' α‖ = ‖U α‖ := by
    intro α
    rw [hT'factor, norm_mul, hg_def, fexp_norm, one_mul]
  have hg1per : Function.Periodic (fun α => ‖T α‖ ^ 2) 1 := by
    intro α
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hTper α)
  have hg2per : Function.Periodic (fun α => ‖T α‖ * ‖T' α‖) 1 := by
    intro α
    exact congrArg₂ (fun z w : ℂ => ‖z‖ * ‖w‖) (hTper α) (hT'per α)
  -- Parseval for `S` and `U`.
  have hPS : ∫ α in (0:ℝ)..1, ‖S α‖ ^ 2 = Z := integral_trigSum_norm_sq a s
  have hPU : ∫ α in (0:ℝ)..1, ‖U α‖ ^ 2 ≤ Real.pi ^ 2 * N ^ 2 * Z := by
    rw [integral_trigSum_norm_sq]
    have hterm : ∀ n ∈ s, ‖b n‖ ^ 2 ≤ (Real.pi * N) ^ 2 * ‖a n‖ ^ 2 := by
      intro n hn
      have hnk : |((n : ℤ) - c : ℝ)| ≤ N / 2 := by
        rw [Finset.mem_Ioc] at hn
        have hupper_int : (2 : ℤ) * ((n : ℤ) - c) ≤ N := by
          omega
        have hlower_int : -(N : ℤ) ≤ 2 * ((n : ℤ) - c) := by
          omega
        have h1 : (((n : ℤ) - c : ℤ) : ℝ) ≤ N / 2 := by
          have hupper_real : (2 : ℝ) * (((n : ℤ) - c : ℤ) : ℝ) ≤ N := by
            exact_mod_cast hupper_int
          linarith
        have h2 : -(N / 2 : ℝ) ≤ (((n : ℤ) - c : ℤ) : ℝ) := by
          have hlower_real : -(N : ℝ) ≤ 2 * (((n : ℤ) - c : ℤ) : ℝ) := by
            exact_mod_cast hlower_int
          linarith
        push_cast at h1 h2
        rw [abs_le]
        exact ⟨h2, h1⟩
      have hbnorm : ‖b n‖ = 2 * Real.pi * |((n : ℤ) - c : ℝ)| * ‖a n‖ := by
        rw [hb_def, norm_mul, norm_mul]
        have h2pi : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
          rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        have h2piI : ‖(2 * Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
          rw [norm_mul, h2pi, Complex.norm_I, mul_one]
        have hnc : ‖((n : ℤ) : ℂ) - (c : ℂ)‖ =
            |((n : ℤ) : ℝ) - (c : ℝ)| := by
          calc
            ‖((n : ℤ) : ℂ) - (c : ℂ)‖ =
                ‖((((n : ℤ) - (c : ℤ) : ℤ)) : ℂ)‖ := by
                  congr 2
                  push_cast
                  rfl
            _ = |((((n : ℤ) - (c : ℤ) : ℤ)) : ℝ)| :=
              Complex.norm_intCast _
            _ = |((n : ℤ) : ℝ) - (c : ℝ)| := by
              push_cast
              rfl
        rw [h2piI, hnc]
      rw [hbnorm]
      have h1 : (2 * Real.pi * |((n : ℤ) - c : ℝ)| * ‖a n‖) ^ 2 ≤
          (Real.pi * N) ^ 2 * ‖a n‖ ^ 2 := by
        have h2 : 2 * Real.pi * |((n : ℤ) - c : ℝ)| ≤ Real.pi * N := by
          nlinarith [mul_le_mul_of_nonneg_left hnk Real.pi_pos.le]
        calc (2 * Real.pi * |((n : ℤ) - c : ℝ)| * ‖a n‖) ^ 2
            = (2 * Real.pi * |((n : ℤ) - c : ℝ)|) ^ 2 * ‖a n‖ ^ 2 := by ring
          _ ≤ (Real.pi * N) ^ 2 * ‖a n‖ ^ 2 := by
              have hsquare : (2 * Real.pi * |((n : ℤ) - c : ℝ)|) ^ 2 ≤
                  (Real.pi * N) ^ 2 :=
                (sq_le_sq₀ (by positivity) (by positivity)).2 h2
              exact mul_le_mul_of_nonneg_right hsquare (sq_nonneg ‖a n‖)
      exact h1
    calc ∑ n ∈ s, ‖b n‖ ^ 2 ≤ ∑ n ∈ s, (Real.pi * N) ^ 2 * ‖a n‖ ^ 2 :=
        Finset.sum_le_sum hterm
      _ = (Real.pi * N) ^ 2 * Z := by rw [Finset.mul_sum]
      _ = Real.pi ^ 2 * N ^ 2 * Z := by ring
  -- The Farey points and their separation.
  set points := (Finset.Icc 1 X).sigma fun q => (Finset.range q).filter (·.Coprime q)
    with hpoints_def
  set y : (Σ q : ℕ, ℕ) → ℝ := fun p => (p.2 : ℝ) / (p.1 : ℝ)
  set δ := 1 / (X : ℝ) ^ 2 with hδ_def
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ_def, div_le_one (by positivity : (0:ℝ) < (X:ℝ)^2)]
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
    nlinarith
  have hmem : (⟨1, 0⟩ : Σ q : ℕ, ℕ) ∈ points := by
    rw [Finset.mem_sigma]
    have hX1 : 1 ≤ X := by omega
    exact ⟨Finset.mem_Icc.mpr ⟨le_rfl, hX1⟩, by simp⟩
  have hpoints_ne : points.Nonempty := ⟨_, hmem⟩
  have hy_lt : ∀ p ∈ points, 0 ≤ y p ∧ y p < 1 := by
    intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hq, hb⟩ := hp
    rw [Finset.mem_filter] at hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [Finset.mem_range] at hb1
    rw [Finset.mem_Icc] at hq
    have hq0 : (0:ℝ) < p.1 := by
      have : 1 ≤ p.1 := hq.1
      positivity
    constructor
    · positivity
    · rw [div_lt_one hq0]
      exact_mod_cast hb1
  have hy_ne : ∀ p ∈ points, ∀ p' ∈ points, p ≠ p' → y p ≠ y p' := by
    intro p hp p' hp' hpp'
    rw [Finset.mem_sigma] at hp hp'
    intro heq
    apply hpp'
    rw [Finset.mem_filter] at *
    obtain ⟨hq1, hb1⟩ := hp
    obtain ⟨hq2, hb2⟩ := hp'
    rw [Finset.mem_Icc] at hq1 hq2
    rw [Finset.mem_range] at *
    obtain ⟨h1, h2⟩ := farey_inj (by omega : 0 < p.1) (by omega : 0 < p'.1) hb1.2 hb2.2 heq
    rcases p with ⟨q, b⟩
    rcases p' with ⟨q', b'⟩
    simp only at h1 h2 ⊢
    subst q'
    subst b'
    rfl
  have hy_sep : ∀ p ∈ points, ∀ p' ∈ points, p ≠ p' →
      δ ≤ |y p - y p'| ∧ |y p - y p'| ≤ 1 - δ := by
    intro p hp p' hp' hpp'
    rw [Finset.mem_sigma] at hp hp'
    obtain ⟨hq1, hb1⟩ := hp
    obtain ⟨hq2, hb2⟩ := hp'
    rw [Finset.mem_filter] at hb1 hb2
    rw [Finset.mem_Icc] at hq1 hq2
    rw [Finset.mem_range] at *
    have := farey_sep hX hq1 hq2 hb1.2 hb2.2 hb1.1 hb2.1 (hy_ne p (by
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_Icc.mpr hq1,
        Finset.mem_filter.mpr ⟨by simpa using hb1.1, hb1.2⟩⟩) p' (by
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_Icc.mpr hq2,
        Finset.mem_filter.mpr ⟨by simpa using hb2.1, hb2.2⟩⟩) hpp')
    rw [hδ_def]
    exact this
  -- The window for the lifted arcs.
  set pts := points.image y with hpts_def
  have hpts_ne : pts.Nonempty := hpoints_ne.image y
  obtain ⟨ρ, hρ⟩ := exists_window hpts_ne hδ hδ1 (by
    intro x₁ hx₁ x₂ hx₂ hne
    rw [Finset.mem_image] at hx₁ hx₂
    obtain ⟨p₁, hp₁, rfl⟩ := hx₁
    obtain ⟨p₂, hp₂, rfl⟩ := hx₂
    have hpp : p₁ ≠ p₂ := fun h => hne (h ▸ rfl)
    exact hy_sep p₁ hp₁ p₂ hp₂ hpp)
  -- Gallagher per point.
  have hgal : ∀ p ∈ points, ‖T (y p)‖ ^ 2 ≤
      δ⁻¹ * (∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ ^ 2) +
        (∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ * ‖T' t‖) := by
    intro p hp
    have h := gallagher_centered hTderiv hT'cont hδ (y p)
    rwa [intervalIntegral.integral_of_le (by linarith : y p - δ / 2 ≤ y p + δ / 2),
      intervalIntegral.integral_of_le (by linarith : y p - δ / 2 ≤ y p + δ / 2)] at h
  -- Shift arcs by `1` and sum.
  have harcs1 : ∑ p ∈ points, ∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ ^ 2 ≤
      ∫ t in Set.Ioc 0 1, ‖T t‖ ^ 2 := by
    rw [Finset.sum_congr rfl (fun p hp => integral_arc_shift hg1per (y p) δ hδ.le)]
    exact sum_integral_arcs_le hδ (fun i hi j hj hij => by
      have := hy_sep i hi j hj hij
      have h1 : |y i + 1 - (y j + 1)| = |y i - y j| := by
        rw [show y i + 1 - (y j + 1) = y i - y j by ring]
      rw [h1]
      exact this.1) (fun i hi => by
      have hyi : y i ∈ pts := Finset.mem_image_of_mem y hi
      exact hρ (y i) hyi) (by
      exact hTcont.norm.pow 2) (fun x => by positivity) hg1per
  have harcs2 : ∑ p ∈ points, ∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ * ‖T' t‖ ≤
      ∫ t in Set.Ioc 0 1, ‖T t‖ * ‖T' t‖ := by
    rw [Finset.sum_congr rfl (fun p hp => integral_arc_shift hg2per (y p) δ hδ.le)]
    exact sum_integral_arcs_le hδ (fun i hi j hj hij => by
      have := hy_sep i hi j hj hij
      have h1 : |y i + 1 - (y j + 1)| = |y i - y j| := by
        rw [show y i + 1 - (y j + 1) = y i - y j by ring]
      rw [h1]
      exact this.1) (fun i hi => by
      have hyi : y i ∈ pts := Finset.mem_image_of_mem y hi
      exact hρ (y i) hyi) (by
      exact hTcont.norm.mul hT'cont.norm) (fun x => by positivity) hg2per
  -- AM–GM on the cross term.
  have hlam : (0:ℝ) < Real.pi * N := by positivity
  have hamgm : (∫ t in Set.Ioc 0 1, ‖T t‖ * ‖T' t‖) ≤
      (Real.pi * N / 2) * (∫ t in Set.Ioc 0 1, ‖T t‖ ^ 2) +
        (2 * Real.pi * N)⁻¹ * (∫ t in Set.Ioc 0 1, ‖T' t‖ ^ 2) := by
    have hpt : ∀ t : ℝ, ‖T t‖ * ‖T' t‖ ≤
        (Real.pi * N / 2) * ‖T t‖ ^ 2 + (2 * Real.pi * N)⁻¹ * ‖T' t‖ ^ 2 := by
      intro t
      have h1 : (Real.pi * N / 2) * ‖T t‖ ^ 2 + (2 * Real.pi * N)⁻¹ * ‖T' t‖ ^ 2 -
          ‖T t‖ * ‖T' t‖ =
          (Real.pi * N / 2) * (‖T t‖ - ‖T' t‖ / (Real.pi * N)) ^ 2 := by
        field_simp
        ring
      have h2 : 0 ≤ (Real.pi * N / 2) * (‖T t‖ - ‖T' t‖ / (Real.pi * N)) ^ 2 := by positivity
      linarith [h2]
    have hint1 : IntegrableOn (fun t => ‖T t‖ * ‖T' t‖) (Set.Ioc 0 1) :=
      (hTcont.norm.mul hT'cont.norm).integrableOn_Ioc
    have hint2a : IntegrableOn (fun t => (Real.pi * N / 2) * ‖T t‖ ^ 2) (Set.Ioc 0 1) :=
      ((hTcont.norm.pow 2).const_mul _).integrableOn_Ioc
    have hint2b : IntegrableOn (fun t => (2 * Real.pi * N)⁻¹ * ‖T' t‖ ^ 2) (Set.Ioc 0 1) :=
      ((hT'cont.norm.pow 2).const_mul _).integrableOn_Ioc
    calc
      ∫ t in Set.Ioc 0 1, ‖T t‖ * ‖T' t‖ ≤
          ∫ t in Set.Ioc 0 1, ((Real.pi * N / 2) * ‖T t‖ ^ 2 +
            (2 * Real.pi * N)⁻¹ * ‖T' t‖ ^ 2) :=
        MeasureTheory.setIntegral_mono_on hint1 (hint2a.add hint2b)
          measurableSet_Ioc (fun x _ => hpt x)
      _ = (Real.pi * N / 2) * (∫ t in Set.Ioc 0 1, ‖T t‖ ^ 2) +
          (2 * Real.pi * N)⁻¹ * (∫ t in Set.Ioc 0 1, ‖T' t‖ ^ 2) := by
        rw [MeasureTheory.integral_add hint2a hint2b, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
  have hPS' : ∫ t in Set.Ioc 0 1, ‖T t‖ ^ 2 = Z := by
    rw [← intervalIntegral.integral_of_le (zero_le_one)]
    calc
      ∫ α in (0 : ℝ)..1, ‖T α‖ ^ 2 = ∫ α in (0 : ℝ)..1, ‖S α‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro α _
        exact congrArg (fun z : ℝ => z ^ 2) (hTnorm α)
      _ = Z := hPS
  have hPU' : ∫ t in Set.Ioc 0 1, ‖T' t‖ ^ 2 ≤ Real.pi ^ 2 * N ^ 2 * Z := by
    rw [← intervalIntegral.integral_of_le (zero_le_one)]
    calc
      ∫ α in (0 : ℝ)..1, ‖T' α‖ ^ 2 = ∫ α in (0 : ℝ)..1, ‖U α‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro α _
        exact congrArg (fun z : ℝ => z ^ 2) (hT'norm α)
      _ ≤ Real.pi ^ 2 * N ^ 2 * Z := hPU
  -- Final assembly.
  have hmain : ∑ p ∈ points, ‖T (y p)‖ ^ 2 ≤ ((X : ℝ) ^ 2 + Real.pi * N) * Z := by
    calc ∑ p ∈ points, ‖T (y p)‖ ^ 2
        ≤ ∑ p ∈ points, (δ⁻¹ *
          (∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ ^ 2) +
          (∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ * ‖T' t‖)) :=
          Finset.sum_le_sum hgal
      _ = δ⁻¹ * (∑ p ∈ points,
          (∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ ^ 2)) +
          (∑ p ∈ points,
            (∫ t in Set.Ioc (y p - δ / 2) (y p + δ / 2), ‖T t‖ * ‖T' t‖)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ δ⁻¹ * (∫ t in Set.Ioc 0 1, ‖T t‖ ^ 2) +
          (∫ t in Set.Ioc 0 1, ‖T t‖ * ‖T' t‖) := by
          exact add_le_add (mul_le_mul_of_nonneg_left harcs1 (inv_nonneg.mpr hδ.le)) harcs2
      _ ≤ δ⁻¹ * Z + ((Real.pi * N / 2) * Z + (2 * Real.pi * N)⁻¹ * (Real.pi ^ 2 * N ^ 2 * Z)) := by
          rw [hPS']
          apply add_le_add le_rfl
          have hc1 : 0 ≤ Real.pi * N / 2 := by positivity
          have hc2 : 0 ≤ (2 * Real.pi * N)⁻¹ := by positivity
          exact hamgm.trans (add_le_add
            (mul_le_mul_of_nonneg_left hPS'.le hc1)
            (mul_le_mul_of_nonneg_left hPU' hc2))
      _ = ((X : ℝ) ^ 2 + Real.pi * N) * Z := by
          rw [hδ_def]
          field_simp [hX.ne', hN.ne', Real.pi_ne_zero]
          ring
  have hST : ∀ p ∈ points, ‖S (y p)‖ ^ 2 = ‖T (y p)‖ ^ 2 := by
    intro p hp
    rw [← hTnorm (y p)]
  calc
    ∑ q ∈ Finset.Icc 1 X, ∑ b ∈ (Finset.range q).filter (·.Coprime q),
        ‖S ((b : ℝ) / q)‖ ^ 2 =
        ∑ p ∈ points, ‖S (y p)‖ ^ 2 := by
          rw [hpoints_def, Finset.sum_sigma]
    _ = ∑ p ∈ points, ‖T (y p)‖ ^ 2 :=
        Finset.sum_congr rfl hST
    _ ≤ ((X : ℝ) ^ 2 + Real.pi * N) * Z := hmain

end Chen.LargeSieve

end

/-! ## ChenTheorem.LargeSieve.Character -/

section

/-
The character form of the large sieve (inequality (2) of Chen's paper) and its
dyadic corollary (inequality (3)), following the paper's derivation from the
additive form (4):

For a primitive character `χ` mod `q`, the Gauss sum expansion
`τ(χ̄) χ(n) = ∑ₐ χ̄(a) e(na/q)` with `|τ(χ̄)|² = q` gives
`(q/φ(q)) ∑*_{χ} |T(χ)|² ≤ ∑_{(a,q)=1} |S(a/q)|²`, and summing over `q ≤ X`
against the additive large sieve (`Additive.lean`) yields
`∑_{q≤X} (q/φ(q)) ∑*_{χ mod q} |∑_{M<n≤M+N} aₙ χ(n)|² ≤ (X² + πN) ∑|aₙ|²`.

The proof of `|τ(χ)|² = q` for primitive `χ` is the standard one through the
same expansion and finite Parseval on `ZMod q`, included here since Mathlib
does not yet have it.
-/

open Set MeasureTheory intervalIntegral Finset
open scoped RealInnerProductSpace ComplexConjugate

namespace Chen.LargeSieve

noncomputable local instance (p : Prop) : Decidable p := Classical.dec p

variable {q : ℕ} [NeZero q] {a : ℕ → ℂ} {s : Finset ℕ}

/-- `Ŝ(b) = ∑_{n ∈ s} aₙ e(nb/q)`, viewed as a function on `ZMod q`. -/
noncomputable def hatSum (b : ZMod q) : ℂ :=
  ∑ n ∈ s, a n * ZMod.stdAddChar ((n : ZMod q) * b)

/-- `Ŝ` evaluated at a lift agrees with the trigonometric sum at `b/q`. -/
lemma hatSum_eq_trigSum (b : ZMod q) :
    hatSum (a := a) (s := s) b = trigSum a s (b.val / q) := by
  rw [hatSum, trigSum]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have hbval : (b.val : ZMod q) = b := by
    simpa only [ZMod.cast_id] using (ZMod.natCast_val (R := ZMod q) b)
  have hcast : (n * b : ZMod q) = ((n * b.val : ℤ) : ZMod q) := by
    calc
      (n : ZMod q) * b = (n : ZMod q) * (b.val : ZMod q) :=
        congrArg (fun z : ZMod q => (n : ZMod q) * z) hbval.symm
      _ = ((n * b.val : ℕ) : ZMod q) := by rw [Nat.cast_mul]
      _ = ((n * b.val : ℤ) : ZMod q) := by norm_cast
  rw [hcast, ZMod.stdAddChar_coe, fexp]
  push_cast
  ring_nf

/-- The Gauss-sum expansion `τ(χ̄) T(χ) = ∑_b χ̄(b) Ŝ(b)` for primitive `χ`. -/
lemma gaussSum_mul_charSum {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    gaussSum χ⁻¹ ZMod.stdAddChar * (∑ n ∈ s, a n * χ n) =
      ∑ b : ZMod q, χ⁻¹ b * hatSum (a := a) (s := s) b := by
  have hprim : (χ⁻¹).IsPrimitive := by
    rwa [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv,
      ← DirichletCharacter.isPrimitive_def]
  rw [Finset.mul_sum]
  have key : ∀ n : ℕ, gaussSum χ⁻¹ ZMod.stdAddChar * (a n * χ n) =
      a n * ∑ b : ZMod q, χ⁻¹ b * ZMod.stdAddChar ((n : ZMod q) * b) := by
    intro n
    have h := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hprim (n : ZMod q)
    rw [inv_inv] at h
    have hgs : gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (n : ZMod q)) =
        ∑ b : ZMod q, χ⁻¹ b * ZMod.stdAddChar ((n : ZMod q) * b) := by
      rw [gaussSum]
      exact Finset.sum_congr rfl fun b _ => by rw [AddChar.mulShift_apply]
    rw [hgs] at h
    calc
      gaussSum χ⁻¹ ZMod.stdAddChar * (a n * χ n) =
          a n * (χ n * gaussSum χ⁻¹ ZMod.stdAddChar) := by ring
      _ = a n * ∑ b : ZMod q, χ⁻¹ b * ZMod.stdAddChar ((n : ZMod q) * b) := by
        rw [← h]
  rw [Finset.sum_congr rfl fun n _ => key n]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [hatSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Dirichlet character values at units have norm `1`. -/
lemma char_value_norm_one {χ : DirichletCharacter ℂ q} {u : (ZMod q)ˣ} :
    ‖χ (u : ZMod q)‖ = 1 := by
  have h1 : χ (u : ZMod q) ^ q.totient = 1 := by
    have h2 : ((u : ZMod q) ^ q.totient) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ZMod.pow_totient u, Units.val_one]
    rw [← map_pow, h2, map_one]
  have h3 : ‖χ (u : ZMod q)‖ ^ q.totient = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _)
    ((Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne')).mp h3

/-- `‖χ n‖² = 1` at units and `0` otherwise. -/
lemma char_norm_sq (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    ‖χ n‖ ^ 2 = if IsUnit n then (1 : ℝ) else 0 := by
  by_cases hn : IsUnit n
  · rw [if_pos hn]
    obtain ⟨u, hu⟩ := hn
    rw [← hu, char_value_norm_one, one_pow]
  · rw [if_neg hn, MulChar.map_nonunit _ hn, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]

/-- The number of units of `ZMod q` as a real sum. -/
lemma card_units_eq_totient :
    (Finset.univ.filter (fun n : ZMod q => IsUnit n)).card = q.totient := by
  have h1 : Fintype.card (ZMod q)ˣ = q.totient := ZMod.card_units_eq_totient q
  rw [← h1]
  rw [← Finset.card_univ]
  symm
  apply Finset.card_bij (s := (Finset.univ : Finset (ZMod q)ˣ))
    (t := Finset.univ.filter (fun n : ZMod q => IsUnit n)) (fun u _ => (u : ZMod q))
  · intro u _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.isUnit⟩
  · intro u v _ _ h
    exact Units.ext h
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨-, hx⟩ := hx
    obtain ⟨u, hu⟩ := hx
    exact ⟨u, Finset.mem_univ _, hu⟩

/-- `∑_{n : ZMod q} ‖χ n‖² = φ(q)`. -/
lemma sum_char_norm_sq (χ : DirichletCharacter ℂ q) :
    (∑ n : ZMod q, ‖χ n‖ ^ 2) = (q.totient : ℝ) := by
  rw [Finset.sum_congr rfl fun n _ => char_norm_sq χ n, Finset.sum_boole,
    card_units_eq_totient]

/-- `star (stdAddChar x) = stdAddChar (-x)`. -/
lemma star_stdAddChar (x : ZMod q) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hnorm : ‖ZMod.stdAddChar x‖ = 1 := by
    simpa only [ZMod.stdAddChar_apply] using Circle.norm_coe (ZMod.toCircle x)
  have h1 : ZMod.stdAddChar (-x) * ZMod.stdAddChar x = 1 := by
    rw [← ZMod.stdAddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : star (ZMod.stdAddChar x) * ZMod.stdAddChar x = 1 := by
    rw [mul_comm]
    change ZMod.stdAddChar x * conj (ZMod.stdAddChar x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm, one_pow, Complex.ofReal_one]
  exact (eq_inv_of_mul_eq_one_left h2).trans (eq_inv_of_mul_eq_one_left h1).symm

/-- The orthogonality of the standard additive character on `ZMod q`:
`∑_{n} e(nt) = q·δ_{t,0}`. -/
lemma sum_stdAddChar_mul (t : ZMod q) :
    (∑ n : ZMod q, ZMod.stdAddChar (n * t)) = if t = 0 then (q : ℂ) else 0 := by
  by_cases ht : t = 0
  · rw [ht, if_pos rfl]
    simp [mul_zero, AddChar.map_zero_eq_one]
  · rw [if_neg ht]
    have h2 : ZMod.stdAddChar.mulShift t ≠ 1 := by
      exact ZMod.isPrimitive_stdAddChar q ht
    have h4 : (∑ n : ZMod q, ZMod.stdAddChar (n * t)) =
        ∑ n : ZMod q, (ZMod.stdAddChar.mulShift t) n := by
      exact Finset.sum_congr rfl fun n _ => by
        rw [AddChar.mulShift_apply, mul_comm]
    rw [h4, AddChar.sum_eq_zero_of_ne_one h2]

/-- The double-sum identity underlying `|τ|² = q` and the character form of the
large sieve: `∑_n (∑_b z_b e(nb))·star(∑_c z_c e(nc)) = q ∑_b z_b·star(z_b)`
for complex `z` supported on... — here stated for `z_b = χ b`, in which case
the right-hand side is `q·φ(q)`. -/
lemma double_sum_stdAddChar (z : ZMod q → ℂ) :
    (∑ n : ZMod q, (∑ b : ZMod q, z b * ZMod.stdAddChar (n * b)) *
      star (∑ c : ZMod q, z c * ZMod.stdAddChar (n * c))) =
      (q : ℂ) * ∑ b : ZMod q, z b * star (z b) := by
  have h1 : ∀ n : ZMod q, (∑ b : ZMod q, z b * ZMod.stdAddChar (n * b)) *
      star (∑ c : ZMod q, z c * ZMod.stdAddChar (n * c)) =
      ∑ b : ZMod q, ∑ c : ZMod q, (z b * star (z c)) * ZMod.stdAddChar (n * (b - c)) := by
    intro n
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [star_mul, star_stdAddChar]
    have hadd : ZMod.stdAddChar (n * b) * ZMod.stdAddChar (-(n * c)) =
        ZMod.stdAddChar (n * (b - c)) := by
      rw [← ZMod.stdAddChar.map_add_eq_mul]
      congr 1
      ring
    calc
      z b * ZMod.stdAddChar (n * b) * (ZMod.stdAddChar (-(n * c)) * star (z c)) =
          (z b * star (z c)) *
            (ZMod.stdAddChar (n * b) * ZMod.stdAddChar (-(n * c))) := by ring
      _ = (z b * star (z c)) * ZMod.stdAddChar (n * (b - c)) := by rw [hadd]
  rw [Finset.sum_congr rfl (fun n _ => h1 n), Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  calc
    (∑ n : ZMod q, ∑ c : ZMod q,
        (z b * star (z c)) * ZMod.stdAddChar (n * (b - c))) =
        ∑ c : ZMod q, ∑ n : ZMod q,
          (z b * star (z c)) * ZMod.stdAddChar (n * (b - c)) := Finset.sum_comm
    _ = ∑ c : ZMod q, (z b * star (z c)) *
        (if b - c = 0 then (q : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.mul_sum, sum_stdAddChar_mul]
    _ = (q : ℂ) * (z b * star (z b)) := by
      rw [Finset.sum_eq_single b]
      · simp [mul_comm]
      · intro c _ hcb
        simp [sub_ne_zero.mpr hcb.symm]
      · simp

/-- The Gauss-sum expansion for primitive `χ`: `χ̄(n)·τ(χ) = ∑_b χ(b) e(nb/q)`. -/
lemma char_inv_mul_gaussSum {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ b : ZMod q, χ b * ZMod.stdAddChar (n * b) := by
  have h := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ n
  rw [← h, gaussSum]
  exact Finset.sum_congr rfl fun b _ => by rw [AddChar.mulShift_apply]

/-- `|τ(χ)|² = q` for primitive `χ` mod `q`. -/
lemma gaussSum_normSq {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
  set τ := gaussSum χ ZMod.stdAddChar with hτ
  have hexp := char_inv_mul_gaussSum hχ
  -- Way 1: `∑_n ‖χ⁻¹ n·τ‖² = φ(q)·‖τ‖²`.
  have h1 : (∑ n : ZMod q, ‖χ⁻¹ n * τ‖ ^ 2) = (q.totient : ℝ) * ‖τ‖ ^ 2 := by
    have hn : ∀ n : ZMod q, ‖χ⁻¹ n‖ ^ 2 = if IsUnit n then (1 : ℝ) else 0 := by
      intro n
      exact char_norm_sq χ⁻¹ n
    rw [Finset.sum_congr rfl fun n _ => by rw [norm_mul, mul_pow, hn n], ← Finset.sum_mul,
      Finset.sum_boole, card_units_eq_totient]
  -- Way 2: `∑_n ‖χ⁻¹ n·τ‖² = q·φ(q)` via the double-sum identity.
  have h2c : (∑ n : ZMod q, (∑ b : ZMod q, χ b * ZMod.stdAddChar (n * b)) *
      star (∑ c : ZMod q, χ c * ZMod.stdAddChar (n * c))) = ((q * q.totient : ℝ) : ℂ) := by
    rw [double_sum_stdAddChar (fun b => χ b)]
    have h3 : (∑ b : ZMod q, χ b * star (χ b)) = ((q.totient : ℝ) : ℂ) := by
      have h4 : ∀ b : ZMod q, χ b * star (χ b) = ((‖χ b‖ ^ 2 : ℝ) : ℂ) := by
        intro b
        rw [show star (χ b) = conj (χ b) from rfl, Complex.mul_conj,
          Complex.normSq_eq_norm_sq]
      rw [Finset.sum_congr rfl (fun b _ => h4 b), ← Complex.ofReal_sum, sum_char_norm_sq χ]
    rw [h3]
    push_cast
    ring
  have h2 : (∑ n : ZMod q, ‖χ⁻¹ n * τ‖ ^ 2) = (q : ℝ) * q.totient := by
    have hnorm : ∀ n : ZMod q, ‖χ⁻¹ n * τ‖ ^ 2 =
        ((∑ b : ZMod q, χ b * ZMod.stdAddChar (n * b)) *
          star (∑ c : ZMod q, χ c * ZMod.stdAddChar (n * c))).re := by
      intro n
      rw [hτ, hexp n, ← Complex.normSq_eq_norm_sq]
      change Complex.normSq (∑ b : ZMod q, χ b * ZMod.stdAddChar (n * b)) =
        ((∑ b : ZMod q, χ b * ZMod.stdAddChar (n * b)) *
          conj (∑ b : ZMod q, χ b * ZMod.stdAddChar (n * b))).re
      rw [Complex.mul_conj, Complex.ofReal_re]
    rw [Finset.sum_congr rfl fun n _ => hnorm n, ← Complex.re_sum, h2c, Complex.ofReal_re]
  have htot' : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have hmul := h1.symm.trans h2
  exact mul_right_cancel₀ htot' (by simpa [mul_comm] using hmul)

/-- The orthogonality sum `∑_χ χ⁻¹(b)·star(χ⁻¹(c))` collapse helper:
`star (χ⁻¹ c) = χ c`. -/
lemma star_inv_char (χ : DirichletCharacter ℂ q) (c : ZMod q) :
    star (χ⁻¹ c) = χ c := by
  by_cases hc : IsUnit c
  · obtain ⟨u, hu⟩ := hc
    rw [← hu, MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv]
    have h1 : star ((χ (u : ZMod q))⁻¹) = χ (u : ZMod q) := by
      have h2 : star (χ (u : ZMod q)) = (χ (u : ZMod q))⁻¹ := by
        have hn := char_value_norm_one (χ := χ) (u := u)
        have h3 : (χ (u : ZMod q)) * star (χ (u : ZMod q)) = 1 := by
          change χ (u : ZMod q) * conj (χ (u : ZMod q)) = 1
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, one_pow,
            Complex.ofReal_one]
        exact eq_inv_of_mul_eq_one_right h3
      calc
        star ((χ (u : ZMod q))⁻¹) = (star (χ (u : ZMod q)))⁻¹ := by
          exact map_inv₀ (starRingEnd ℂ) _
        _ = ((χ (u : ZMod q))⁻¹)⁻¹ := by rw [h2]
        _ = χ (u : ZMod q) := inv_inv _
    exact h1
  · rw [MulChar.map_nonunit _ hc, MulChar.map_nonunit _ hc, star_zero]

/-- `∑_χ χ⁻¹(b)·χ(c) = φ(q)` if `b = c` is a unit, else `0`. -/
lemma sum_char_inv_mul_char (b c : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c) =
      if (b = c ∧ IsUnit b) then (q.totient : ℂ) else 0 := by
  by_cases hb : IsUnit b
  · have h1 : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c = χ (b⁻¹ * c) := by
      intro χ
      rw [MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv]
      have h2 : χ (b⁻¹) * χ b = 1 := by
        rw [← map_mul, ZMod.inv_mul_of_unit b hb, map_one]
      change (χ b)⁻¹ * χ c = χ (b⁻¹ * c)
      rw [← eq_inv_of_mul_eq_one_left h2, ← map_mul]
    rw [Finset.sum_congr rfl (fun χ _ => h1 χ), DirichletCharacter.sum_characters_eq]
    have hd : b⁻¹ * c = 1 ↔ b = c := by
      constructor
      · intro h
        calc
          b = b * (b⁻¹ * c) := by rw [h, mul_one]
          _ = (b * b⁻¹) * c := by ring
          _ = c := by rw [ZMod.mul_inv_of_unit b hb, one_mul]
      · rintro rfl
        exact ZMod.inv_mul_of_unit b hb
    by_cases hbc : b = c
    · rw [if_pos (hd.mpr hbc), if_pos ⟨hbc, hb⟩]
    · rw [if_neg (fun h => hbc (hd.mp h)), if_neg (fun h => hbc h.1)]
  · rw [if_neg (fun h => hb h.2), Finset.sum_eq_zero]
    intro χ _
    rw [MulChar.map_nonunit _ hb, zero_mul]

/-- The character-form orthogonality identity:
`∑_χ ‖∑_b χ⁻¹(b) Ŝ(b)‖² = φ(q)·∑_{b unit} ‖Ŝ(b)‖²`. -/
lemma sum_all_char_hatSum :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * hatSum (a := a) (s := s) b‖ ^ 2) =
      (q.totient : ℝ) * ∑ b : ZMod q,
        (if IsUnit b then ‖hatSum (a := a) (s := s) b‖ ^ 2 else 0) := by
  let H : ZMod q → ℂ := fun b => hatSum (a := a) (s := s) b
  change (∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * H b‖ ^ 2) =
    (q.totient : ℝ) * ∑ b : ZMod q, (if IsUnit b then ‖H b‖ ^ 2 else 0)
  have h1c : (∑ χ : DirichletCharacter ℂ q,
      (∑ b : ZMod q, χ⁻¹ b * H b) * star (∑ c : ZMod q, χ⁻¹ c * H c)) =
      ((q.totient : ℝ) : ℂ) * ∑ b : ZMod q,
        (if IsUnit b then (H b * star (H b)) else 0) := by
    have hstep : ∀ χ : DirichletCharacter ℂ q,
        (∑ b : ZMod q, χ⁻¹ b * H b) * star (∑ c : ZMod q, χ⁻¹ c * H c) =
        ∑ b : ZMod q, ∑ c : ZMod q, (H b * star (H c)) * (χ⁻¹ b * star (χ⁻¹ c)) := by
      intro χ
      rw [star_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [star_mul, star_inv_char]
      ring
    rw [Finset.sum_congr rfl (fun χ _ => hstep χ), Finset.sum_comm,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
    simp_rw [star_inv_char]
    calc
      (∑ c : ZMod q, ∑ χ : DirichletCharacter ℂ q,
          H b * star (H c) * (χ⁻¹ b * χ c)) =
          ∑ c : ZMod q, (H b * star (H c)) *
            (if b = c ∧ IsUnit b then (q.totient : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [← Finset.mul_sum, sum_char_inv_mul_char b c]
      _ = (q.totient : ℂ) *
          (if IsUnit b then H b * star (H b) else 0) := by
        by_cases hb : IsUnit b
        · rw [if_pos hb, Finset.sum_eq_single b]
          · simp [hb, mul_comm]
          · intro c _ hcb
            simp [Ne.symm hcb, hb]
          · simp
        · simp [hb]
  have hnorm : ∀ χ : DirichletCharacter ℂ q,
      ‖∑ b : ZMod q, χ⁻¹ b * H b‖ ^ 2 =
      ((∑ b : ZMod q, χ⁻¹ b * H b) * star (∑ c : ZMod q, χ⁻¹ c * H c)).re := by
    intro χ
    rw [← Complex.normSq_eq_norm_sq]
    change Complex.normSq (∑ b : ZMod q, χ⁻¹ b * H b) =
      ((∑ b : ZMod q, χ⁻¹ b * H b) *
        conj (∑ b : ZMod q, χ⁻¹ b * H b)).re
    rw [Complex.mul_conj, Complex.ofReal_re]
  have hY : (∑ b : ZMod q, (if IsUnit b then (H b * star (H b)) else 0)) =
      ((∑ b : ZMod q, (if IsUnit b then (‖H b‖ ^ 2 : ℝ) else 0) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : IsUnit b
    · rw [if_pos hb, if_pos hb, show star (H b) = conj (H b) from rfl,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · rw [if_neg hb, if_neg hb, Complex.ofReal_zero]
  rw [Finset.sum_congr rfl (fun χ _ => hnorm χ), ← Complex.re_sum, h1c, hY, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- The sum of `‖Ŝ(b)‖²` over units of `ZMod q` equals the sum of `‖S(b/q)‖²`
over reduced residues `1 ≤ b ≤ q`, `(b,q) = 1`. -/
lemma sum_units_hatSum_eq :
    (∑ b : ZMod q, (if IsUnit b then ‖hatSum (a := a) (s := s) b‖ ^ 2 else 0)) =
      ∑ b ∈ (Finset.range q).filter (·.Coprime q), ‖trigSum a s (b / q)‖ ^ 2 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij
    (s := Finset.univ.filter (fun b : ZMod q => IsUnit b))
    (t := (Finset.range q).filter (·.Coprime q)) (fun b _ => b.val)
  · intro b hb
    rw [Finset.mem_filter] at hb
    have h1 : b.val.Coprime q := by
      exact (ZMod.isUnit_iff_coprime b.val q).mp (by simpa using hb.2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt b), h1⟩
  · intro b₁ _ b₂ _ h
    exact ZMod.val_injective q h
  · intro b' hb'
    rw [Finset.mem_filter, Finset.mem_range] at hb'
    obtain ⟨hb1, hb2⟩ := hb'
    exact ⟨(b' : ZMod q), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (ZMod.isUnit_iff_coprime b' q).mpr hb2⟩, ZMod.val_cast_of_lt hb1⟩
  · intro b _
    rw [hatSum_eq_trigSum]

/-- The per-modulus bound: `(q/φ(q)) ∑*_{χ mod q} |T(χ)|² ≤ ∑_{(b,q)=1} |S(b/q)|²`. -/
lemma character_bound_per_q (hq : 1 ≤ q) :
    (q : ℝ) / (q.totient : ℝ) * (∑ χ : DirichletCharacter ℂ q,
        if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) ≤
      ∑ b ∈ (Finset.range q).filter (·.Coprime q), ‖trigSum a s (b / q)‖ ^ 2 := by
  classical
  have htot : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hT : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      (q : ℝ) * ‖∑ n ∈ s, a n * χ n‖ ^ 2 = ‖∑ b : ZMod q, χ⁻¹ b * hatSum (a := a) (s := s) b‖ ^ 2 := by
    intro χ hχ
    have hprim : (χ⁻¹).IsPrimitive := by
      rwa [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv,
        ← DirichletCharacter.isPrimitive_def]
    have h1 := gaussSum_mul_charSum (a := a) (s := s) hχ
    have h3 : ‖gaussSum χ⁻¹ ZMod.stdAddChar * (∑ n ∈ s, a n * χ n)‖ ^ 2 =
        (q : ℝ) * ‖∑ n ∈ s, a n * χ n‖ ^ 2 := by
      rw [norm_mul, mul_pow, gaussSum_normSq hprim]
    rw [h1] at h3
    rw [← h3]
  have h4 : (q : ℝ) * ∑ χ : DirichletCharacter ℂ q,
      (if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) =
      ∑ χ : DirichletCharacter ℂ q, (if χ.IsPrimitive then
        ‖∑ b : ZMod q, χ⁻¹ b * hatSum (a := a) (s := s) b‖ ^ 2 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    by_cases hχ : χ.IsPrimitive
    · rw [if_pos hχ, if_pos hχ, hT χ hχ]
    · rw [if_neg hχ, if_neg hχ, mul_zero]
  have h5 : ∑ χ : DirichletCharacter ℂ q, (if χ.IsPrimitive then
      ‖∑ b : ZMod q, χ⁻¹ b * hatSum (a := a) (s := s) b‖ ^ 2 else 0) ≤
      ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * hatSum (a := a) (s := s) b‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro χ _
    by_cases hχ : χ.IsPrimitive
    · rw [if_pos hχ]
    · rw [if_neg hχ]
      positivity
  have h6 : (q : ℝ) * ∑ χ : DirichletCharacter ℂ q,
      (if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) ≤
      (q.totient : ℝ) * ∑ b : ZMod q, (if IsUnit b then ‖hatSum (a := a) (s := s) b‖ ^ 2 else 0) := by
    rw [h4]
    exact h5.trans (le_of_eq (sum_all_char_hatSum (a := a) (s := s)))
  have h7 : (q : ℝ) / (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q,
      (if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) ≤
      ∑ b : ZMod q, (if IsUnit b then ‖hatSum (a := a) (s := s) b‖ ^ 2 else 0) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ htot]
    simpa [mul_comm] using h6
  exact h7.trans (le_of_eq (sum_units_hatSum_eq (a := a) (s := s)))

/-- **The character form of the large sieve** (inequality (2) of Chen's paper):
`∑_{q≤X} (q/φ(q)) ∑*_{χ mod q} |∑_{M<n≤M+N} aₙ χ(n)|² ≤ (X² + πN) ∑|aₙ|²`. -/
theorem large_sieve_character (X M N : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 X, (q : ℝ) / (q.totient : ℝ) *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 else 0)
      ≤ ((X : ℝ) ^ 2 + Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  classical
  calc ∑ q ∈ Finset.Icc 1 X, (q : ℝ) / (q.totient : ℝ) * (∑ χ : DirichletCharacter ℂ q,
        if χ.IsPrimitive then ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 else 0)
      ≤ ∑ q ∈ Finset.Icc 1 X, ∑ b ∈ (Finset.range q).filter (·.Coprime q),
          ‖trigSum a (Finset.Ioc M (M + N)) (b / q)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hq' := Finset.mem_Icc.mp hq
        haveI : NeZero q := ⟨by omega⟩
        exact character_bound_per_q (a := a) (s := Finset.Ioc M (M + N)) hq'.1
    _ ≤ ((X : ℝ) ^ 2 + Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
        additive_large_sieve X M N a

/-- **The dyadic large sieve** (inequality (3) of Chen's paper):
`∑_{D<q≤Q} φ(q)⁻¹ ∑*_{χ mod q} |∑ aₙ χ(n)|² ≪ (Q + N/D) ∑|aₙ|²`,
proved by decomposing `(D, Q]` into dyadic blocks `(2ⁱD, 2ⁱ⁺¹D]` and applying
the character form at each block's top. -/
theorem large_sieve_character_dyadic :
    ∃ C : ℝ, 0 < C ∧ ∀ (D Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ D → D ≤ Q →
      ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2 else 0) ≤
        C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  refine ⟨8 + 2 * Real.pi, by positivity, fun D Q M N a hD hDQ => ?_⟩
  set s := Finset.Ioc M (M + N)
  set Z := ∑ n ∈ s, ‖a n‖ ^ 2
  set F : ℕ → ℝ := fun q => (q.totient : ℝ)⁻¹ * (∑ χ : DirichletCharacter ℂ q,
    if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0)
  have hF : ∀ q, 0 ≤ F q := by
    intro q
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun χ _ => by split_ifs <;> positivity)
  rcases eq_or_lt_of_le hDQ with rfl | hlt
  · simp only [Finset.Ioc_self, Finset.sum_empty]
    positivity
  · -- D < Q: decompose into dyadic blocks.
    set h := Nat.log 2 ((Q - 1) / D) with hh_def
    have hblock : ∀ i : ℕ, ∑ q ∈ Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D), F q ≤
        (2 ^ (i + 2) * D + Real.pi * N / (2 ^ i * D)) * Z := by
      intro i
      have hDi : (0 : ℝ) < (2 ^ i * D : ℝ) := by positivity
      have hXnn : ∀ q : ℕ, 0 ≤ (q : ℝ) / (q.totient : ℝ) * (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) := by
        intro q
        positivity
      calc ∑ q ∈ Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D), F q
          ≤ (2 ^ i * D : ℝ)⁻¹ * ∑ q ∈ Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D),
              (q : ℝ) / (q.totient : ℝ) * (∑ χ : DirichletCharacter ℂ q,
                if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro q hq
            rw [Finset.mem_Ioc] at hq
            have hq0 : (0 : ℝ) < q := by
              exact_mod_cast (by omega : 0 < q)
            have htotq : (0:ℝ) < q.totient := by
              exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
            have hX : 0 ≤ (∑ χ : DirichletCharacter ℂ q,
                if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) :=
              Finset.sum_nonneg fun χ _ => by split_ifs <;> positivity
            have hrewrite : (q.totient : ℝ)⁻¹ * (∑ χ : DirichletCharacter ℂ q,
                if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) =
                (q : ℝ)⁻¹ * ((q : ℝ) / (q.totient : ℝ) *
                  (∑ χ : DirichletCharacter ℂ q,
                  if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0)) := by
              field_simp
            change (q.totient : ℝ)⁻¹ * (∑ χ : DirichletCharacter ℂ q,
                if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) ≤
              (2 ^ i * D : ℝ)⁻¹ * ((q : ℝ) / (q.totient : ℝ) *
                (∑ χ : DirichletCharacter ℂ q,
                  if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0))
            rw [hrewrite]
            have hinv : (q : ℝ)⁻¹ ≤ (2 ^ i * D : ℝ)⁻¹ := by
              apply (inv_le_inv₀ hq0 hDi).2
              exact_mod_cast (le_of_lt hq.1)
            simpa [mul_assoc] using
              mul_le_mul_of_nonneg_right hinv (mul_nonneg (by positivity) hX)
        _ ≤ (2 ^ i * D : ℝ)⁻¹ * (((2 ^ (i + 1) * D : ℝ)) ^ 2 + Real.pi * N) * Z := by
            have hext : ∑ q ∈ Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D),
                (q : ℝ) / (q.totient : ℝ) * (∑ χ : DirichletCharacter ℂ q,
                  if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) ≤
                ∑ q ∈ Finset.Icc 1 (2 ^ (i + 1) * D), (q : ℝ) / (q.totient : ℝ) *
                  (∑ χ : DirichletCharacter ℂ q,
                    if χ.IsPrimitive then ‖∑ n ∈ s, a n * χ n‖ ^ 2 else 0) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro q hq
                rw [Finset.mem_Ioc] at hq
                rw [Finset.mem_Icc]
                exact ⟨by omega, hq.2⟩
              · intro q _ _
                exact hXnn q
            have hls := hext.trans (large_sieve_character (2 ^ (i + 1) * D) M N a)
            simpa only [Z, s, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using
              mul_le_mul_of_nonneg_left hls (inv_nonneg.mpr hDi.le)
        _ = (2 ^ (i + 2) * D + Real.pi * N / (2 ^ i * D)) * Z := by
            field_simp
            ring
    have hdisj : Set.PairwiseDisjoint (Finset.range (h + 1))
        (fun i => Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D)) := by
      intro i _ j _ hij
      apply Finset.disjoint_left.mpr
      intro q hq1 hq2
      rw [Finset.mem_Ioc] at hq1 hq2
      rcases lt_or_gt_of_ne hij with hij | hji
      · have hpow : 2 ^ (i + 1) ≤ 2 ^ j :=
          pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
        have hsep := Nat.mul_le_mul_right D hpow
        omega
      · have hpow : 2 ^ (j + 1) ≤ 2 ^ i :=
          pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
        have hsep := Nat.mul_le_mul_right D hpow
        omega
    have hcover : Finset.Ioc D Q ⊆ (Finset.range (h + 1)).biUnion
        (fun i => Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D)) := by
      intro q hq
      rw [Finset.mem_Ioc] at hq
      rw [Finset.mem_biUnion]
      refine ⟨Nat.log 2 ((q - 1) / D), ?_, ?_⟩
      · rw [Finset.mem_range, Nat.lt_succ_iff]
        exact Nat.log_mono_right (Nat.div_le_div_right (by omega : q - 1 ≤ Q - 1))
      · rw [Finset.mem_Ioc]
        constructor
        · have h1 : 2 ^ Nat.log 2 ((q - 1) / D) * D ≤ q - 1 := by
            have hx : 0 < (q - 1) / D := Nat.div_pos (by omega) (by omega)
            have h2 := Nat.pow_log_le_self 2 (x := (q - 1) / D) hx.ne'
            calc 2 ^ Nat.log 2 ((q - 1) / D) * D
                ≤ ((q - 1) / D) * D := Nat.mul_le_mul_right D h2
              _ ≤ q - 1 := Nat.div_mul_le_self _ _
          omega
        · have h2 : (q - 1) / D < 2 ^ (Nat.log 2 ((q - 1) / D) + 1) :=
            Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
          have h3 : q - 1 < 2 ^ (Nat.log 2 ((q - 1) / D) + 1) * D := by
            exact (Nat.div_lt_iff_lt_mul (by omega : 0 < D)).mp h2
          omega
    have hZ : 0 ≤ Z := Finset.sum_nonneg fun n _ => sq_nonneg ‖a n‖
    have hhpow : 2 ^ h * D ≤ Q := by
      rw [hh_def]
      have hx : 0 < (Q - 1) / D := Nat.div_pos (by omega) (by omega)
      calc
        2 ^ Nat.log 2 ((Q - 1) / D) * D
            ≤ ((Q - 1) / D) * D :=
              Nat.mul_le_mul_right D (Nat.pow_log_le_self 2 hx.ne')
        _ ≤ Q - 1 := Nat.div_mul_le_self _ _
        _ ≤ Q := by omega
    have hpowSum : ∀ k : ℕ, (∑ i ∈ Finset.range k, (2 : ℝ) ^ i) ≤ 2 ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Finset.sum_range_succ, pow_succ]
          nlinarith [show 0 ≤ (2 : ℝ) ^ k by positivity]
    have hfirst :
        (∑ i ∈ Finset.range (h + 1), (2 ^ (i + 2) * D : ℝ)) ≤ 8 * Q := by
      calc
        (∑ i ∈ Finset.range (h + 1), (2 ^ (i + 2) * D : ℝ)) =
            4 * (D : ℝ) * ∑ i ∈ Finset.range (h + 1), (2 : ℝ) ^ i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ ≤ 4 * (D : ℝ) * (2 : ℝ) ^ (h + 1) := by
              gcongr
              exact hpowSum (h + 1)
        _ = 8 * ((2 ^ h * D : ℕ) : ℝ) := by
              push_cast
              rw [pow_succ]
              ring
        _ ≤ 8 * Q := by
              exact_mod_cast (Nat.mul_le_mul_left 8 hhpow)
    have hsecond :
        (∑ i ∈ Finset.range (h + 1), Real.pi * N / (2 ^ i * D)) ≤
          2 * Real.pi * N / D := by
      have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
      calc
        (∑ i ∈ Finset.range (h + 1), Real.pi * N / (2 ^ i * D)) =
            (Real.pi * N / D) *
              ∑ i ∈ Finset.range (h + 1), (1 / (2 : ℝ)) ^ i := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                rw [div_pow]
                norm_num
                field_simp
        _ ≤ (Real.pi * N / D) * 2 := by
              apply mul_le_mul_of_nonneg_left (sum_geometric_two_le (h + 1))
              positivity
        _ = 2 * Real.pi * N / D := by ring
    have hcoef :
        (∑ i ∈ Finset.range (h + 1),
            ((2 ^ (i + 2) * D : ℝ) + Real.pi * N / (2 ^ i * D))) ≤
          8 * Q + 2 * Real.pi * N / D := by
      rw [Finset.sum_add_distrib]
      exact add_le_add hfirst hsecond
    have hsum :
        ∑ q ∈ Finset.Ioc D Q, F q ≤
          (8 * Q + 2 * Real.pi * N / D) * Z := by
      calc
        ∑ q ∈ Finset.Ioc D Q, F q ≤
            ∑ q ∈ (Finset.range (h + 1)).biUnion
              (fun i => Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D)), F q := by
                apply Finset.sum_le_sum_of_subset_of_nonneg hcover
                intro q _ _
                exact hF q
        _ = ∑ i ∈ Finset.range (h + 1),
              ∑ q ∈ Finset.Ioc (2 ^ i * D) (2 ^ (i + 1) * D), F q := by
                exact Finset.sum_biUnion hdisj
        _ ≤ ∑ i ∈ Finset.range (h + 1),
              ((2 ^ (i + 2) * D : ℝ) + Real.pi * N / (2 ^ i * D)) * Z := by
                apply Finset.sum_le_sum
                intro i _
                exact hblock i
        _ = (∑ i ∈ Finset.range (h + 1),
              ((2 ^ (i + 2) * D : ℝ) + Real.pi * N / (2 ^ i * D))) * Z := by
                rw [Finset.sum_mul]
        _ ≤ (8 * Q + 2 * Real.pi * N / D) * Z :=
              mul_le_mul_of_nonneg_right hcoef hZ
    have hQ0 : (0 : ℝ) ≤ Q := by positivity
    have hND0 : (0 : ℝ) ≤ (N : ℝ) / D := by positivity
    have hconstant :
        8 * (Q : ℝ) + 2 * Real.pi * N / D ≤
          (8 + 2 * Real.pi) * ((Q : ℝ) + (N : ℝ) / D) := by
      calc
        8 * (Q : ℝ) + 2 * Real.pi * N / D ≤
            8 * Q + 2 * Real.pi * N / D +
              (2 * Real.pi * Q + 8 * ((N : ℝ) / D)) := by
                exact le_add_of_nonneg_right
                  (add_nonneg
                    (mul_nonneg (show 0 ≤ 2 * Real.pi by positivity) hQ0)
                    (mul_nonneg (show (0 : ℝ) ≤ 8 by norm_num) hND0))
        _ = (8 + 2 * Real.pi) * ((Q : ℝ) + (N : ℝ) / D) := by ring
    change ∑ q ∈ Finset.Ioc D Q, F q ≤
      (8 + 2 * Real.pi) * ((Q : ℝ) + (N : ℝ) / D) * Z
    exact hsum.trans (mul_le_mul_of_nonneg_right hconstant hZ)

end Chen.LargeSieve

end

/-! ## ChenTheorem.Lemma5.PrimeReciprocals -/

section

open Finset Real Filter
open scoped Nat.Prime Classical

namespace Chen

noncomputable def primeIndicator (n : ℕ) : ℝ :=
  if n.Prime then 1 else 0

theorem sum_primeIndicator_eq_primeCounting (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, primeIndicator k =
      (n.primeCounting : ℝ) := by
  have hset :
      (Finset.Icc 0 n).filter Nat.Prime = n.primesLE := by
    ext k
    simp [Nat.primesLE, Nat.primesBelow]
  rw [← Nat.primesLE_card_eq_primeCounting, ← hset]
  simp [primeIndicator]

theorem sum_inv_primeIndicator_eq_sum_primesLE (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, (k : ℝ)⁻¹ * primeIndicator k =
      ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ := by
  have hset :
      (Finset.Icc 0 n).filter Nat.Prime = n.primesLE := by
    ext k
    simp [Nat.primesLE, Nat.primesBelow]
  rw [← hset]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hp : k.Prime <;> simp [primeIndicator, hp]

theorem sum_inv_primesLE_eq (n : ℕ) :
    ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ =
      (n.primeCounting : ℝ) / n +
        ∫ t in Set.Ioc (2 : ℝ) n,
          (⌊t⌋₊.primeCounting : ℝ) / t ^ 2 := by
  have hab :=
    sum_mul_eq_sub_integral_mul₁
      primeIndicator (f := fun t : ℝ => t⁻¹)
      (by simp [primeIndicator, Nat.not_prime_zero])
      (by simp [primeIndicator, Nat.not_prime_one]) n
      (by
        intro t ht
        exact differentiableAt_inv (by linarith [ht.1]))
      (by
        rw [deriv_inv']
        apply ContinuousOn.integrableOn_Icc
        exact (continuousOn_id.pow 2).inv₀
          (fun t ht => pow_ne_zero 2 (by
            simpa only [id_eq] using
              (show t ≠ 0 by linarith [ht.1]))) |>.neg)
  rw [sum_inv_primeIndicator_eq_sum_primesLE,
    sum_primeIndicator_eq_primeCounting, deriv_inv'] at hab
  simp_rw [sum_primeIndicator_eq_primeCounting] at hab
  simp only [neg_mul] at hab
  rw [MeasureTheory.integral_neg] at hab
  simpa [div_eq_mul_inv, mul_comm] using hab

theorem primeCounting_le_log_term_add_sqrt
    {t : ℝ} (ht : 2 ≤ t) :
    (⌊t⌋₊.primeCounting : ℝ) ≤
      2 * Real.log 4 * t / Real.log t + Real.sqrt t := by
  have h := Chebyshev.pi_le_log4_mul_div (lt_of_lt_of_le (by norm_num) ht)
  rw [Real.log_sqrt (by positivity : 0 ≤ t)] at h
  have hlog : Real.log t ≠ 0 :=
    ne_of_gt (Real.log_pos (lt_of_lt_of_le (by norm_num) ht))
  calc
    (⌊t⌋₊.primeCounting : ℝ) ≤
        Real.log 4 * t / (Real.log t / 2) + Real.sqrt t := h
    _ = 2 * Real.log 4 * t / Real.log t + Real.sqrt t := by
      field_simp

theorem primeCounting_div_sq_le
    {t : ℝ} (ht : 2 ≤ t) :
    (⌊t⌋₊.primeCounting : ℝ) / t ^ 2 ≤
      2 * Real.log 4 / (t * Real.log t) +
        t ^ (-(3 : ℝ) / 2) := by
  have hpi := primeCounting_le_log_term_add_sqrt ht
  have htpos : 0 < t := by linarith
  have hsq : 0 < t ^ 2 := by positivity
  calc
    (⌊t⌋₊.primeCounting : ℝ) / t ^ 2 ≤
        (2 * Real.log 4 * t / Real.log t +
          Real.sqrt t) / t ^ 2 :=
      (div_le_div_iff_of_pos_right hsq).2 hpi
    _ = 2 * Real.log 4 / (t * Real.log t) +
        t ^ (-(3 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      rw [add_div]
      congr 1
      · field_simp
      rw [div_eq_mul_inv, ← Real.rpow_natCast]
      change t ^ ((1 : ℝ) / 2) * (t ^ (2 : ℝ))⁻¹ =
        t ^ (-(3 : ℝ) / 2)
      rw [← Real.rpow_neg (le_of_lt htpos) (2 : ℝ),
        ← Real.rpow_add htpos]
      congr 1
      norm_num

theorem integral_one_div_mul_log (n : ℝ) (hn : 2 ≤ n) :
    ∫ t in (2 : ℝ)..n, 1 / (t * Real.log t) =
      Real.log (Real.log n) - Real.log (Real.log 2) := by
  let F : ℝ → ℝ := fun t => Real.log (Real.log t)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    have ht2 : 2 ≤ t := by
      rw [Set.uIcc_of_le hn] at ht
      exact ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog0 : Real.log t ≠ 0 :=
      ne_of_gt (Real.log_pos (by linarith))
    have h := (Real.hasDerivAt_log ht0).log hlog0
    simpa only [one_div, mul_inv, div_eq_mul_inv, mul_comm,
      one_mul] using h
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hn]
    have hlogcont :
        ContinuousOn Real.log (Set.Icc (2 : ℝ) n) :=
      Real.continuousOn_log.mono (by
        intro t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [ht.1])
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_id :
          ContinuousOn (fun x : ℝ => x) (Set.Icc 2 n)).mul
        hlogcont)
    intro t ht
    exact mul_ne_zero (by
      simpa only [id_eq] using
        (show t ≠ 0 by linarith [ht.1]))
      (ne_of_gt (Real.log_pos (by linarith [ht.1])))

theorem integral_rpow_neg_three_halves_le_two
    (n : ℝ) (hn : 2 ≤ n) :
    ∫ t in (2 : ℝ)..n, t ^ (-(3 : ℝ) / 2) ≤ 2 := by
  rw [integral_rpow]
  · have hnnonneg :
        0 ≤ n ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
    have htwo :
        (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    norm_num
    linarith
  · right
    constructor
    · norm_num
    · rw [Set.uIcc_of_le hn]
      intro hzero
      have hmem := hzero
      simp only [Set.mem_Icc] at hmem
      norm_num at hmem

theorem primeCounting_div_nat_le_one
    (n : ℕ) (hn : 1 ≤ n) :
    (n.primeCounting : ℝ) / n ≤ 1 := by
  have hcard : n.primeCounting ≤ n := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    have hsub : n.primesLE ⊆ Finset.Icc 1 n := by
      intro p hp
      have hp' := Nat.prime_of_mem_primesLE hp
      exact Finset.mem_Icc.mpr ⟨hp'.one_le, Nat.le_of_mem_primesLE hp⟩
    have hc := Finset.card_le_card hsub
    simpa [Nat.card_Icc, hn] using hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  rw [div_le_one hnR]
  exact_mod_cast hcard

theorem sum_inv_primesLE_le_log_log (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ ≤
      1 + 2 * Real.log 4 *
        (Real.log (Real.log n) - Real.log (Real.log 2)) + 2 := by
  rw [sum_inv_primesLE_eq]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hleftOn :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          (⌊t⌋₊.primeCounting : ℝ) / t ^ 2)
        (Set.Icc 2 (n : ℝ)) := by
    have hg :
        MeasureTheory.IntegrableOn
          (fun t : ℝ => (t ^ 2)⁻¹)
          (Set.Icc 2 (n : ℝ)) := by
      apply ContinuousOn.integrableOn_Icc
      exact (continuousOn_id.pow 2).inv₀ (by
        intro t ht
        exact pow_ne_zero 2 (by
          simpa only [id_eq] using
            (show t ≠ 0 by linarith [ht.1])))
    have hi :=
      integrableOn_mul_sum_Icc
        (c := primeIndicator) (m := 0)
        (a := (2 : ℝ)) (b := (n : ℝ))
        (by norm_num) hg
    simp_rw [sum_primeIndicator_eq_primeCounting] at hi
    simpa only [div_eq_mul_inv, mul_comm] using hi
  have hlogTermOn :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          2 * Real.log 4 / (t * Real.log t))
        (Set.Icc 2 (n : ℝ)) := by
    apply ContinuousOn.integrableOn_Icc
    have hlogcont :
        ContinuousOn Real.log (Set.Icc (2 : ℝ) n) :=
      Real.continuousOn_log.mono (by
        intro t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith [ht.1])
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_id :
          ContinuousOn (fun x : ℝ => x) (Set.Icc 2 n)).mul
        hlogcont)
    intro t ht
    exact mul_ne_zero (by
      simpa only [id_eq] using
        (show t ≠ 0 by linarith [ht.1]))
      (ne_of_gt (Real.log_pos (by linarith [ht.1])))
  have hrpowOn :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => t ^ (-(3 : ℝ) / 2))
        (Set.Icc 2 (n : ℝ)) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    exact (Real.continuousAt_rpow_const t
      (-(3 : ℝ) / 2) (.inl (by linarith [ht.1]))).continuousWithinAt
  have hrightOn :
      MeasureTheory.IntegrableOn
        (fun t : ℝ =>
          2 * Real.log 4 / (t * Real.log t) +
            t ^ (-(3 : ℝ) / 2))
        (Set.Icc 2 (n : ℝ)) :=
    hlogTermOn.add hrpowOn
  have hleftInt :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hnR).2 hleftOn
  have hlogTermInt :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hnR).2 hlogTermOn
  have hrpowInt :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hnR).2 hrpowOn
  have hrightInt :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hnR).2 hrightOn
  have hinter :
      (∫ t in (2 : ℝ)..n,
          (⌊t⌋₊.primeCounting : ℝ) / t ^ 2) ≤
        ∫ t in (2 : ℝ)..n,
          (2 * Real.log 4 / (t * Real.log t) +
            t ^ (-(3 : ℝ) / 2)) := by
    apply intervalIntegral.integral_mono_on hnR
      hleftInt hrightInt
    intro t ht
    exact primeCounting_div_sq_le ht.1
  have hrpow :=
    integral_rpow_neg_three_halves_le_two (n : ℝ) hnR
  have hlogint := integral_one_div_mul_log (n : ℝ) hnR
  rw [intervalIntegral.integral_add hlogTermInt hrpowInt,
    show (fun t : ℝ => 2 * Real.log 4 / (t * Real.log t)) =
      fun t : ℝ => (2 * Real.log 4) * (1 / (t * Real.log t)) by
        funext t
        ring,
    intervalIntegral.integral_const_mul, hlogint] at hinter
  calc
    (n.primeCounting : ℝ) / n +
        ∫ t in Set.Ioc (2 : ℝ) n,
          (⌊t⌋₊.primeCounting : ℝ) / t ^ 2 ≤
      1 + ∫ t in Set.Ioc (2 : ℝ) n,
          (⌊t⌋₊.primeCounting : ℝ) / t ^ 2 := by
        gcongr
        exact primeCounting_div_nat_le_one n (by omega)
    _ = 1 + ∫ t in (2 : ℝ)..n,
          (⌊t⌋₊.primeCounting : ℝ) / t ^ 2 := by
      rw [intervalIntegral.integral_of_le hnR]
    _ ≤ 1 + (2 * Real.log 4 *
          (Real.log (Real.log n) - Real.log (Real.log 2)) +
        ∫ t in (2 : ℝ)..n, t ^ (-(3 : ℝ) / 2)) := by
      gcongr
    _ ≤ 1 + 2 * Real.log 4 *
          (Real.log (Real.log n) - Real.log (Real.log 2)) + 2 := by
      linarith

/-- The square of the prime harmonic sum grows more slowly than any
fixed positive power of `log n`.  The exponent `1/25` leaves the
specific margin needed by the short-interval sieve in Lemma 5. -/
theorem eventually_sum_inv_primesLE_sq_le_log_rpow :
    ∀ᶠ n : ℕ in atTop,
      (∑ p ∈ n.primesLE, (p : ℝ)⁻¹) ^ 2 ≤
        (Real.log n) ^ ((1 : ℝ) / 25) := by
  let A : ℝ := 2 * Real.log 4
  let B : ℝ := 3 - A * Real.log (Real.log 2)
  let C : ℝ := A + B
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hB : 0 < B := by
    dsimp only [B, A]
    have hloglog2 : Real.log (Real.log 2) < 0 := by
      rw [Real.log_neg_iff (Real.log_pos (by norm_num))]
      have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ))
        (by norm_num) (by norm_num)
      norm_num at h
      exact h
    nlinarith [Real.log_pos (show (1 : ℝ) < 4 by norm_num)]
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hlogNat :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog :
      ∀ᶠ n : ℕ in atTop,
        Real.log (Real.log n) ≤
          (Real.log n) ^ ((1 : ℝ) / 100) := by
    have hδ : (0 : ℝ) < (1 : ℝ) / 100 := by norm_num
    have hreal :
        ∀ᶠ y : ℝ in atTop,
          ‖Real.log y ^ (1 : ℝ)‖ ≤
            ‖y ^ ((1 : ℝ) / 100)‖ :=
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hδ).eventuallyLE
    have hnat := hlogNat.eventually hreal
    filter_upwards [hnat, hlogNat.eventually (eventually_gt_atTop 1)]
        with n hn hL
    have hlogL : 0 < Real.log (Real.log n) :=
      Real.log_pos hL
    have hLpos : 0 < Real.log (n : ℝ) :=
      zero_lt_one.trans hL
    simpa [Real.rpow_one, Real.norm_of_nonneg hlogL.le,
      Real.norm_of_nonneg (Real.rpow_nonneg hLpos.le _)] using hn
  have hconstant :
      ∀ᶠ n : ℕ in atTop,
        C ^ 2 ≤ (Real.log n) ^ ((1 : ℝ) / 50) := by
    have hrpow :
        Tendsto (fun y : ℝ => y ^ ((1 : ℝ) / 50)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    exact hlogNat.eventually
      (hrpow.eventually (eventually_ge_atTop (C ^ 2)))
  filter_upwards [eventually_ge_atTop 2, hloglog, hconstant,
      hlogNat.eventually (eventually_ge_atTop (Real.exp 1))] with
      n hn hloglog hconstant hL
  have hsum := sum_inv_primesLE_le_log_log n hn
  have hloglogOne : 1 ≤ Real.log (Real.log n) := by
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log (Real.log n) :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr (Real.exp_pos 1))
          (Set.mem_Ioi.mpr ((Real.exp_pos 1).trans_le hL)) hL
  have hsumNonneg :
      0 ≤ ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ := by positivity
  have hsumC :
      ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ ≤
        C * Real.log (Real.log n) := by
    calc
      ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ ≤
          A * Real.log (Real.log n) + B := by
        dsimp only [A, B]
        nlinarith [hsum]
      _ ≤ (A + B) * Real.log (Real.log n) := by
        nlinarith
      _ = C * Real.log (Real.log n) := by rfl
  have hLpos : 0 < Real.log (n : ℝ) :=
    (Real.exp_pos 1).trans_le hL
  have hsumPower :
      ∑ p ∈ n.primesLE, (p : ℝ)⁻¹ ≤
        C * (Real.log n) ^ ((1 : ℝ) / 100) :=
    hsumC.trans
      (mul_le_mul_of_nonneg_left hloglog hC.le)
  have hsquare :
      (∑ p ∈ n.primesLE, (p : ℝ)⁻¹) ^ 2 ≤
        C ^ 2 * ((Real.log n) ^ ((1 : ℝ) / 100)) ^ 2 := by
    calc
      (∑ p ∈ n.primesLE, (p : ℝ)⁻¹) ^ 2 ≤
          (C * (Real.log n) ^ ((1 : ℝ) / 100)) ^ 2 :=
        pow_le_pow_left₀ hsumNonneg hsumPower 2
      _ = C ^ 2 * ((Real.log n) ^ ((1 : ℝ) / 100)) ^ 2 := by
        ring
  calc
    (∑ p ∈ n.primesLE, (p : ℝ)⁻¹) ^ 2 ≤
        C ^ 2 * ((Real.log n) ^ ((1 : ℝ) / 100)) ^ 2 := hsquare
    _ ≤ (Real.log n) ^ ((1 : ℝ) / 50) *
          ((Real.log n) ^ ((1 : ℝ) / 100)) ^ 2 := by
      gcongr
    _ = (Real.log n) ^ ((1 : ℝ) / 25) := by
      rw [← Real.rpow_natCast,
        ← Real.rpow_mul hLpos.le,
        ← Real.rpow_add hLpos]
      congr 1
      norm_num

end Chen

end

/-! ## ChenTheorem.Lemma5.EulerPenalty -/

section

/-! Uniform control of the Euler-factor penalty caused by primes dividing `x`. -/

open Finset Real Filter
open scoped Nat.Prime Classical

namespace Chen

noncomputable def primeFactorEulerPenalty (x : ℕ) : ℝ :=
  ∏ p ∈ x.primeFactors, (1 + (p : ℝ)⁻¹)

noncomputable def primeFactorSplitLevel (x : ℕ) : ℕ :=
  ⌊Real.log x⌋₊

theorem two_pow_primeFactors_card_le {x : ℕ} (hx : 1 ≤ x) :
    2 ^ x.primeFactors.card ≤ x := by
  calc
    2 ^ x.primeFactors.card =
        ∏ p ∈ x.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ x.primeFactors, p := by
      apply Finset.prod_le_prod
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ x := by
      exact Nat.le_of_dvd (Nat.zero_lt_of_lt hx)
        (Nat.prod_primeFactors_dvd x)

theorem primeFactors_card_mul_log_two_le_log
    {x : ℕ} (hx : 1 ≤ x) :
    (x.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log x := by
  have hpow := two_pow_primeFactors_card_le hx
  have hpowR :
      (2 : ℝ) ^ x.primeFactors.card ≤ (x : ℝ) := by
    exact_mod_cast hpow
  have hposLeft : 0 < (2 : ℝ) ^ x.primeFactors.card := by positivity
  have hposRight : 0 < (x : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hx)
  have hlog :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hposLeft) (Set.mem_Ioi.mpr hposRight) hpowR
  simpa [Real.log_pow] using hlog

theorem primeFactorEulerPenalty_le_exp_sum (x : ℕ) :
    primeFactorEulerPenalty x ≤
      Real.exp (∑ p ∈ x.primeFactors, (p : ℝ)⁻¹) := by
  exact Real.prod_one_add_le_exp_sum x.primeFactors
    (fun p => by positivity)

theorem small_primeFactor_inv_sum_le
    {x Y : ℕ} :
    ∑ p ∈ x.primeFactors.filter (fun p => p ≤ Y), (p : ℝ)⁻¹ ≤
      ∑ p ∈ Y.primesLE, (p : ℝ)⁻¹ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr
      ⟨hp'.2, Nat.prime_of_mem_primeFactors hp'.1⟩
  · intro p hpY hpx
    positivity

theorem large_primeFactor_inv_sum_le
    {x Y : ℕ} (hY : 1 ≤ Y) :
    ∑ p ∈ x.primeFactors.filter (fun p => ¬ p ≤ Y), (p : ℝ)⁻¹ ≤
      (x.primeFactors.card : ℝ) / Y := by
  calc
    ∑ p ∈ x.primeFactors.filter (fun p => ¬ p ≤ Y), (p : ℝ)⁻¹ ≤
        ∑ _p ∈ x.primeFactors.filter (fun p => ¬ p ≤ Y),
          (Y : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpY : Y ≤ p := by
        have hpnot := (Finset.mem_filter.mp hp).2
        omega
      have hpPrime :=
        Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      exact (inv_le_inv₀
        (by exact_mod_cast hpPrime.pos : (0 : ℝ) < p)
        (by exact_mod_cast (Nat.zero_lt_of_lt hY))).2
          (by exact_mod_cast hpY)
    _ = ((x.primeFactors.filter (fun p => ¬ p ≤ Y)).card : ℝ) /
        Y := by
      simp [div_eq_mul_inv]
    _ ≤ (x.primeFactors.card : ℝ) / Y := by
      rw [div_le_div_iff_of_pos_right
        (by exact_mod_cast (Nat.zero_lt_of_lt hY) : (0 : ℝ) < Y)]
      exact_mod_cast Finset.card_filter_le
        x.primeFactors (fun p => ¬ p ≤ Y)

theorem primeFactor_inv_sum_split (x Y : ℕ) :
    ∑ p ∈ x.primeFactors, (p : ℝ)⁻¹ =
      (∑ p ∈ x.primeFactors.filter (fun p => p ≤ Y), (p : ℝ)⁻¹) +
      ∑ p ∈ x.primeFactors.filter (fun p => ¬ p ≤ Y), (p : ℝ)⁻¹ := by
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := x.primeFactors) (p := fun p => p ≤ Y)
      (f := fun p => (p : ℝ)⁻¹)).symm

theorem splitLevel_two_le
    {x : ℕ} (hxlog : 2 ≤ Real.log x) :
    2 ≤ primeFactorSplitLevel x := by
  unfold primeFactorSplitLevel
  exact Nat.le_floor hxlog

theorem splitLevel_cast_le_log (x : ℕ) :
    (primeFactorSplitLevel x : ℝ) ≤ Real.log x := by
  unfold primeFactorSplitLevel
  cases x with
  | zero => simp
  | succ x =>
      exact Nat.floor_le (Real.log_nonneg (by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero x))))

theorem log_half_le_splitLevel_cast
    {x : ℕ} (hxlog : 2 ≤ Real.log x) :
    Real.log x / 2 ≤ (primeFactorSplitLevel x : ℝ) := by
  have hfloor :
      Real.log x < (primeFactorSplitLevel x : ℝ) + 1 := by
    unfold primeFactorSplitLevel
    exact_mod_cast Nat.lt_floor_add_one (Real.log x)
  linarith

theorem large_primeFactor_inv_sum_le_const
    {x : ℕ} (hx : 1 ≤ x) (hxlog : 2 ≤ Real.log x) :
    ∑ p ∈ x.primeFactors.filter
        (fun p => ¬ p ≤ primeFactorSplitLevel x), (p : ℝ)⁻¹ ≤
      2 / Real.log 2 := by
  let Y := primeFactorSplitLevel x
  have hY : 1 ≤ Y := (splitLevel_two_le hxlog).trans' (by omega)
  have hlarge :=
    large_primeFactor_inv_sum_le (x := x) (Y := Y) hY
  have hcard :=
    primeFactors_card_mul_log_two_le_log hx
  have hhalf :
      Real.log x / 2 ≤ (Y : ℝ) :=
    log_half_le_splitLevel_cast hxlog
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    ∑ p ∈ x.primeFactors.filter (fun p => ¬ p ≤ Y), (p : ℝ)⁻¹ ≤
        (x.primeFactors.card : ℝ) / Y := hlarge
    _ ≤ 2 / Real.log 2 := by
      rw [div_le_div_iff₀ hYpos hlog2]
      nlinarith

theorem primeFactor_inv_sum_le_explicit
    {x : ℕ} (hx : 1 ≤ x) (hxlog : 2 ≤ Real.log x) :
    ∑ p ∈ x.primeFactors, (p : ℝ)⁻¹ ≤
      1 + 2 * Real.log 4 *
          (Real.log (Real.log (primeFactorSplitLevel x)) -
            Real.log (Real.log 2)) +
        2 + 2 / Real.log 2 := by
  let Y := primeFactorSplitLevel x
  have hY : 2 ≤ Y := splitLevel_two_le hxlog
  rw [primeFactor_inv_sum_split x Y]
  calc
    (∑ p ∈ x.primeFactors.filter (fun p => p ≤ Y), (p : ℝ)⁻¹) +
        ∑ p ∈ x.primeFactors.filter (fun p => ¬ p ≤ Y), (p : ℝ)⁻¹ ≤
      (∑ p ∈ Y.primesLE, (p : ℝ)⁻¹) +
        2 / Real.log 2 := by
      exact add_le_add small_primeFactor_inv_sum_le
        (large_primeFactor_inv_sum_le_const hx hxlog)
    _ ≤ (1 + 2 * Real.log 4 *
          (Real.log (Real.log Y) - Real.log (Real.log 2)) + 2) +
        2 / Real.log 2 := by
      gcongr
      exact sum_inv_primesLE_le_log_log Y hY
    _ = 1 + 2 * Real.log 4 *
          (Real.log (Real.log (primeFactorSplitLevel x)) -
            Real.log (Real.log 2)) +
        2 + 2 / Real.log 2 := by rfl

noncomputable def primeFactorPenaltyConstant : ℝ :=
  Real.exp
    (3 + 2 / Real.log 2 -
      2 * Real.log 4 * Real.log (Real.log 2))

theorem primeFactorPenaltyConstant_pos :
    0 < primeFactorPenaltyConstant := by
  unfold primeFactorPenaltyConstant
  positivity

theorem primeFactorEulerPenalty_le_log_splitLevel_rpow
    {x : ℕ} (hx : 1 ≤ x) (hxlog : 2 ≤ Real.log x) :
    primeFactorEulerPenalty x ≤
      primeFactorPenaltyConstant *
        (Real.log (primeFactorSplitLevel x)) ^
          (2 * Real.log 4) := by
  have hsum := primeFactor_inv_sum_le_explicit hx hxlog
  have hY : 2 ≤ primeFactorSplitLevel x :=
    splitLevel_two_le hxlog
  have hlogY :
      0 < Real.log (primeFactorSplitLevel x) :=
    Real.log_pos (by exact_mod_cast (show 1 < primeFactorSplitLevel x by omega))
  calc
    primeFactorEulerPenalty x ≤
        Real.exp (∑ p ∈ x.primeFactors, (p : ℝ)⁻¹) :=
      primeFactorEulerPenalty_le_exp_sum x
    _ ≤ Real.exp
        (1 + 2 * Real.log 4 *
            (Real.log (Real.log (primeFactorSplitLevel x)) -
              Real.log (Real.log 2)) +
          2 + 2 / Real.log 2) :=
      Real.exp_le_exp.mpr hsum
    _ = primeFactorPenaltyConstant *
        (Real.log (primeFactorSplitLevel x)) ^
          (2 * Real.log 4) := by
      rw [Real.rpow_def_of_pos hlogY]
      unfold primeFactorPenaltyConstant
      rw [← Real.exp_add]
      congr 1
      ring

theorem eventually_primeFactorEulerPenalty_le_log_rpow :
    ∀ᶠ x : ℕ in atTop,
      primeFactorEulerPenalty x ≤
        (Real.log x) ^ ((1 : ℝ) / 100) := by
  let K := primeFactorPenaltyConstant
  let A : ℝ := 2 * Real.log 4
  let b : ℝ := (1 : ℝ) / 100
  have hK : 0 < K := primeFactorPenaltyConstant_pos
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hb : 0 < b := by
    dsimp only [b]
    norm_num
  have hboundReal :
      ∀ᶠ y : ℝ in atTop,
        K * (Real.log y) ^ A ≤ y ^ b := by
    have hlittle :=
      (isLittleO_log_rpow_rpow_atTop A hb).bound (inv_pos.mpr hK)
    filter_upwards [hlittle, eventually_gt_atTop 1] with y hy hy1
    have hlogpos : 0 < Real.log y := Real.log_pos hy1
    have hypow : 0 ≤ y ^ b := Real.rpow_nonneg (by positivity) _
    have hlogpow : 0 ≤ (Real.log y) ^ A :=
      Real.rpow_nonneg hlogpos.le _
    have hy' :
        (Real.log y) ^ A ≤ K⁻¹ * y ^ b := by
      simpa [Real.norm_of_nonneg hlogpow,
        Real.norm_of_nonneg hypow] using hy
    calc
      K * (Real.log y) ^ A ≤ K * (K⁻¹ * y ^ b) :=
        mul_le_mul_of_nonneg_left hy' hK.le
      _ = y ^ b := by
        rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
  have hboundNat :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually hboundReal
  have hxlog :
      ∀ᶠ x : ℕ in atTop, 2 ≤ Real.log x :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop 2)
  filter_upwards [hboundNat, hxlog, eventually_ge_atTop 1] with
      x hbound hxlog hx
  have hYlog :
      Real.log (primeFactorSplitLevel x) ≤
        Real.log (Real.log x) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by
        exact_mod_cast (Nat.zero_lt_of_lt (splitLevel_two_le hxlog)))
    · exact Set.mem_Ioi.mpr (by linarith)
    · exact splitLevel_cast_le_log x
  have hYone : 1 ≤ primeFactorSplitLevel x := by
    have hYtwo := splitLevel_two_le hxlog
    omega
  have hpow :
      (Real.log (primeFactorSplitLevel x)) ^ A ≤
        (Real.log (Real.log x)) ^ A :=
    Real.rpow_le_rpow
      (Real.log_nonneg (by
        exact_mod_cast hYone))
      hYlog hA
  calc
    primeFactorEulerPenalty x ≤
        K * (Real.log (primeFactorSplitLevel x)) ^ A := by
      simpa only [K, A] using
        primeFactorEulerPenalty_le_log_splitLevel_rpow hx hxlog
    _ ≤ K * (Real.log (Real.log x)) ^ A :=
      mul_le_mul_of_nonneg_left hpow hK.le
    _ ≤ (Real.log x) ^ b := hbound
    _ = (Real.log x) ^ ((1 : ℝ) / 100) := by rfl

end Chen

end

/-! ## ChenTheorem.Lemma6.BiquadraticCoefficients -/

section

open ArithmeticFunction
open scoped ComplexOrder

namespace Chen

theorem convolution_prime_power_congr {p : ℕ} (hp : p.Prime)
    {f₁ f₂ g₁ g₂ : ArithmeticFunction ℂ}
    (hf : ∀ k : ℕ, f₁ (p ^ k) = f₂ (p ^ k))
    (hg : ∀ k : ℕ, g₁ (p ^ k) = g₂ (p ^ k)) (k : ℕ) :
    (f₁ * g₁) (p ^ k) = (f₂ * g₂) (p ^ k) := by
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp (show d.1 ∣ p ^ k from ⟨d.2, he.symm⟩)
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp
    (show d.2 ∣ p ^ k from ⟨d.1, by rw [mul_comm]; exact he.symm⟩)
  rw [hi, hj, hf i, hg j]

theorem charArithmetic_prime_power {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (k : ℕ) :
    toArithmeticFunction (χ ·) (p ^ k) = χ p ^ k := by
  simp [toArithmeticFunction, hp.ne_zero, map_pow]

theorem charArithmetic_prime_power_eq_one {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (h : χ p = 0) (k : ℕ) :
    toArithmeticFunction (χ ·) (p ^ k) = (1 : ArithmeticFunction ℂ) (p ^ k) := by
  rw [charArithmetic_prime_power χ hp, h]
  cases k with
  | zero => simp
  | succ k => simp [hp.ne_one]

theorem charArithmetic_prime_power_eq_zeta {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (h : χ p = 1) (k : ℕ) :
    toArithmeticFunction (χ ·) (p ^ k) = (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ k) := by
  simp [charArithmetic_prime_power χ hp, h, hp.ne_zero]

/-- The Dirichlet coefficients of ζ(s)L(s,χ)L(s,ψ)L(s,χψ).
Multiplication in this definition is Dirichlet convolution. -/
noncomputable def biquadraticCoefficients {q : ℕ}
    (χ ψ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  χ.zetaMul * (toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·))

theorem biquadraticCoefficients_isMultiplicative {q : ℕ}
    (χ ψ : DirichletCharacter ℂ q) : (biquadraticCoefficients χ ψ).IsMultiplicative :=
  χ.isMultiplicative_zetaMul.mul ((DirichletCharacter.isMultiplicative_toArithmeticFunction ψ).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction (χ * ψ)))

theorem convolution_nonneg {f g : ArithmeticFunction ℂ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f * g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun d _ => mul_nonneg (hf d.1) (hg d.2)

theorem biquadraticCoefficients_prime_power_nonneg {q p : ℕ}
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (hp : p.Prime) (k : ℕ) : 0 ≤ biquadraticCoefficients χ ψ (p ^ k) := by
  let Z : ArithmeticFunction ℂ := ArithmeticFunction.zeta
  let A := toArithmeticFunction (χ ·)
  let B := toArithmeticFunction (ψ ·)
  let C := toArithmeticFunction ((χ * ψ) ·)
  have hc (v : ℂ) (hv : χ p * ψ p = v) (i : ℕ) : C (p ^ i) = v ^ i := by
    change toArithmeticFunction ((χ * ψ) ·) (p ^ i) = v ^ i
    rw [charArithmetic_prime_power (χ * ψ) hp, MulChar.mul_apply, hv]
  have hsχ : 0 ≤ (χ.zetaMul * χ.zetaMul) (p ^ k) :=
    convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
      (DirichletCharacter.zetaMul_nonneg hχ) _
  have hsψ : 0 ≤ (ψ.zetaMul * ψ.zetaMul) (p ^ k) :=
    convolution_nonneg (DirichletCharacter.zetaMul_nonneg hψ)
      (DirichletCharacter.zetaMul_nonneg hψ) _
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with ha | ha | ha
  · have hA := charArithmetic_prime_power_eq_one χ hp ha
    have hC := charArithmetic_prime_power_eq_one (χ * ψ) hp
      (by rw [MulChar.mul_apply, ha, zero_mul])
    have he := convolution_prime_power_congr hp
      (convolution_prime_power_congr hp (f₁ := Z) (f₂ := Z) (fun _ => rfl) hA)
      (convolution_prime_power_congr hp (f₁ := B) (f₂ := B) (fun _ => rfl) hC) k
    have he' : biquadraticCoefficients χ ψ (p ^ k) = ψ.zetaMul (p ^ k) := by
      simpa only [biquadraticCoefficients, DirichletCharacter.zetaMul, Z, B,
        mul_one] using he
    rw [he']
    exact DirichletCharacter.zetaMul_nonneg hψ _
  · have hA := charArithmetic_prime_power_eq_zeta χ hp ha
    have hC : ∀ i : ℕ, C (p ^ i) = B (p ^ i) := by
      intro i
      rw [hc (ψ p) (by rw [ha, one_mul]), charArithmetic_prime_power ψ hp]
    have he := convolution_prime_power_congr hp
      (convolution_prime_power_congr hp (f₁ := Z) (f₂ := Z) (fun _ => rfl) hA)
      (convolution_prime_power_congr hp (f₁ := B) (f₂ := B) (fun _ => rfl) hC) k
    have he' : biquadraticCoefficients χ ψ (p ^ k) =
        (ψ.zetaMul * ψ.zetaMul) (p ^ k) := by
      simpa only [biquadraticCoefficients, DirichletCharacter.zetaMul, Z, B, C,
        mul_assoc, mul_comm, mul_left_comm] using he
    rw [he']
    exact hsψ
  · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hψ p with hb | hb | hb
    · have hB := charArithmetic_prime_power_eq_one ψ hp hb
      have hC := charArithmetic_prime_power_eq_one (χ * ψ) hp
        (by rw [MulChar.mul_apply, hb, mul_zero])
      have he := convolution_prime_power_congr hp
        (f₁ := χ.zetaMul) (f₂ := χ.zetaMul) (fun _ => rfl)
        (convolution_prime_power_congr hp hB hC) k
      have he' : biquadraticCoefficients χ ψ (p ^ k) = χ.zetaMul (p ^ k) := by
        simpa only [biquadraticCoefficients, mul_one] using he
      rw [he']
      exact DirichletCharacter.zetaMul_nonneg hχ _
    · have hB := charArithmetic_prime_power_eq_zeta ψ hp hb
      have hC : ∀ i : ℕ, C (p ^ i) = A (p ^ i) := by
        intro i
        rw [hc (χ p) (by rw [hb, mul_one]), charArithmetic_prime_power χ hp]
      have he := convolution_prime_power_congr hp
        (f₁ := χ.zetaMul) (f₂ := χ.zetaMul) (fun _ => rfl)
        (convolution_prime_power_congr hp hB hC) k
      have he' : biquadraticCoefficients χ ψ (p ^ k) =
          (χ.zetaMul * χ.zetaMul) (p ^ k) := by
        simpa only [biquadraticCoefficients, DirichletCharacter.zetaMul, A, C] using he
      rw [he']
      exact hsχ
    · have hB : ∀ i : ℕ, B (p ^ i) = A (p ^ i) := by
        intro i
        rw [charArithmetic_prime_power ψ hp, charArithmetic_prime_power χ hp, ha, hb]
      have hC := charArithmetic_prime_power_eq_zeta (χ * ψ) hp
        (by rw [MulChar.mul_apply, ha, hb]; norm_num)
      have he := convolution_prime_power_congr hp
        (f₁ := χ.zetaMul) (f₂ := χ.zetaMul) (fun _ => rfl)
        (convolution_prime_power_congr hp hB hC) k
      have he' : biquadraticCoefficients χ ψ (p ^ k) =
          (χ.zetaMul * χ.zetaMul) (p ^ k) := by
        simpa only [biquadraticCoefficients, DirichletCharacter.zetaMul, A, B,
          mul_comm] using he
      rw [he']
      exact hsχ

/-- Positivity of the coefficients used in the classical Siegel argument. -/
theorem biquadraticCoefficients_nonneg {q : ℕ}
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (n : ℕ) : 0 ≤ biquadraticCoefficients χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simpa only [(biquadraticCoefficients_isMultiplicative χ ψ).multiplicative_factorization _ hn]
      using! Finset.prod_nonneg fun p hp =>
        biquadraticCoefficients_prime_power_nonneg χ ψ hχ hψ (Nat.prime_of_mem_primeFactors hp) _

end Chen

end

/-! ## ChenTheorem.Lemma6.BiquadraticLSeries -/

section

open ArithmeticFunction
open scoped ComplexOrder

namespace Chen

noncomputable def biquadraticLFunction {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction χ s *
    DirichletCharacter.LFunction ψ s * DirichletCharacter.LFunction (χ * ψ) s

theorem LSeriesSummable_charArithmetic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (toArithmeticFunction (χ ·)) s := by
  exact (LSeriesSummable_congr s (fun hn => χ.apply_eq_toArithmeticFunction_apply hn)).mp
    (ZMod.LSeriesSummable_of_one_lt_re χ hs)

theorem LSeriesSummable_biquadraticCoefficients {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (biquadraticCoefficients χ ψ) s :=
  ArithmeticFunction.LSeriesSummable_mul (χ.LSeriesSummable_zetaMul hs)
    (ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_charArithmetic ψ hs)
      (LSeriesSummable_charArithmetic (χ * ψ) hs))

theorem biquadraticLFunction_eq_LSeries {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    biquadraticLFunction χ ψ s = LSeries (biquadraticCoefficients χ ψ) s := by
  have he (η : DirichletCharacter ℂ q) :
      LSeries (toArithmeticFunction (η ·)) s = DirichletCharacter.LFunction η s := by
    rw [η.LFunction_eq_LSeries hs]
    exact LSeries_congr (fun hn => (η.apply_eq_toArithmeticFunction_apply hn).symm) s
  have hz : LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s = riemannZeta s :=
    LSeries_zeta_eq_riemannZeta hs
  have hfirst : LSeries χ.zetaMul s = riemannZeta s * DirichletCharacter.LFunction χ s := by
    calc
      LSeries χ.zetaMul s =
          LSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s *
            LSeries (toArithmeticFunction (χ ·)) s :=
        ArithmeticFunction.LSeries_mul' (LSeriesSummable_zeta_iff.mpr hs)
          (LSeriesSummable_charArithmetic χ hs)
      _ = _ := congrArg₂ (· * ·) hz (he χ)
  have hsecond : LSeries (toArithmeticFunction (ψ ·) *
      toArithmeticFunction ((χ * ψ) ·) : ArithmeticFunction ℂ) s =
      DirichletCharacter.LFunction ψ s * DirichletCharacter.LFunction (χ * ψ) s := by
    calc
      _ = LSeries (toArithmeticFunction (ψ ·)) s *
          LSeries (toArithmeticFunction ((χ * ψ) ·) : ArithmeticFunction ℂ) s :=
        ArithmeticFunction.LSeries_mul' (LSeriesSummable_charArithmetic ψ hs)
          (LSeriesSummable_charArithmetic (χ * ψ) hs)
      _ = _ := congrArg₂ (· * ·) (he ψ) (he (χ * ψ))
  symm
  calc
    LSeries (biquadraticCoefficients χ ψ) s = LSeries χ.zetaMul s *
        LSeries (toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·) : ArithmeticFunction ℂ) s :=
      ArithmeticFunction.LSeries_mul' (χ.LSeriesSummable_zetaMul hs)
        (ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_charArithmetic ψ hs)
          (LSeriesSummable_charArithmetic (χ * ψ) hs))
    _ = (riemannZeta s * DirichletCharacter.LFunction χ s) *
        (DirichletCharacter.LFunction ψ s * DirichletCharacter.LFunction (χ * ψ) s) :=
      congrArg₂ (· * ·) hfirst hsecond
    _ = biquadraticLFunction χ ψ s := by unfold biquadraticLFunction; ring

theorem biquadraticLFunction_real_ge_one {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (σ : ℝ) (hσ : 1 < σ) : 1 ≤ biquadraticLFunction χ ψ (σ : ℂ) := by
  rw [biquadraticLFunction_eq_LSeries χ ψ (by simpa using hσ)]
  have hs := LSeriesSummable_biquadraticCoefficients χ ψ (s := (σ : ℂ)) (by simpa using hσ)
  have hn (n : ℕ) : 0 ≤ LSeries.term (biquadraticCoefficients χ ψ) (σ : ℂ) n :=
    LSeries.term_nonneg (biquadraticCoefficients_nonneg χ ψ hχ hψ n) σ
  have hone := (biquadraticCoefficients_isMultiplicative χ ψ).map_one
  simpa [LSeries, LSeries.term_def, hone] using hs.le_tsum 1 (fun n _ => hn n)

theorem biquadraticLSeries_iteratedDeriv_alternating {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (σ : ℝ) (hσ : 1 < σ) (n : ℕ) :
    0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n (LSeries (biquadraticCoefficients χ ψ)) (σ : ℂ) := by
  have hab : LSeries.abscissaOfAbsConv (biquadraticCoefficients χ ψ) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun _ hs => LSeriesSummable_biquadraticCoefficients χ ψ hs)
  exact LSeries.iteratedDeriv_alternating (biquadraticCoefficients_nonneg χ ψ hχ hψ)
    (hab.trans_lt (by exact_mod_cast hσ)) n

theorem biquadraticLFunction_iteratedDeriv_alternating {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (σ : ℝ) (hσ : 1 < σ) (n : ℕ) :
    0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n (biquadraticLFunction χ ψ) (σ : ℂ) := by
  have he : Set.EqOn (biquadraticLFunction χ ψ) (LSeries (biquadraticCoefficients χ ψ))
      {s : ℂ | 1 < s.re} := fun _ hs => biquadraticLFunction_eq_LSeries χ ψ hs
  have hopen : IsOpen {s : ℂ | 1 < s.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  rw [he.iteratedDeriv_of_isOpen hopen n (by simpa using hσ)]
  exact biquadraticLSeries_iteratedDeriv_alternating χ ψ hχ hψ σ hσ n

theorem backwardTaylorCoeff_biquadratic_nonneg {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (σ : ℝ) (hσ : 1 < σ) (n : ℕ) :
    0 ≤ backwardTaylorCoeff (biquadraticLFunction χ ψ) (σ : ℂ) n :=
  backwardTaylorCoeff_nonneg_of_alternating
    (biquadraticLFunction_iteratedDeriv_alternating χ ψ hχ hψ σ hσ) n

end Chen

end

/-! ## ChenTheorem.Lemma6.BiquadraticRegularPart -/

section

namespace Chen

noncomputable def biquadraticHolomorphicFactor {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction ψ s *
    DirichletCharacter.LFunction (χ * ψ) s

noncomputable def biquadraticResidue {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) : ℂ := biquadraticHolomorphicFactor χ ψ 1

noncomputable def biquadraticRegularPart {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  regularizedZetaMul (biquadraticHolomorphicFactor χ ψ)

theorem differentiable_biquadraticHolomorphicFactor {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    Differentiable ℂ (biquadraticHolomorphicFactor χ ψ) :=
  ((DirichletCharacter.differentiable_LFunction hχ).mul
    (DirichletCharacter.differentiable_LFunction hψ)).mul
      (DirichletCharacter.differentiable_LFunction hχψ)

theorem differentiable_biquadraticRegularPart {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    Differentiable ℂ (biquadraticRegularPart χ ψ) :=
  differentiable_regularizedZetaMul
    (differentiable_biquadraticHolomorphicFactor χ ψ hχ hψ hχψ)

theorem biquadraticRegularPart_eq {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    biquadraticRegularPart χ ψ s = biquadraticLFunction χ ψ s - biquadraticResidue χ ψ / (s - 1) := by
  rw [biquadraticRegularPart, regularizedZetaMul_eq hs]
  simp only [biquadraticHolomorphicFactor, biquadraticLFunction, biquadraticResidue]
  ring

theorem biquadraticRegularPart_at_zero {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1)
    (hz : DirichletCharacter.LFunction χ s = 0) :
    biquadraticRegularPart χ ψ s = -biquadraticResidue χ ψ / (s - 1) := by
  rw [biquadraticRegularPart_eq χ ψ hs]
  simp only [biquadraticLFunction, hz, mul_zero, zero_mul, zero_sub, neg_div]

end Chen

end

/-! ## ChenTheorem.Lemma6.CauchyHolder -/

section

/-
The fourth-power Cauchy--Hölder estimate used after equation (15).
-/

open MeasureTheory Set Real
open scoped Interval

namespace Chen

/-- Weighted Cauchy--Schwarz in the form used for the `A` term after
equation (17).  The exceptional arithmetic factor `c i` is absorbed into
the first second moment through the pointwise bound `c i ^ 2 ≤ I`. -/
theorem weighted_cauchy_sq_of_sq_le
    {ι : Type*} (s : Finset ι) (w c f g : ι → ℝ) {I : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hI : 0 ≤ I) (hcI : ∀ i ∈ s, c i ^ 2 ≤ I) :
    (∑ i ∈ s, w i * c i * f i * g i) ^ 2 ≤
      (I * ∑ i ∈ s, w i * f i ^ 2) *
        ∑ i ∈ s, w i * g i ^ 2 := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => w i * c i * f i * g i)
    (f := fun i => I * (w i * f i ^ 2))
    (g := fun i => w i * g i ^ 2)
    (fun i hi => mul_nonneg hI (mul_nonneg (hw i hi) (sq_nonneg _)))
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
    (fun i hi => by
      calc
        (w i * c i * f i * g i) ^ 2 =
            c i ^ 2 * (w i ^ 2 * f i ^ 2 * g i ^ 2) := by ring
        _ ≤ I * (w i ^ 2 * f i ^ 2 * g i ^ 2) :=
          mul_le_mul_of_nonneg_right (hcI i hi) (by positivity)
        _ = (I * (w i * f i ^ 2)) * (w i * g i ^ 2) := by ring)
  simpa only [← Finset.mul_sum] using hcs

/-- Weighted three-factor Hölder in the polynomial `2,4,4` form used for
the `B` term after equation (17).  Keeping fourth powers avoids introducing
square roots into the later dyadic estimates. -/
theorem weighted_holder_244_pow_four_of_sq_le
    {ι : Type*} (s : Finset ι) (w c f g h : ι → ℝ) {I : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hh : ∀ i ∈ s, 0 ≤ h i)
    (hI : 0 ≤ I) (hcI : ∀ i ∈ s, c i ^ 2 ≤ I) :
    (∑ i ∈ s, w i * c i * f i * g i * h i) ^ 4 ≤
      (I * ∑ i ∈ s, w i * f i ^ 2) ^ 2 *
        (∑ i ∈ s, w i * g i ^ 4) *
          ∑ i ∈ s, w i * h i ^ 4 := by
  let A : ℝ := ∑ i ∈ s, w i * c i * f i * g i * h i
  let F : ℝ := I * ∑ i ∈ s, w i * f i ^ 2
  let G : ℝ := ∑ i ∈ s, w i * (g i * h i) ^ 2
  let G₄ : ℝ := ∑ i ∈ s, w i * g i ^ 4
  let H₄ : ℝ := ∑ i ∈ s, w i * h i ^ 4
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (hw i hi) (hc i hi)) (hf i hi))
        (hg i hi))
      (hh i hi)
  have hF0 : 0 ≤ F := by
    dsimp only [F]
    exact mul_nonneg hI (Finset.sum_nonneg fun i hi =>
      mul_nonneg (hw i hi) (sq_nonneg _))
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  have hG₄0 : 0 ≤ G₄ := by
    dsimp only [G₄]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hw i hi) (by positivity)
  have hH₄0 : 0 ≤ H₄ := by
    dsimp only [H₄]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hw i hi) (by positivity)
  have hfirst : A ^ 2 ≤ F * G := by
    simpa only [A, F, G, mul_assoc] using
      weighted_cauchy_sq_of_sq_le s w c f (fun i => g i * h i)
        hw hI hcI
  have hsecond : G ^ 2 ≤ G₄ * H₄ := by
    dsimp only [G, G₄, H₄]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (r := fun i => w i * (g i * h i) ^ 2)
      (f := fun i => w i * g i ^ 4)
      (g := fun i => w i * h i ^ 4)
    · intro i hi
      exact mul_nonneg (hw i hi) (by positivity)
    · intro i hi
      exact mul_nonneg (hw i hi) (by positivity)
    · intro i hi
      ring_nf
      exact le_rfl
  change A ^ 4 ≤ F ^ 2 * G₄ * H₄
  calc
    A ^ 4 = (A ^ 2) ^ 2 := by ring
    _ ≤ (F * G) ^ 2 := by gcongr
    _ = F ^ 2 * G ^ 2 := by ring
    _ ≤ F ^ 2 * (G₄ * H₄) := by gcongr
    _ = F ^ 2 * G₄ * H₄ := by ring

/-- Jensen's inequality on an interval of length `2π`, in the exact
fourth-power form needed for Cauchy's formula. -/
theorem intervalIntegral_pow_four_le
    (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t) :
    (∫ t in (0 : ℝ)..2 * Real.pi, g t) ^ 4 ≤
      (2 * Real.pi) ^ 3 *
        ∫ t in (0 : ℝ)..2 * Real.pi, (g t) ^ 4 := by
  let T : ℝ := 2 * Real.pi
  let S : Set ℝ := Set.Ioc 0 T
  have hT : 0 < T := by dsimp only [T]; positivity
  have hSint : IntegrableOn g S := by
    rw [show S = Set.Ioc 0 T by rfl]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
      (hg.intervalIntegrable 0 T)
  have hSfour : IntegrableOn (fun t => (g t) ^ 4) S := by
    rw [show S = Set.Ioc 0 T by rfl]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
      ((hg.pow 4).intervalIntegrable 0 T)
  have hmeasure : volume S = ENNReal.ofReal T := by
    simp [S, Real.volume_Ioc]
  have hmeasure0 : volume S ≠ 0 := by
    rw [hmeasure, ENNReal.ofReal_ne_zero_iff]
    exact hT
  have hmeasureTop : volume S ≠ ⊤ := by
    rw [hmeasure]
    exact ENNReal.ofReal_ne_top
  have hmeasureReal : volume.real S = T := by
    simp [S, Real.volume_real_Ioc_of_le hT.le]
  have hJ := (convexOn_pow 4 :
    ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ 4)).map_set_average_le
      (continuous_pow 4).continuousOn isClosed_Ici hmeasure0 hmeasureTop
      (Filter.Eventually.of_forall fun t => hg0 t) hSint hSfour
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq] at hJ
  rw [hmeasureReal] at hJ
  simp only [smul_eq_mul] at hJ
  rw [intervalIntegral.integral_of_le hT.le,
    intervalIntegral.integral_of_le hT.le]
  change (∫ t in S, g t) ^ 4 ≤ T ^ 3 * ∫ t in S, g t ^ 4
  have hTne : T ≠ 0 := ne_of_gt hT
  field_simp [hTne] at hJ ⊢
  nlinarith

/-- Fourth-power form of Cauchy's estimate, retaining the circle integral
instead of replacing it by a supremum. -/
theorem norm_deriv_pow_four_le_circleIntegral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} {r : ℝ} (hr : 0 < r) :
    ‖deriv f c‖ ^ 4 ≤
      (2 * Real.pi * r ^ 4)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          ‖f (circleMap c r θ)‖ ^ 4 := by
  let g : ℝ → ℝ := fun θ => ‖f (circleMap c r θ)‖
  have hg : Continuous g :=
    hf.continuous.norm.comp (continuous_circleMap c r)
  have hJ := intervalIntegral_pow_four_le g hg
    (fun θ => norm_nonneg _)
  have hcauchy := (hf.differentiableOn).deriv_eq_smul_circleIntegral
    hr (c := c) (R := r)
  have hnorm :
      2 * Real.pi * ‖deriv f c‖ ≤
        ∫ θ in (0 : ℝ)..2 * Real.pi, g θ / r := by
    calc
      2 * Real.pi * ‖deriv f c‖ =
          ‖(2 * Real.pi * Complex.I : ℂ) • deriv f c‖ := by
        simp [Complex.norm_real, Complex.norm_I,
          abs_of_pos Real.pi_pos]
      _ = ‖∮ z in C(c, r), (1 / (z - c) ^ 2) • f z‖ := by
        rw [hcauchy]
      _ ≤ ∫ θ in (0 : ℝ)..2 * Real.pi,
          ‖deriv (circleMap c r) θ •
            ((1 / (circleMap c r θ - c) ^ 2) •
              f (circleMap c r θ))‖ := by
        unfold circleIntegral
        exact intervalIntegral.norm_integral_le_integral_norm
          Real.two_pi_pos.le
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi, g θ / r := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        dsimp only [g]
        simp [deriv_circleMap, circleMap_sub_center,
          norm_pow, norm_circleMap_zero, abs_of_pos hr]
        field_simp [hr.ne']
  rw [intervalIntegral.integral_div] at hnorm
  have hnorm' :
      2 * Real.pi * r * ‖deriv f c‖ ≤
        ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
    calc
      2 * Real.pi * r * ‖deriv f c‖ =
          r * (2 * Real.pi * ‖deriv f c‖) := by ring
      _ ≤ r * ((∫ θ in (0 : ℝ)..2 * Real.pi, g θ) / r) :=
        mul_le_mul_of_nonneg_left hnorm hr.le
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
        field_simp [hr.ne']
  have hpow :
      (2 * Real.pi * r * ‖deriv f c‖) ^ 4 ≤
        (∫ θ in (0 : ℝ)..2 * Real.pi, g θ) ^ 4 := by
    gcongr
  have hcombined := hpow.trans hJ
  let I : ℝ := ∫ θ in (0 : ℝ)..2 * Real.pi, g θ ^ 4
  have hscaled :
      (2 * Real.pi) ^ 3 *
          (‖deriv f c‖ ^ 4 * (2 * Real.pi * r ^ 4)) ≤
        (2 * Real.pi) ^ 3 * I := by
    calc
      (2 * Real.pi) ^ 3 *
          (‖deriv f c‖ ^ 4 * (2 * Real.pi * r ^ 4)) =
        (2 * Real.pi * r * ‖deriv f c‖) ^ 4 := by ring
      _ ≤ (2 * Real.pi) ^ 3 * I := by
        simpa only [I] using hcombined
  have hcancel :
      ‖deriv f c‖ ^ 4 * (2 * Real.pi * r ^ 4) ≤ I :=
    (mul_le_mul_iff_left₀ (pow_pos Real.two_pi_pos 3)).mp (by
      simpa only [mul_comm] using hscaled)
  have hden : 0 < 2 * Real.pi * r ^ 4 := by positivity
  calc
    ‖deriv f c‖ ^ 4 ≤ I / (2 * Real.pi * r ^ 4) :=
      (le_div_iff₀ hden).2 hcancel
    _ = (2 * Real.pi * r ^ 4)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          ‖f (circleMap c r θ)‖ ^ 4 := by
      dsimp only [I, g]
      rw [div_eq_inv_mul]

end Chen

end

/-! ## ChenTheorem.Lemma6.DirichletEulerLogDerivative -/

section

open Set Metric

namespace Chen

noncomputable def dirichletEulerFactor {d : ℕ} (χ : DirichletCharacter ℂ d)
    (p : ℕ) (s : ℂ) : ℂ := 1 - χ p * (p : ℂ) ^ (-s)

theorem norm_dirichletEulerTerm_le_inv {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ 1 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [norm_mul, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < p), Complex.neg_re]
  calc
    _ ≤ 1 * (p : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (χ.norm_le_one p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ ≤ (p : ℝ) ^ (-1 : ℝ) := by
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = _ := by rw [Real.rpow_neg_one, one_div]

theorem norm_dirichletEulerTerm_le_half {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  apply (norm_dirichletEulerTerm_le_inv χ hp s hs).trans
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp)

theorem dirichletEulerFactor_ne_zero {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) : dirichletEulerFactor χ p s ≠ 0 := by
  have h := norm_dirichletEulerTerm_le_half χ hp s hs
  intro he
  have he' : χ p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp he).symm
  rw [he', norm_one] at h
  norm_num at h

theorem hasDerivAt_dirichletEulerFactor {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : p ≠ 0) (s : ℂ) :
    HasDerivAt (dirichletEulerFactor χ p)
      (χ p * (p : ℂ) ^ (-s) * Complex.log p) s := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hpow := (hasDerivAt_id s).neg.const_cpow (c := (p : ℂ)) (Or.inl hpC)
  have h := (hpow.const_mul (χ p)).const_sub 1
  change HasDerivAt (dirichletEulerFactor χ p)
    (-(χ p * ((p : ℂ) ^ (-s) * Complex.log p * (-1)))) s at h
  convert h using 1
  ring

theorem norm_deriv_dirichletEulerFactor {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : 2 ≤ p) (s : ℂ) :
    ‖deriv (dirichletEulerFactor χ p) s‖ = Real.log p * ‖χ p * (p : ℂ) ^ (-s)‖ := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p),
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith))]
  rw [(hasDerivAt_dirichletEulerFactor χ (by omega) s).deriv, norm_mul, hlog, mul_comm]

theorem norm_logDeriv_dirichletEulerFactor_le {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖logDeriv (dirichletEulerFactor χ p) s‖ ≤ Real.log p := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hterm := norm_dirichletEulerTerm_le_half χ hp s hs
  have hden := norm_sub_norm_le (1 : ℂ) (χ p * (p : ℂ) ^ (-s))
  rw [norm_one] at hden
  change 1 - ‖χ p * (p : ℂ) ^ (-s)‖ ≤ ‖dirichletEulerFactor χ p s‖ at hden
  rw [logDeriv_apply, norm_div, norm_deriv_dirichletEulerFactor χ hp s]
  apply (div_le_iff₀ (norm_pos_iff.mpr (dirichletEulerFactor_ne_zero χ hp s hs))).mpr
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.log_nonneg (by linarith))

theorem sum_log_primeFactors_le_log (q : ℕ) (hq : 0 < q) :
    ∑ p ∈ q.primeFactors, Real.log (p : ℝ) ≤ Real.log q := by
  have hp : ∀ p ∈ q.primeFactors, (0 : ℝ) < p := by
    intro p hp
    exact_mod_cast Nat.pos_of_mem_primeFactors hp
  have hprod : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ q := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  rw [← Real.log_prod (fun p h => (hp p h).ne')]
  exact Real.log_le_log (Finset.prod_pos hp) hprod

theorem norm_logDeriv_dirichletEulerProduct_le {d : ℕ} (χ : DirichletCharacter ℂ d)
    (q : ℕ) (hq : 0 < q) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖logDeriv (fun z => ∏ p ∈ q.primeFactors, dirichletEulerFactor χ p z) s‖ ≤ Real.log q := by
  rw [logDeriv_fun_prod (s := q.primeFactors) (f := fun p z => dirichletEulerFactor χ p z) (x := s)
    (fun p hp => dirichletEulerFactor_ne_zero χ (Nat.prime_of_mem_primeFactors hp).two_le s hs)
    (fun p hp => (hasDerivAt_dirichletEulerFactor χ (Nat.pos_of_mem_primeFactors hp).ne' s).differentiableAt)]
  apply (norm_sum_le _ _).trans
  apply le_trans _ (sum_log_primeFactors_le_log q hq)
  exact Finset.sum_le_sum (fun p hp => norm_logDeriv_dirichletEulerFactor_le χ
    (Nat.prime_of_mem_primeFactors hp).two_le s hs)

end Chen

end

/-! ## ChenTheorem.Lemma6.DirichletPhase -/

section

namespace Chen

noncomputable def dirichletPhase (n : ℕ) (t : ℝ) : ℂ :=
  (n : ℂ) ^ (-((t : ℂ) * Complex.I))

theorem norm_dirichletPhase (n : ℕ) (hn : n ≠ 0) (t : ℝ) : ‖dirichletPhase n t‖ = 1 := by
  unfold dirichletPhase
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < n)]
  simp
theorem dirichletPhase_twice (n : ℕ) (t : ℝ) : dirichletPhase n (2 * t) = dirichletPhase n t ^ 2 := by
  unfold dirichletPhase
  rw [show -(((2 * t : ℝ) : ℂ) * Complex.I) = (-((t : ℂ) * Complex.I)) * (2 : ℕ) by push_cast; ring]
  exact Complex.cpow_mul_nat _ _ 2
theorem real_part_trigonometric_polynomial_nonneg (z : ℂ) (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hn := Complex.sq_norm z
  rw [Complex.normSq_apply] at hn
  rw [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg (z.re + 1), norm_nonneg z]
/-- Separating the real decay from the vertical phase in a twisted von
Mangoldt series term. -/
theorem vonMangoldt_twist_term_phase {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))
      ((σ : ℂ) + (t : ℂ) * Complex.I) n =
      ((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        (χ n * dirichletPhase n t) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
    show -((σ : ℂ) + (t : ℂ) * Complex.I) = -(σ : ℂ) + -((t : ℂ) * Complex.I) by ring,
    Complex.cpow_add _ _ hnC]
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg, Complex.ofReal_natCast]
  unfold dirichletPhase
  ring
theorem vonMangoldt_term_real (σ : ℝ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) n =
      ((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow (Nat.cast_nonneg n) σ, ← Complex.ofReal_div,
    Real.rpow_neg (Nat.cast_nonneg n)]
  congr 1

end Chen

end

