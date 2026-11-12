module

public import Green64.Library.Sieve.Foundation.Lemma9.Part003

@[expose] public section

/-!
# Sieve / Foundation / Lemma9 / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.Lemma9.BombieriVinogradov.SmallConductorSmoothing -/

section

open Filter Real
open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Adjustable smoothing for the small-conductor range

The fixed smoothing parameter used in Lemma 6 has transition width
`(log x)^(-1/10)`, which is not enough for the arbitrary logarithmic saving
in Bombieri--Vinogradov.  We do not need a second Mellin-inversion proof:
the existing function `Chen.chenPhi R` accepts an arbitrary positive real
parameter `R`.  Taking

`R = exp ((log x) ^ (10 * (K + 1)))`

makes its transition width `(log x)^(-(K+1))`, while retaining the same
high-order rational Mellin kernel already formalized for Lemma 6.
-/

/-- Auxiliary real parameter fed to Chen's existing smoothing function. -/
noncomputable def bvSmoothingParameter (K x : ℕ) : ℝ :=
  Real.exp (Real.log (x : ℝ) ^ (10 * (K + 1)))

theorem log_bvSmoothingParameter (K x : ℕ) :
    Real.log (bvSmoothingParameter K x) =
      Real.log (x : ℝ) ^ (10 * (K + 1)) := by
  unfold bvSmoothingParameter
  rw [Real.log_exp]

theorem one_lt_bvSmoothingParameter
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x) :
    1 < bvSmoothingParameter K x := by
  rw [bvSmoothingParameter, Real.one_lt_exp_iff]
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  exact pow_pos hlog _

/-- The `-1/10` transition exponent of Chen's smoothing function becomes
the freely chosen logarithmic exponent `-(K+1)`. -/
theorem log_bvSmoothingParameter_rpow_neg_tenth
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x) :
    Real.log (bvSmoothingParameter K x) ^ (-(0.1 : ℝ)) =
      Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) := by
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  rw [log_bvSmoothingParameter]
  calc
    (Real.log (x : ℝ) ^ (10 * (K + 1))) ^ (-(0.1 : ℝ)) =
        (Real.log (x : ℝ) ^ ((10 * (K + 1) : ℕ) : ℝ)) ^
          (-(0.1 : ℝ)) := by
            rw [Real.rpow_natCast]
    _ = Real.log (x : ℝ) ^
          (((10 * (K + 1) : ℕ) : ℝ) * (-(0.1 : ℝ))) :=
      (Real.rpow_mul hlog.le _ _).symm
    _ = Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) := by
      congr 1
      push_cast
      norm_num
      ring

/-- The adjustable cutoff attached to the summand indexed by `n`. -/
noncomputable def bvSmoothingWeight (K x n : ℕ) : ℝ :=
  Chen.chenPhi (bvSmoothingParameter K x) ((x : ℝ) / (n : ℝ))

/-- Multiplicative transition width of the adjustable smoothing. -/
noncomputable def bvSmoothingBoundaryRatio (K x : ℕ) : ℝ :=
  Real.exp (2 * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)))

/-- Polylogarithmic contour height chosen as the square of the adjustable
Mellin scale. -/
noncomputable def bvSmoothingContourHeight (K x : ℕ) : ℝ :=
  (Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2

theorem bvSmoothingContourHeight_nonneg (K x : ℕ) :
    0 ≤ bvSmoothingContourHeight K x := by
  unfold bvSmoothingContourHeight
  positivity

/-- Indices in the short interval next to `x` on which Lemma 1 does not
yet force the smoothing weight to be power-close to one. -/
noncomputable def bvSmoothingBoundaryIndices (K x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun n =>
    (x : ℝ) / (n : ℝ) < bvSmoothingBoundaryRatio K x

@[simp]
theorem mem_bvSmoothingBoundaryIndices {K x n : ℕ} :
    n ∈ bvSmoothingBoundaryIndices K x ↔
      n ∈ Finset.Icc 1 x ∧
        (x : ℝ) / (n : ℝ) < bvSmoothingBoundaryRatio K x := by
  simp [bvSmoothingBoundaryIndices]

/-- Smoothed twisted Chebyshev sum.  The finite range is retained here so
that approximation to the original sharp sum is purely algebraic. -/
noncomputable def bvSmoothedTwistedPsi {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
      (bvSmoothingWeight K x n : ℂ)

/-- Finite Mellin integrand whose vertical integral is the adjustable
smoothed twisted Chebyshev sum. -/
noncomputable def bvSmoothedTwistedPsiFiniteIntegrand {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
      (((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^ s) *
        Chen.lemma6SmoothingMellinKernel
          (bvSmoothingParameter K x) s)

theorem bvSmoothingWeight_nonneg
    (K : ℕ) {x n : ℕ} (hx : 2 ≤ x) :
    0 ≤ bvSmoothingWeight K x n := by
  unfold bvSmoothingWeight
  exact Chen.chenPhi_nonneg _ (one_lt_bvSmoothingParameter K hx)
    (by positivity)

theorem bvSmoothingWeight_le_one
    (K : ℕ) {x n : ℕ} (hx : 2 ≤ x) :
    bvSmoothingWeight K x n ≤ 1 := by
  unfold bvSmoothingWeight
  exact Chen.chenPhi_le_one _ (one_lt_bvSmoothingParameter K hx)
    (by positivity)

/-- At and to the right of the sharp endpoint the adjustable weight is
identically zero. -/
theorem bvSmoothingWeight_eq_zero_of_le
    (K : ℕ) {x n : ℕ} (hx : 2 ≤ x) (hn : 1 ≤ n) (hxn : x ≤ n) :
    bvSmoothingWeight K x n = 0 := by
  unfold bvSmoothingWeight
  apply Chen.chenPhi_eq_zero (one_lt_bvSmoothingParameter K hx)
  · positivity
  · exact (div_le_one (by exact_mod_cast (show 0 < n by omega))).2
      (by exact_mod_cast hxn)

theorem bvSmoothingScale_pos
    (K : ℕ) {x : ℕ}
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1))) :
    0 < Chen.lemma6SmoothingScale (bvSmoothingParameter K x) := by
  have hlogR : 1 ≤ Real.log (bvSmoothingParameter K x) := by
    rw [log_bvSmoothingParameter]
    exact (by norm_num : (1 : ℝ) ≤ 10 ^ 4).trans hlarge
  unfold Chen.lemma6SmoothingScale
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlogR) _

theorem bvSmoothingOrder_one_le
    (K : ℕ) {x : ℕ}
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1))) :
    1 ≤ Chen.lemma6SmoothingOrder (bvSmoothingParameter K x) := by
  have hlogR : 1 ≤ Real.log (bvSmoothingParameter K x) := by
    rw [log_bvSmoothingParameter]
    exact (by norm_num : (1 : ℝ) ≤ 10 ^ 4).trans hlarge
  unfold Chen.lemma6SmoothingOrder
  rw [Nat.one_le_floor_iff]
  exact hlogR

/-- The Mellin scale attached to the adjustable parameter is still a
plain power of `log x`; its exponent is `11 * (K+1)`. -/
theorem bvSmoothingScale_eq
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x) :
    Chen.lemma6SmoothingScale (bvSmoothingParameter K x) =
      Real.log (x : ℝ) ^ (11 * (K + 1)) := by
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  unfold Chen.lemma6SmoothingScale
  rw [log_bvSmoothingParameter]
  calc
    (Real.log (x : ℝ) ^ (10 * (K + 1))) ^ (1.1 : ℝ) =
        (Real.log (x : ℝ) ^ ((10 * (K + 1) : ℕ) : ℝ)) ^
          (1.1 : ℝ) := by rw [Real.rpow_natCast]
    _ = Real.log (x : ℝ) ^
          (((10 * (K + 1) : ℕ) : ℝ) * (1.1 : ℝ)) :=
      (Real.rpow_mul hlog.le _ _).symm
    _ = Real.log (x : ℝ) ^ (((11 * (K + 1) : ℕ) : ℝ)) := by
      congr 1
      push_cast
      norm_num
      ring
    _ = Real.log (x : ℝ) ^ (11 * (K + 1)) :=
      Real.rpow_natCast _ _

theorem bvSmoothingOrder_three_le
    (K : ℕ) {x : ℕ}
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1))) :
    3 ≤ Chen.lemma6SmoothingOrder (bvSmoothingParameter K x) := by
  have hlogR : (3 : ℝ) ≤ Real.log (bvSmoothingParameter K x) := by
    rw [log_bvSmoothingParameter]
    exact (by norm_num : (3 : ℝ) ≤ 10 ^ 4).trans hlarge
  unfold Chen.lemma6SmoothingOrder
  exact (Nat.le_floor_iff (show 0 ≤
    Real.log (bvSmoothingParameter K x) by linarith)).2 hlogR

/-- Quartic tail bound for the adjustable Mellin kernel, with its scale
displayed as a power of `log x`. -/
theorem norm_bvSmoothingMellinKernel_le_quartic
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    {σ : ℝ} (hσ : 0 < σ) (ν : ℝ) :
    ‖Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x)
        ((σ : ℂ) + (ν : ℂ) * Complex.I)‖ ≤
      σ⁻¹ *
        ((1 + (ν / Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ := by
  simpa only [bvSmoothingScale_eq K hx] using
    (Chen.norm_lemma6SmoothingMellinKernel_le_quartic
      (bvSmoothingScale_pos K hlarge)
      (bvSmoothingOrder_three_le K hlarge) hσ ν)

/-- Mellin inversion for the adjustable weight.  This is a direct
specialization of the smoothing theorem already proved for Lemma 6, with
its parameter replaced by `bvSmoothingParameter K x`. -/
theorem bvSmoothingWeight_eq_smoothing_verticalIntegral
    (K : ℕ) {x n : ℕ} (hx : 2 ≤ x) (hn : 1 ≤ n)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (σ : ℝ) (hσ : 0 < σ) :
    (bvSmoothingWeight K x n : ℂ) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ ν : ℝ,
          ((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^
              ((σ : ℂ) + (ν : ℂ) * Complex.I) *
            Chen.lemma6SmoothingMellinKernel
              (bvSmoothingParameter K x)
              ((σ : ℂ) + (ν : ℂ) * Complex.I)) := by
  have hy : 0 < (x : ℝ) / (n : ℝ) := by
    positivity
  unfold bvSmoothingWeight
  simpa only using
    (Chen.chenPhi_eq_smoothing_verticalIntegral
      (one_lt_bvSmoothingParameter K hx)
      (bvSmoothingScale_pos K hlarge)
      (bvSmoothingOrder_one_le K hlarge) hσ hy)

/-- Exact finite Mellin representation of the adjustable smoothed sum.
This is the bridge from the elementary smoothing-error estimates below to
the later logarithmic-derivative contour argument. -/
theorem bvSmoothedTwistedPsi_eq_finiteVerticalIntegral
    {q : ℕ} (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) (σ : ℝ) (hσ : 0 < σ) :
    bvSmoothedTwistedPsi K x χ =
      VerticalIntegral' (bvSmoothedTwistedPsiFiniteIntegrand K x χ) σ := by
  have hterm (n : ℕ) (hnmem : n ∈ Finset.Icc 1 x) :
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (bvSmoothingWeight K x n : ℂ) =
        VerticalIntegral' (fun s : ℂ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
            (((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^ s) *
              Chen.lemma6SmoothingMellinKernel
                (bvSmoothingParameter K x) s)) σ := by
    have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
    rw [bvSmoothingWeight_eq_smoothing_verticalIntegral
      K hx hn hlarge σ hσ]
    unfold VerticalIntegral' VerticalIntegral
    simp only [smul_eq_mul, Complex.real_smul]
    rw [MeasureTheory.integral_const_mul]
    push_cast
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
    simp only [mul_comm]
  unfold bvSmoothedTwistedPsi
  calc
    (∑ n ∈ Finset.Icc 1 x,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (bvSmoothingWeight K x n : ℂ)) =
      ∑ n ∈ Finset.Icc 1 x,
        VerticalIntegral' (fun s : ℂ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
            (((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^ s) *
              Chen.lemma6SmoothingMellinKernel
                (bvSmoothingParameter K x) s)) σ :=
      Finset.sum_congr rfl hterm
    _ = VerticalIntegral'
        (bvSmoothedTwistedPsiFiniteIntegrand K x χ) σ := by
      unfold bvSmoothedTwistedPsiFiniteIntegrand
      unfold VerticalIntegral' VerticalIntegral
      simp only [smul_eq_mul]
      rw [MeasureTheory.integral_finsetSum]
      · simp only [Finset.mul_sum]
      · intro n hnmem
        have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
        have hy : 0 < (x : ℝ) / (n : ℝ) := by positivity
        exact (Chen.integrable_cpow_mul_lemma6SmoothingMellinKernel
          hy (bvSmoothingScale_pos K hlarge)
          (bvSmoothingOrder_one_le K hlarge) hσ).const_mul _

/-- Exact algebraic form of the smoothing error. -/
theorem twistedPsi_sub_bvSmoothedTwistedPsi {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) :
    twistedPsi x χ - bvSmoothedTwistedPsi K x χ =
      ∑ n ∈ Finset.Icc 1 x,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (1 - bvSmoothingWeight K x n : ℂ) := by
  unfold twistedPsi bvSmoothedTwistedPsi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The character contributes no loss to the elementary smoothing error. -/
theorem norm_twistedPsi_sub_bvSmoothedTwistedPsi_le {q : ℕ}
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (χ : DirichletCharacter ℂ q) :
    ‖twistedPsi x χ - bvSmoothedTwistedPsi K x χ‖ ≤
      ∑ n ∈ Finset.Icc 1 x,
        ArithmeticFunction.vonMangoldt n *
          (1 - bvSmoothingWeight K x n) := by
  rw [twistedPsi_sub_bvSmoothedTwistedPsi]
  calc
    ‖∑ n ∈ Finset.Icc 1 x,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (1 - bvSmoothingWeight K x n : ℂ)‖ ≤
      ∑ n ∈ Finset.Icc 1 x,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
          (1 - bvSmoothingWeight K x n : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 x,
        ArithmeticFunction.vonMangoldt n *
          (1 - bvSmoothingWeight K x n) := by
      apply Finset.sum_le_sum
      intro n _
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have hw0 := bvSmoothingWeight_nonneg K hx (n := n)
      have hw1 := bvSmoothingWeight_le_one K hx (n := n)
      have hΛnorm : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
          ArithmeticFunction.vonMangoldt n := by
        rw [Complex.norm_real, Real.norm_of_nonneg hΛ]
      have hwnorm : ‖(1 - bvSmoothingWeight K x n : ℂ)‖ =
          1 - bvSmoothingWeight K x n := by
        rw [show (1 - bvSmoothingWeight K x n : ℂ) =
          ((1 - bvSmoothingWeight K x n : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real,
          Real.norm_of_nonneg (sub_nonneg.mpr hw1)]
      rw [norm_mul, norm_mul, hΛnorm, hwnorm]
      calc
        ArithmeticFunction.vonMangoldt n * ‖χ n‖ *
            (1 - bvSmoothingWeight K x n) ≤
          ArithmeticFunction.vonMangoldt n * 1 *
            (1 - bvSmoothingWeight K x n) := by
              gcongr
              exact χ.norm_le_one n
        _ = _ := by ring

/-- In the deep interior, Lemma 1 gives a power-small smoothing error.
The later asymptotic layer rewrites the displayed threshold in terms of
`(log x)^(-(K+1))`. -/
theorem one_sub_bvSmoothingWeight_le
    (K : ℕ) {x n : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (bvSmoothingParameter K x))
    (hdeep : Real.exp
        (2 * Real.log (bvSmoothingParameter K x) ^ (-(0.1 : ℝ))) ≤
      (x : ℝ) / (n : ℝ)) :
    1 - bvSmoothingWeight K x n ≤
      bvSmoothingParameter K x ^ (-(0.1 : ℝ)) := by
  unfold bvSmoothingWeight
  have hphi := Chen.chenPhi_ge
    (one_lt_bvSmoothingParameter K hx) hlarge hdeep
  linarith

/-- Same interior estimate with the transition width displayed directly
as the chosen power of `log x`. -/
theorem one_sub_bvSmoothingWeight_le_log_width
    (K : ℕ) {x n : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hdeep : Real.exp
        (2 * Real.log (x : ℝ) ^ (-(K + 1 : ℝ))) ≤
      (x : ℝ) / (n : ℝ)) :
    1 - bvSmoothingWeight K x n ≤
      bvSmoothingParameter K x ^ (-(0.1 : ℝ)) := by
  apply one_sub_bvSmoothingWeight_le K hx
  · rwa [log_bvSmoothingParameter]
  · rwa [log_bvSmoothingParameter_rpow_neg_tenth K hx]

/-- Quantitative smoothing-error split.  The deep part costs the tiny
power `R^(-1/10)` times `ψ(x)`; all remaining loss is confined to the
explicit short boundary interval. -/
theorem norm_twistedPsi_sub_bvSmoothedTwistedPsi_le_deep_add_boundary
    {q : ℕ} (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    ‖twistedPsi x χ - bvSmoothedTwistedPsi K x χ‖ ≤
      bvSmoothingParameter K x ^ (-(0.1 : ℝ)) * Chebyshev.psi x +
        ((bvSmoothingBoundaryIndices K x).card : ℝ) *
          Real.log (x : ℝ) := by
  let Rerr : ℝ := bvSmoothingParameter K x ^ (-(0.1 : ℝ))
  let L : ℝ := Real.log (x : ℝ)
  let S : Finset ℕ := Finset.Icc 1 x
  let B : Finset ℕ := bvSmoothingBoundaryIndices K x
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hR0 : 0 ≤ Rerr := by
    dsimp only [Rerr]
    exact Real.rpow_nonneg (Real.exp_pos _).le _
  have hpoint : ∀ n ∈ S,
      ArithmeticFunction.vonMangoldt n *
          (1 - bvSmoothingWeight K x n) ≤
        ArithmeticFunction.vonMangoldt n * Rerr +
          if n ∈ B then L else 0 := by
    intro n hn
    have hnData := Finset.mem_Icc.mp hn
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hΛL : ArithmeticFunction.vonMangoldt n ≤ L := by
      dsimp only [L]
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
          (by exact_mod_cast hnData.2))
    by_cases hdeep : bvSmoothingBoundaryRatio K x ≤
        (x : ℝ) / (n : ℝ)
    · have herr : 1 - bvSmoothingWeight K x n ≤ Rerr := by
        dsimp only [Rerr]
        apply one_sub_bvSmoothingWeight_le_log_width K hx hlarge
        simpa only [bvSmoothingBoundaryRatio] using hdeep
      have hnB : n ∉ B := by
        dsimp only [B]
        rw [mem_bvSmoothingBoundaryIndices]
        exact fun h => (not_lt_of_ge hdeep) h.2
      rw [if_neg hnB, add_zero]
      exact mul_le_mul_of_nonneg_left herr hΛ0
    · have hnB : n ∈ B := by
        dsimp only [B]
        rw [mem_bvSmoothingBoundaryIndices]
        exact ⟨hn, lt_of_not_ge hdeep⟩
      rw [if_pos hnB]
      have hw0 := bvSmoothingWeight_nonneg K hx (n := n)
      have hone : 1 - bvSmoothingWeight K x n ≤ 1 := by linarith
      calc
        ArithmeticFunction.vonMangoldt n *
              (1 - bvSmoothingWeight K x n) ≤
            ArithmeticFunction.vonMangoldt n * 1 :=
          mul_le_mul_of_nonneg_left hone hΛ0
        _ ≤ ArithmeticFunction.vonMangoldt n * Rerr + L := by
          nlinarith [mul_nonneg hΛ0 hR0]
  have hbase := norm_twistedPsi_sub_bvSmoothedTwistedPsi_le K hx χ
  calc
    ‖twistedPsi x χ - bvSmoothedTwistedPsi K x χ‖ ≤
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n *
          (1 - bvSmoothingWeight K x n) := by
            simpa only [S] using hbase
    _ ≤ ∑ n ∈ S,
        (ArithmeticFunction.vonMangoldt n * Rerr +
          if n ∈ B then L else 0) := Finset.sum_le_sum hpoint
    _ = Rerr * Chebyshev.psi x + (B.card : ℝ) * L := by
      rw [Finset.sum_add_distrib]
      have hpsi : (∑ n ∈ S, ArithmeticFunction.vonMangoldt n) =
          Chebyshev.psi x := by
        dsimp only [S]
        rw [Chebyshev.psi_eq_sum_Icc]
        simp only [Nat.floor_natCast]
        apply Finset.sum_subset
        · intro n hn
          exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hn).2⟩
        · intro n hn hnnot
          have hnData := Finset.mem_Icc.mp hn
          have hn0 : n = 0 := by
            by_contra hnne
            exact hnnot (Finset.mem_Icc.mpr
              ⟨Nat.one_le_iff_ne_zero.mpr hnne, hnData.2⟩)
          subst n
          simp
      rw [← Finset.sum_mul, hpsi]
      have hBsub : B ⊆ S := by
        intro n hn
        dsimp only [B, S] at hn ⊢
        exact (mem_bvSmoothingBoundaryIndices.mp hn).1
      have hboundary :
          (∑ n ∈ S, if n ∈ B then L else 0) = (B.card : ℝ) * L := by
        calc
          (∑ n ∈ S, if n ∈ B then L else 0) =
              ∑ n ∈ B, if n ∈ B then L else 0 := by
            symm
            apply Finset.sum_subset hBsub
            intro n _ hnB
            rw [if_neg hnB]
          _ = (B.card : ℝ) * L := by simp
      rw [hboundary]
      ring
    _ = _ := by rfl

/-- The transition layer next to `x` contains only
`O(x * (log x)^(-(K+1)))` integers.  This is the elementary counting
estimate which turns the pointwise smoothing estimate into an arbitrary
logarithmic saving. -/
theorem card_bvSmoothingBoundaryIndices_le
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x) :
    ((bvSmoothingBoundaryIndices K x).card : ℝ) ≤
      2 * (x : ℝ) * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) + 1 := by
  let δ : ℝ := Real.log (x : ℝ) ^ (-(K + 1 : ℝ))
  let R : ℝ := Real.exp (2 * δ)
  let a : ℕ := ⌊(x : ℝ) / R⌋₊
  have hx0 : 0 ≤ (x : ℝ) := by positivity
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    exact Real.rpow_nonneg (Real.log_pos
      (by exact_mod_cast (show 1 < x by omega))).le _
  have hRpos : 0 < R := by
    dsimp only [R]
    positivity
  have hRone : 1 ≤ R := by
    dsimp only [R]
    exact Real.one_le_exp (by positivity)
  have hquot0 : 0 ≤ (x : ℝ) / R := div_nonneg hx0 hRpos.le
  have hquotx : (x : ℝ) / R ≤ x := div_le_self hx0 hRone
  have hax : a ≤ x := by
    dsimp only [a]
    exact Nat.floor_le_of_le hquotx
  have hsubset : bvSmoothingBoundaryIndices K x ⊆ Finset.Ioc a x := by
    intro n hn
    have hnData := mem_bvSmoothingBoundaryIndices.mp hn
    have hnIcc := Finset.mem_Icc.mp hnData.1
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    have hratio : (x : ℝ) / (n : ℝ) < R := by
      simpa only [R, bvSmoothingBoundaryRatio, δ] using hnData.2
    have hxlt : (x : ℝ) < R * (n : ℝ) :=
      (div_lt_iff₀ hnpos).mp hratio
    have hquotlt : (x : ℝ) / R < n := by
      apply (div_lt_iff₀ hRpos).2
      simpa only [mul_comm] using hxlt
    exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hquot0).2 hquotlt, hnIcc.2⟩
  have hcardNat := Finset.card_le_card hsubset
  have hcard : ((bvSmoothingBoundaryIndices K x).card : ℝ) ≤
      ((Finset.Ioc a x).card : ℝ) := by exact_mod_cast hcardNat
  rw [Nat.card_Ioc, Nat.cast_sub hax] at hcard
  have hfloor : (x : ℝ) / R < (a : ℝ) + 1 := by
    dsimp only [a]
    exact Nat.lt_floor_add_one _
  have hcount : (x : ℝ) - (a : ℝ) ≤ (x : ℝ) - (x : ℝ) / R + 1 := by
    linarith
  have hexp : 1 - Real.exp (-2 * δ) ≤ 2 * δ := by
    have := Real.add_one_le_exp (-2 * δ)
    linarith
  have hRinv : R⁻¹ = Real.exp (-2 * δ) := by
    dsimp only [R]
    rw [← Real.exp_neg]
    congr 1
    ring
  have hlast : (x : ℝ) - (x : ℝ) / R + 1 ≤
      2 * (x : ℝ) * δ + 1 := by
    rw [div_eq_mul_inv, hRinv]
    have hmul := mul_le_mul_of_nonneg_left hexp hx0
    nlinarith
  exact hcard.trans (hcount.trans (by simpa only [δ] using hlast))

/-- Fully explicit adjustable smoothing error.  Its first term is
super-polynomially small in `log x`, while the second is visibly of size
`x * (log x)^(-K)` after multiplication by the endpoint logarithm. -/
theorem norm_twistedPsi_sub_bvSmoothedTwistedPsi_le_explicit
    {q : ℕ} (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    ‖twistedPsi x χ - bvSmoothedTwistedPsi K x χ‖ ≤
      bvSmoothingParameter K x ^ (-(0.1 : ℝ)) * Chebyshev.psi x +
        (2 * (x : ℝ) * Real.log (x : ℝ) ^ (-(K + 1 : ℝ)) + 1) *
          Real.log (x : ℝ) := by
  have hsplit :=
    norm_twistedPsi_sub_bvSmoothedTwistedPsi_le_deep_add_boundary
      K hx hlarge χ
  have hlog0 : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  exact hsplit.trans (add_le_add_right
    (mul_le_mul_of_nonneg_right
      (card_bvSmoothingBoundaryIndices_le K hx) hlog0) _)

/-- Exact mass of the Cauchy envelope after rescaling its horizontal
variable. -/
theorem integral_scaled_cauchy
    {a : ℝ} (ha : 0 < a) :
    (∫ ν : ℝ, (1 + (ν / a) ^ 2)⁻¹) = a * Real.pi := by
  let g : ℝ → ℝ := fun u => (1 + u ^ 2)⁻¹
  have hscale :=
    MeasureTheory.Measure.integral_comp_mul_left g a⁻¹
  calc
    (∫ ν : ℝ, (1 + (ν / a) ^ 2)⁻¹) =
        ∫ ν : ℝ, g (a⁻¹ * ν) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ν
      dsimp only [g]
      rw [div_eq_inv_mul]
    _ = |(a⁻¹)⁻¹| * ∫ u : ℝ, g u := by
      simpa only [smul_eq_mul] using hscale
    _ = a * Real.pi := by
      rw [integral_univ_inv_one_add_sq]
      simp only [inv_inv, abs_of_pos ha]

theorem integrable_scaled_quartic
    {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun ν : ℝ =>
      ((1 + (ν / a) ^ 2) ^ 2)⁻¹) := by
  let h : ℝ → ℝ := fun ν => (1 + (ν / a) ^ 2)⁻¹
  have hh : MeasureTheory.Integrable h := by
    have hbase := integrable_inv_one_add_sq.comp_mul_left'
      (R := a⁻¹) (inv_ne_zero ha.ne')
    simpa only [h, div_eq_inv_mul] using hbase
  apply hh.mono
  · fun_prop
  · filter_upwards with ν
    have hu : 1 ≤ 1 + (ν / a) ^ 2 := by nlinarith [sq_nonneg (ν / a)]
    have huPos : 0 < 1 + (ν / a) ^ 2 := by positivity
    rw [Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by dsimp only [h]; positivity)]
    dsimp only [h]
    rw [pow_two, mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr huPos.le)
      (inv_le_one_of_one_le₀ hu)

/-- The quartic scaled kernel outside `[-T,T]` is bounded by one frozen
decay factor times the total mass of a scaled Cauchy kernel. -/
theorem integral_scaled_quartic_compl_Ioc_le
    {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    (∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ,
        ((1 + (ν / a) ^ 2) ^ 2)⁻¹) ≤
      ((1 + (T / a) ^ 2)⁻¹) * (a * Real.pi) := by
  let g : ℝ → ℝ := fun ν => ((1 + (ν / a) ^ 2) ^ 2)⁻¹
  let h : ℝ → ℝ := fun ν => (1 + (ν / a) ^ 2)⁻¹
  let E : ℝ := (1 + (T / a) ^ 2)⁻¹
  have ha0 : a ≠ 0 := ha.ne'
  have hh : MeasureTheory.Integrable h := by
    have hbase := integrable_inv_one_add_sq.comp_mul_left'
      (R := a⁻¹) (inv_ne_zero ha0)
    simpa only [h, div_eq_inv_mul] using hbase
  have hg : MeasureTheory.Integrable g := by
    simpa only [g] using integrable_scaled_quartic ha
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hmajor : MeasureTheory.Integrable (fun ν => E * h ν) :=
    hh.const_mul E
  have hpoint : ∀ ν ∈ (Set.Ioc (-T) T)ᶜ, g ν ≤ E * h ν := by
    intro ν hνmem
    have hνlarge : T ≤ |ν| := by
      rw [Set.mem_compl_iff, Set.mem_Ioc] at hνmem
      by_cases hleft : ν ≤ -T
      · have : T ≤ -ν := by linarith
        exact this.trans_eq (abs_of_nonpos (by linarith)).symm
      · have hright : T < ν := by
          by_contra hnot
          exact hνmem ⟨lt_of_not_ge hleft, le_of_not_gt hnot⟩
        exact hright.le.trans (le_abs_self ν)
    have hsq : T ^ 2 ≤ ν ^ 2 := by
      rw [← sq_abs ν]
      nlinarith [sq_nonneg (|ν| - T)]
    have hdivsq : (T / a) ^ 2 ≤ (ν / a) ^ 2 := by
      rw [div_pow, div_pow]
      exact div_le_div_of_nonneg_right hsq (sq_nonneg a)
    have hu : 1 + (T / a) ^ 2 ≤ 1 + (ν / a) ^ 2 := by linarith
    have hinv : (1 + (ν / a) ^ 2)⁻¹ ≤
        (1 + (T / a) ^ 2)⁻¹ := by
      exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hu
    dsimp only [g, E, h]
    rw [pow_two, mul_inv]
    exact mul_le_mul_of_nonneg_right hinv (by positivity)
  calc
    (∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, g ν) ≤
        ∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, E * h ν := by
      apply MeasureTheory.integral_mono_ae hg.integrableOn
        hmajor.integrableOn
      filter_upwards [MeasureTheory.ae_restrict_mem
        measurableSet_Ioc.compl] with ν hνmem
      exact hpoint ν hνmem
    _ ≤ ∫ ν : ℝ, E * h ν := by
      exact MeasureTheory.integral_mono_measure
        MeasureTheory.Measure.restrict_le_self
        (Filter.Eventually.of_forall (fun ν => by
          exact mul_nonneg hE0 (by dsimp only [h]; positivity))) hmajor
    _ = E * (a * Real.pi) := by
      rw [MeasureTheory.integral_const_mul, integral_scaled_cauchy ha]
    _ = ((1 + (T / a) ^ 2)⁻¹) * (a * Real.pi) := rfl

/-- At height `|tau| = a^2`, the quartic kernel contributes `a^-4`. -/
theorem scaled_quartic_at_sq_le_inv_four
    {a τ : ℝ} (ha : 0 < a) (hτ : |τ| = a ^ 2) :
    ((1 + (τ / a) ^ 2) ^ 2)⁻¹ ≤ (a ^ 4)⁻¹ := by
  have hτsq : τ ^ 2 = a ^ 4 := by
    rw [← sq_abs τ, hτ]
    ring
  have hratio : (τ / a) ^ 2 = a ^ 2 := by
    rw [div_pow, hτsq]
    field_simp [ha.ne']
  rw [hratio]
  have hden : a ^ 4 ≤ (1 + a ^ 2) ^ 2 := by
    nlinarith [sq_nonneg a, sq_nonneg (a ^ 2)]
  simpa only [one_div] using
    one_div_le_one_div_of_le (pow_pos ha 4) hden

end Chen.BombieriVinogradov

end

/-! ## ChenTheorem.Lemma9.BombieriVinogradov.SmallConductorLogDeriv -/

section

open Filter Real
open scoped Classical Interval

namespace Chen.BombieriVinogradov

/-!
# Logarithmic-derivative form of the adjustable smoothing

This file passes from the finite Mellin representation of
`bvSmoothedTwistedPsi` to the absolutely convergent von Mangoldt
Dirichlet series on `Re s > 1`.  The resulting integrand is the one to be
moved through the finite zero-free rectangle.
-/
/-- One term of the full, separated Mellin series. -/
noncomputable def bvSmoothedFullTerm {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) (n : ℕ) (s : ℂ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
    ((x : ℂ) ^ s * (n : ℂ) ^ (-s) *
      Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x) s)
/-- The analytic integrand after summing the von Mangoldt series. -/
noncomputable def bvSmoothedLogDerivIntegrand {q : ℕ} [NeZero q]
    (K x : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -(((x : ℂ) ^ s *
      Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x) s) *
    (deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s))
/-- Positive real quotients separate cleanly under complex powers. -/
theorem ofReal_div_cpow_eq_mul_cpow_neg
    {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) (s : ℂ) :
    (((x / n : ℝ) : ℂ) ^ s) =
      (x : ℂ) ^ s * (n : ℂ) ^ (-s) := by
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hx (inv_nonneg.mpr hn.le)]
  congr 1
  rw [Complex.ofReal_inv, Complex.inv_cpow, ← Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg hn.le]
  exact Real.pi_ne_zero.symm
/-- On a nonzero index, the quotient form coming from Mellin inversion
is exactly the separated full-series term. -/
theorem bvSmoothedFullTerm_eq_ratio {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 ≤ n)
    (s : ℂ) :
    bvSmoothedFullTerm K x χ n s =
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
        (((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^ s) *
          Chen.lemma6SmoothingMellinKernel
            (bvSmoothingParameter K x) s) := by
  rw [ofReal_div_cpow_eq_mul_cpow_neg
    (Nat.cast_nonneg x) (by exact_mod_cast (show 0 < n by omega))]
  unfold bvSmoothedFullTerm
  push_cast
  ring
/-- The full smoothed series is the expected logarithmic derivative on
the half-plane of absolute convergence. -/
theorem tsum_bvSmoothedFullTerm_eq_logDeriv
    {q : ℕ} [NeZero q] (K x : ℕ)
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, bvSmoothedFullTerm K x χ n s) =
      bvSmoothedLogDerivIntegrand K x χ s := by
  let a : ℕ → ℂ := fun n =>
    χ n * (ArithmeticFunction.vonMangoldt n : ℂ)
  have ha0 : a 0 = 0 := by
    dsimp only [a]
    simp
  calc
    (∑' n : ℕ, bvSmoothedFullTerm K x χ n s) =
        ((x : ℂ) ^ s *
          Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x) s) *
          (∑' n : ℕ, LSeries.term a s n) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [LSeries.term_def₀ ha0]
      unfold bvSmoothedFullTerm
      dsimp only [a]
      ring
    _ = ((x : ℂ) ^ s *
          Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x) s) *
          LSeries a s := rfl
    _ = -(((x : ℂ) ^ s *
          Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x) s) *
        (deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s)) := by
      have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
      have hseq :
          (fun n : ℕ => χ n) *
              (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) = a := by
        funext n
        rfl
      rw [hseq] at h
      have hL : LSeries a s =
          -(deriv (DirichletCharacter.LFunction χ) s /
            DirichletCharacter.LFunction χ s) := by
        calc
          LSeries a s =
              -deriv (LSeries (fun n : ℕ => χ n)) s /
                LSeries (fun n : ℕ => χ n) s := h
          _ = _ := by
            rw [← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
              ← DirichletCharacter.LFunction_eq_LSeries χ hs]
            ring
      rw [hL]
      ring
    _ = bvSmoothedLogDerivIntegrand K x χ s := rfl
/-- The full term restricted to Chen's standard initial line
`alpha = 1 + 1 / log x`. -/
noncomputable def bvSmoothedAlphaTerm {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) (n : ℕ) (t : ℝ) : ℂ :=
  bvSmoothedFullTerm K x χ n (Chen.lemma6AlphaPoint x t)
theorem bvSmoothedAlphaTerm_eq_ratio {q : ℕ}
    (K x : ℕ) (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 ≤ n)
    (t : ℝ) :
    bvSmoothedAlphaTerm K x χ n t =
      (ArithmeticFunction.vonMangoldt n : ℂ) * χ n *
        (((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^
            Chen.lemma6AlphaPoint x t) *
          Chen.lemma6SmoothingMellinKernel
            (bvSmoothingParameter K x) (Chen.lemma6AlphaPoint x t)) := by
  unfold bvSmoothedAlphaTerm
  exact bvSmoothedFullTerm_eq_ratio K x χ hn _
theorem integrable_bvSmoothedAlphaTerm {q : ℕ}
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    MeasureTheory.Integrable (bvSmoothedAlphaTerm K x χ n) := by
  by_cases hn0 : n = 0
  · subst n
    have hz : bvSmoothedAlphaTerm K x χ 0 = 0 := by
      funext t
      simp [bvSmoothedAlphaTerm, bvSmoothedFullTerm]
    rw [hz]
    exact MeasureTheory.integrable_zero ℝ ℂ MeasureTheory.volume
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hσ : 0 < σ := by dsimp only [σ]; positivity
    have hy : 0 < (x : ℝ) / (n : ℝ) := by positivity
    have hbase := Chen.integrable_cpow_mul_lemma6SmoothingMellinKernel
      hy (bvSmoothingScale_pos K hlarge)
        (bvSmoothingOrder_one_le K hlarge) hσ
    exact hbase.const_mul
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n) |>.congr (by
        filter_upwards with t
        unfold bvSmoothedAlphaTerm
        rw [bvSmoothedFullTerm_eq_ratio K x χ hn]
        unfold Chen.lemma6AlphaPoint
        dsimp only [σ])
/-- The integrated norms of the full smoothed von Mangoldt series are
summable on the initial `alpha`-line.  This supplies the exact Tonelli
hypothesis needed below. -/
theorem summable_integral_norm_bvSmoothedAlphaTerm {q : ℕ}
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖bvSmoothedAlphaTerm K x χ n t‖) := by
  let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
  let Λ : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let G : ℝ → ℝ := fun t =>
    ‖Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x)
      ((σ : ℂ) + (t : ℂ) * Complex.I)‖
  let J : ℝ := ∫ t : ℝ, G t
  let D : ℝ := (x : ℝ) ^ σ * J
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hσone : 1 < σ := by
    dsimp only [σ]
    have : 0 < (1 : ℝ) / Real.log (x : ℝ) := by positivity
    linarith
  have hGint : MeasureTheory.Integrable G := by
    have hk := Chen.verticalIntegrable_lemma6SmoothingMellinKernel
      (bvSmoothingScale_pos K hlarge)
      (bvSmoothingOrder_one_le K hlarge) (lt_trans zero_lt_one hσone)
    rw [Complex.VerticalIntegrable] at hk
    simpa only [G] using hk.norm
  have hJ0 : 0 ≤ J := by
    dsimp only [J]
    exact MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (Real.rpow_nonneg hxpos.le _) hJ0
  have hΛsum : Summable (fun n : ℕ =>
      ‖LSeries.term Λ (σ : ℂ) n‖) := by
    rw [summable_norm_iff]
    simpa only [Λ, LSeriesSummable] using
      ArithmeticFunction.LSeriesSummable_vonMangoldt
        (s := (σ : ℂ)) (by simpa using hσone)
  have hmajor : Summable (fun n : ℕ =>
      D * ‖LSeries.term Λ (σ : ℂ) n‖) := hΛsum.mul_left D
  apply hmajor.of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg
    (MeasureTheory.integral_nonneg fun _ => norm_nonneg _)]
  by_cases hn0 : n = 0
  · subst n
    have hz : bvSmoothedAlphaTerm K x χ 0 = 0 := by
      funext t
      simp [bvSmoothedAlphaTerm, bvSmoothedFullTerm]
    simp only [hz, Pi.zero_apply, norm_zero, MeasureTheory.integral_zero,
      LSeries.term_zero, mul_zero]
    exact le_rfl
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by omega)
    let y : ℝ := (x : ℝ) / (n : ℝ)
    let c : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ) * χ n
    have hy : 0 < y := by dsimp only [y]; positivity
    have hterm (t : ℝ) :
        bvSmoothedAlphaTerm K x χ n t =
          c * (((y : ℂ) ^
              ((σ : ℂ) + (t : ℂ) * Complex.I)) *
            Chen.lemma6SmoothingMellinKernel
              (bvSmoothingParameter K x)
              ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      unfold bvSmoothedAlphaTerm
      rw [bvSmoothedFullTerm_eq_ratio K x χ hn]
      unfold Chen.lemma6AlphaPoint
      dsimp only [σ, y, c]
    have hcoeff : ‖c‖ ≤ ArithmeticFunction.vonMangoldt n := by
      dsimp only [c]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
        (χ.norm_le_one n)
    have hpoint (t : ℝ) :
        ‖bvSmoothedAlphaTerm K x χ n t‖ ≤
          (ArithmeticFunction.vonMangoldt n * y ^ σ) * G t := by
      rw [hterm, norm_mul]
      have hinner :
          ‖(y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
              Chen.lemma6SmoothingMellinKernel
                (bvSmoothingParameter K x)
                ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
            y ^ σ *
              ‖Chen.lemma6SmoothingMellinKernel
                (bvSmoothingParameter K x)
                ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
          mul_one, sub_self, add_zero]
      rw [hinner]
      dsimp only [G]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoeff
            (Real.rpow_nonneg hy.le σ))
          (norm_nonneg (Chen.lemma6SmoothingMellinKernel
            (bvSmoothingParameter K x)
            ((σ : ℂ) + (t : ℂ) * Complex.I))))
    have hright : MeasureTheory.Integrable (fun t : ℝ =>
        (ArithmeticFunction.vonMangoldt n * y ^ σ) * G t) :=
      hGint.const_mul _
    have htermnorm :
        ‖LSeries.term Λ (σ : ℂ) n‖ =
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
      rw [LSeries.norm_term_eq]
      simp only [hn0, if_false, Λ, Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.ofReal_re]
    have hyFactor : y ^ σ =
        (x : ℝ) ^ σ / (n : ℝ) ^ σ := by
      dsimp only [y]
      exact Real.div_rpow hxpos.le hnpos.le σ
    calc
      (∫ t : ℝ, ‖bvSmoothedAlphaTerm K x χ n t‖) ≤
          ∫ t : ℝ,
            (ArithmeticFunction.vonMangoldt n * y ^ σ) * G t := by
        exact MeasureTheory.integral_mono
          (integrable_bvSmoothedAlphaTerm K hx hlarge χ n).norm
          hright hpoint
      _ = (ArithmeticFunction.vonMangoldt n * y ^ σ) * J := by
        rw [MeasureTheory.integral_const_mul]
      _ = D * ‖LSeries.term Λ (σ : ℂ) n‖ := by
        rw [hyFactor, htermnorm]
        dsimp only [D, J]
        ring
/-- The full smoothed series may be integrated term by term on the
initial line. -/
theorem tsum_integral_bvSmoothedAlphaTerm_eq_integral_tsum {q : ℕ}
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    (∑' n : ℕ, ∫ t : ℝ, bvSmoothedAlphaTerm K x χ n t) =
      ∫ t : ℝ, ∑' n : ℕ, bvSmoothedAlphaTerm K x χ n t := by
  exact MeasureTheory.integral_tsum_of_summable_integral_norm
    (integrable_bvSmoothedAlphaTerm K hx hlarge χ)
    (summable_integral_norm_bvSmoothedAlphaTerm K hx hlarge χ)
/-- The logarithmic-derivative integrand itself is integrable on the
initial `alpha`-line.  This is the form needed to split the improper
integral into a finite segment and its complement. -/
theorem integrable_bvSmoothedLogDerivIntegrand_alpha
    {q : ℕ} [NeZero q] (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    MeasureTheory.Integrable (fun t : ℝ =>
      bvSmoothedLogDerivIntegrand K x χ
        (Chen.lemma6AlphaPoint x t)) := by
  have hsum : MeasureTheory.Integrable (fun t : ℝ =>
      ∑' n : ℕ, bvSmoothedAlphaTerm K x χ n t) :=
    Chen.integrable_tsum_of_summable_integral_norm_complex
      (integrable_bvSmoothedAlphaTerm K hx hlarge χ)
      (summable_integral_norm_bvSmoothedAlphaTerm K hx hlarge χ)
  exact hsum.congr (by
    filter_upwards with t
    exact tsum_bvSmoothedFullTerm_eq_logDeriv K x χ
      (Chen.one_lt_lemma6AlphaPoint_re hx t))
/-- Terms outside `[1,x]` have zero Mellin integral because the adjustable
smoothing weight itself vanishes there. -/
theorem integral_bvSmoothedAlphaTerm_eq_zero_of_not_mem {q : ℕ}
    (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) {n : ℕ}
    (hnmem : n ∉ Finset.Icc 1 x) :
    (∫ t : ℝ, bvSmoothedAlphaTerm K x χ n t) = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [bvSmoothedAlphaTerm, bvSmoothedFullTerm]
  · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hxn : x ≤ n := by
      have : ¬(1 ≤ n ∧ n ≤ x) := by
        simpa only [Finset.mem_Icc] using hnmem
      omega
    let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hσ : 0 < σ := by dsimp only [σ]; positivity
    have hweight := bvSmoothingWeight_eq_smoothing_verticalIntegral
      K hx hn hlarge σ hσ
    rw [bvSmoothingWeight_eq_zero_of_le K hx hn hxn] at hweight
    have hcoef : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by
      exact one_div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    have hintegral :
        (∫ t : ℝ,
          ((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^
              ((σ : ℂ) + (t : ℂ) * Complex.I) *
            Chen.lemma6SmoothingMellinKernel
              (bvSmoothingParameter K x)
              ((σ : ℂ) + (t : ℂ) * Complex.I))) = 0 := by
      rw [Complex.real_smul] at hweight
      exact (mul_eq_zero.mp hweight.symm).resolve_left
        (Complex.ofReal_ne_zero.mpr hcoef)
    unfold bvSmoothedAlphaTerm
    simp_rw [bvSmoothedFullTerm_eq_ratio K x χ hn]
    unfold Chen.lemma6AlphaPoint
    change (∫ t : ℝ,
      ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n) *
        (((((x : ℝ) / (n : ℝ) : ℝ) : ℂ) ^
            ((σ : ℂ) + (t : ℂ) * Complex.I)) *
          Chen.lemma6SmoothingMellinKernel
            (bvSmoothingParameter K x)
            ((σ : ℂ) + (t : ℂ) * Complex.I))) = 0
    rw [MeasureTheory.integral_const_mul, hintegral, mul_zero]
/-- Exact logarithmic-derivative Perron formula for the adjustable
smoothed sum on `alpha = 1 + 1 / log x`. -/
theorem bvSmoothedTwistedPsi_eq_logDerivPerron
    {q : ℕ} [NeZero q] (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    bvSmoothedTwistedPsi K x χ =
      VerticalIntegral' (bvSmoothedLogDerivIntegrand K x χ)
        (1 + 1 / Real.log (x : ℝ)) := by
  let σ : ℝ := 1 + 1 / Real.log (x : ℝ)
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hpoint (t : ℝ) : Chen.lemma6AlphaPoint x t =
      (σ : ℂ) + (t : ℂ) * Complex.I := by
    unfold Chen.lemma6AlphaPoint
    dsimp only [σ]
  have hfinite :
      (∫ t : ℝ,
          bvSmoothedTwistedPsiFiniteIntegrand K x χ
            (Chen.lemma6AlphaPoint x t)) =
        ∑ n ∈ Finset.Icc 1 x,
          ∫ t : ℝ, bvSmoothedAlphaTerm K x χ n t := by
    unfold bvSmoothedTwistedPsiFiniteIntegrand
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hnmem
      have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      exact (bvSmoothedAlphaTerm_eq_ratio K x χ hn t).symm
    · intro n hnmem
      have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
      exact (integrable_bvSmoothedAlphaTerm K hx hlarge χ n).congr (by
        filter_upwards with t
        exact bvSmoothedAlphaTerm_eq_ratio K x χ hn t)
  have hfull :
      (∫ t : ℝ,
          bvSmoothedTwistedPsiFiniteIntegrand K x χ
            (Chen.lemma6AlphaPoint x t)) =
        ∫ t : ℝ,
          bvSmoothedLogDerivIntegrand K x χ
            (Chen.lemma6AlphaPoint x t) := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 x,
          ∫ t : ℝ, bvSmoothedAlphaTerm K x χ n t := hfinite
      _ = ∑' n : ℕ,
          ∫ t : ℝ, bvSmoothedAlphaTerm K x χ n t :=
        (tsum_eq_sum (s := Finset.Icc 1 x) (fun n hnmem =>
          integral_bvSmoothedAlphaTerm_eq_zero_of_not_mem
            K hx hlarge χ hnmem)).symm
      _ = ∫ t : ℝ,
          ∑' n : ℕ, bvSmoothedAlphaTerm K x χ n t :=
        tsum_integral_bvSmoothedAlphaTerm_eq_integral_tsum
          K hx hlarge χ
      _ = _ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        unfold bvSmoothedAlphaTerm
        exact tsum_bvSmoothedFullTerm_eq_logDeriv K x χ
          (Chen.one_lt_lemma6AlphaPoint_re hx t)
  rw [bvSmoothedTwistedPsi_eq_finiteVerticalIntegral
    K hx hlarge χ σ hσ]
  change VerticalIntegral' (bvSmoothedTwistedPsiFiniteIntegrand K x χ) σ =
    VerticalIntegral' (bvSmoothedLogDerivIntegrand K x χ) σ
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  simp_rw [← hpoint]
  rw [hfull]
/-- Cauchy--Goursat for the adjustable smoothed logarithmic-derivative
integrand on the finite rectangle bounded by `alpha` and `gamma`.  The
mixed classical zero-free region is only required up to height `T`. -/
theorem bvSmoothedLogDeriv_finite_rectangle_classical
    {E : ℕ} (data : Chen.PrimitiveZeroFreeRegionDataAt E)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 0 ≤ T)
    (hwidth : ∀ t : ℝ, |t| ≤ T →
      2 / Real.sqrt (Real.log (x : ℝ)) <
        Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q t) :
    let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
    let α : ℝ := 1 + 1 / Real.log (x : ℝ)
    let F : ℂ → ℂ := bvSmoothedLogDerivIntegrand K x χ
    (∫ σ : ℝ in γ..α, F ((σ : ℂ) - (T : ℂ) * Complex.I)) -
        (∫ σ : ℝ in γ..α, F ((σ : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I • (∫ t : ℝ in (-T)..T,
        F ((α : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I • (∫ t : ℝ in (-T)..T,
        F ((γ : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
  dsimp only
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let z : ℂ := (γ : ℂ) + (-T : ℂ) * Complex.I
  let w : ℂ := (α : ℂ) + (T : ℂ) * Complex.I
  let F : ℂ → ℂ := bvSmoothedLogDerivIntegrand K x χ
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hγα : γ ≤ α := by
    dsimp only [γ, α]
    have h1 : (0 : ℝ) ≤ 1 / Real.sqrt (Real.log (x : ℝ)) := by
      positivity
    have h2 : (0 : ℝ) ≤ 1 / Real.log (x : ℝ) :=
      div_nonneg zero_le_one hlog.le
    linarith
  have hzre : z.re = γ := by dsimp only [z]; simp
  have hwre : w.re = α := by dsimp only [w]; simp
  have hzim : z.im = -T := by dsimp only [z]; simp
  have hwim : w.im = T := by dsimp only [w]; simp
  have hrectpos :
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    change 0 < s.re
    have hre := hs.1
    rw [hzre, hwre, Set.uIcc_of_le hγα] at hre
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (hγpos.trans hre.1)
  letI : NeZero (x : ℂ) := ⟨by
    exact_mod_cast (show x ≠ 0 by omega)⟩
  have hxpow : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) :=
    (differentiable_const_cpow_of_neZero (x : ℂ)).differentiableOn
  have hk : DifferentiableOn ℂ
      (Chen.lemma6SmoothingMellinKernel (bvSmoothingParameter K x))
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) :=
    (Chen.differentiableOn_lemma6SmoothingMellinKernel
      (one_lt_bvSmoothingParameter K hx)).mono hrectpos
  have hLq : DifferentiableOn ℂ
      (fun s => deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    intro s hs
    have hre := hs.1
    have him := hs.2
    rw [hzre, hwre, Set.uIcc_of_le hγα] at hre
    rw [hzim, hwim, Set.uIcc_of_le (by linarith)] at him
    have habs : |s.im| ≤ T :=
      abs_le.mpr ⟨by linarith [him.1], him.2⟩
    have hwidths := hwidth s.im habs
    have htwoDiv : 2 / Real.sqrt (Real.log (x : ℝ)) =
        2 * (1 / Real.sqrt (Real.log (x : ℝ))) := by ring
    rw [htwoDiv] at hwidths
    have hhalfwidth : 1 / Real.sqrt (Real.log (x : ℝ)) <
        Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q s.im / 2 := by
      linarith
    have hhalf : 1 -
        Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q s.im / 2 < γ := by
      dsimp only [γ]
      linarith
    have hregion : 1 -
        Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q s.im < s.re := by
      have hwpos := Chen.primitiveZeroFreeWidthAt_pos (N := E) data.cHeight_pos
        data.cSiegel_pos hq s.im
      exact Chen.one_sub_width_lt_of_half_width_le hwpos
        (hhalf.le.trans hre.1)
    have hne := data.nonvanishing q inferInstance χ hq hχ s hregion
    exact ((Chen.primitiveCharacter_differentiable_LFunction_deriv hq
        hχ).differentiableAt.div
      (Chen.primitiveCharacter_differentiable_LFunction hq hχ).differentiableAt
      hne).differentiableWithinAt
  have hdiff : DifferentiableOn ℂ F
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    unfold F bvSmoothedLogDerivIntegrand
    exact ((hxpow.mul hk).mul hLq).neg
  have hrect :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hdiff
  rw [hzre, hwre, hzim, hwim] at hrect
  dsimp only [F] at hrect
  simpa only [γ, α, sub_eq_add_neg, Complex.ofReal_neg, neg_mul] using hrect
/-! ### Quantitative specialization of the classical zero-free region -/
/-- At the adjustable square-scale contour height and for conductors at
most `(log x)^R`, the shifted line eventually lies in the half-width
classical zero-free region.  The threshold may depend on the requested
logarithmic saving `K` and on the constants in `data`, but is uniform in the
conductor and in every height inside the finite rectangle. -/
theorem eventually_two_div_sqrt_log_lt_primitiveZeroFreeWidth_bvHeight
    {E : ℕ} (data : Chen.PrimitiveZeroFreeRegionDataAt E) (K R : ℕ)
    (hR : 1 ≤ R) (hER : 3 * R ≤ E) :
    ∀ᶠ x : ℕ in atTop,
      ∀ (q : ℕ), 2 ≤ q →
        (q : ℝ) ≤ Real.log (x : ℝ) ^ R →
        ∀ t : ℝ, |t| ≤ bvSmoothingContourHeight K x →
          2 / Real.sqrt (Real.log (x : ℝ)) <
            Chen.primitiveZeroFreeWidthAt E
              data.cHeight data.cSiegel q t := by
  let N : ℕ := 22 * (K + 1) + R + 1
  let F : ℝ := (N : ℝ)
  have hFpos : 0 < F := by
    dsimp only [F, N]
    positivity
  have hsmallReal : ∀ᶠ y : ℝ in atTop,
      ‖Real.log y ^ (1 : ℝ)‖ ≤
        (data.cHeight / (4 * F)) *
          ‖y ^ ((1 : ℝ) / 2)‖ :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).def
        (div_pos data.cHeight_pos (mul_pos (by norm_num) hFpos))
  have hlogT : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hheight : ∀ᶠ x : ℕ in atTop,
      2 * F * Real.log (Real.log (x : ℝ)) <
        data.cHeight * Real.sqrt (Real.log (x : ℝ)) := by
    filter_upwards [hlogT.eventually hsmallReal,
        hlogT.eventually (eventually_gt_atTop 1)] with x hx hL1
    have hlogLpos : 0 < Real.log (Real.log (x : ℝ)) := Real.log_pos hL1
    have hLpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans hL1
    have hrpowpos : 0 <
        Real.log (x : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_pos_of_pos hLpos _
    have hx' : Real.log (Real.log (x : ℝ)) ≤
        (data.cHeight / (4 * F)) *
          Real.log (x : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_one, Real.norm_eq_abs, abs_of_pos hlogLpos,
        Real.norm_eq_abs, abs_of_pos hrpowpos] at hx
      exact hx
    have hscaled :
        2 * F * Real.log (Real.log (x : ℝ)) ≤
          2 * F * ((data.cHeight / (4 * F)) *
            Real.log (x : ℝ) ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hx'
        (mul_nonneg (by norm_num) hFpos.le)
    have heq :
        2 * F * ((data.cHeight / (4 * F)) *
          Real.log (x : ℝ) ^ ((1 : ℝ) / 2)) =
        data.cHeight / 2 *
          Real.log (x : ℝ) ^ ((1 : ℝ) / 2) := by
      field_simp [hFpos.ne']; ring
    rw [heq] at hscaled
    rw [Real.sqrt_eq_rpow]
    nlinarith [mul_pos data.cHeight_pos hrpowpos]
  have hsiegelReal : ∀ᶠ y : ℝ in atTop,
      2 < data.cSiegel * y ^ ((1 : ℝ) / 6) := by
    have ht := tendsto_rpow_atTop (show (0 : ℝ) < 1 / 6 by norm_num)
    have hev := ht.eventually
      (eventually_gt_atTop (2 / data.cSiegel))
    filter_upwards [hev, eventually_gt_atTop 0] with y hy hy0
    calc
      (2 : ℝ) = data.cSiegel * (2 / data.cSiegel) := by
        field_simp [data.cSiegel_pos.ne']
      _ < data.cSiegel * y ^ ((1 : ℝ) / 6) :=
        mul_lt_mul_of_pos_left hy data.cSiegel_pos
  have hsiegel := hlogT.eventually hsiegelReal
  have hLtwo := hlogT.eventually (eventually_ge_atTop 2)
  filter_upwards [hheight, hsiegel, hLtwo] with x hheight hsiegel hLtwo
  intro q hq hqR t ht
  let L : ℝ := Real.log (x : ℝ)
  let B : ℕ := 22 * (K + 1)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hBpos : 1 ≤ B := by dsimp only [B]; omega
  have hheight_eq : bvSmoothingContourHeight K x = L ^ B := by
    dsimp only [bvSmoothingContourHeight, L, B]
    rw [← pow_mul]
    congr 1
    omega
  have hpowtwo : (2 : ℝ) ≤ L ^ B := by
    calc
      (2 : ℝ) ≤ L := hLtwo
      _ = L ^ 1 := by ring
      _ ≤ L ^ B := pow_le_pow_right₀ hLone hBpos
  have ht2 : |t| + 2 ≤ L ^ (B + 1) := by
    calc
      |t| + 2 ≤ bvSmoothingContourHeight K x + 2 := by linarith
      _ = L ^ B + 2 := by rw [hheight_eq]
      _ ≤ 2 * L ^ B := by linarith
      _ ≤ L * L ^ B :=
        mul_le_mul_of_nonneg_right hLtwo (pow_nonneg hLpos.le _)
      _ = L ^ (B + 1) := by rw [pow_succ']
  have harg : (q : ℝ) * (|t| + 2) ≤ L ^ N := by
    calc
      (q : ℝ) * (|t| + 2) ≤ L ^ R * L ^ (B + 1) :=
        mul_le_mul hqR ht2 (by positivity) (by positivity)
      _ = L ^ N := by
        rw [← pow_add]
        congr 1
        dsimp only [N, B]
        omega
  have hargpos : 0 < (q : ℝ) * (|t| + 2) := by positivity
  have hlogarg : Real.log ((q : ℝ) * (|t| + 2)) ≤
      F * Real.log L := by
    have hlogle := Real.log_le_log hargpos harg
    rw [Real.log_pow] at hlogle
    simpa only [F] using hlogle
  have hlogargpos := Chen.primitiveZeroFreeHeightLog_pos hq t
  have hheightWidth : 2 / Real.sqrt L <
      data.cHeight / Real.log ((q : ℝ) * (|t| + 2)) := by
    rw [div_lt_div_iff₀ (Real.sqrt_pos.2 hLpos) hlogargpos]
    calc
      2 * Real.log ((q : ℝ) * (|t| + 2)) ≤
          2 * F * Real.log L := by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left hlogarg (by norm_num : (0 : ℝ) ≤ 2))
      _ < data.cHeight * Real.sqrt L := by
        simpa only [L] using hheight
  have hEpos : (0 : ℝ) < E := by
    exact_mod_cast (show 0 < E by omega)
  have hratio : (R : ℝ) / (E : ℝ) ≤ (1 : ℝ) / 3 := by
    rw [div_le_iff₀ hEpos]
    have hERreal : 3 * (R : ℝ) ≤ (E : ℝ) := by exact_mod_cast hER
    nlinarith
  have hpowq : L ^ ((-1 : ℝ) / 3) ≤
      (q : ℝ) ^ ((-1 : ℝ) / E) := by
    have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < q)
      hqR (div_nonpos_of_nonpos_of_nonneg
        (show (-1 : ℝ) ≤ 0 by norm_num) hEpos.le)
    have hpow : (L ^ R) ^ ((-1 : ℝ) / E) =
        L ^ (-((R : ℝ) / E)) := by
      rw [← Real.rpow_natCast L R, ← Real.rpow_mul hLpos.le]
      congr 1
      ring
    have hmono : L ^ ((-1 : ℝ) / 3) ≤
        L ^ (-((R : ℝ) / E)) :=
      Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
    exact hmono.trans (hpow ▸ hp)
  have hsiegelWidth : 2 / Real.sqrt L <
      data.cSiegel * (q : ℝ) ^ ((-1 : ℝ) / E) := by
    have hpowid : L ^ ((-1 : ℝ) / 2) * L ^ ((1 : ℝ) / 6) =
        L ^ ((-1 : ℝ) / 3) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    have hinvSqrt : 1 / Real.sqrt L = L ^ ((-1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hLpos.le]
      congr 1
      ring
    have hinvSqrt' : (Real.sqrt L)⁻¹ = L ^ ((-1 : ℝ) / 2) := by
      simpa only [one_div] using hinvSqrt
    calc
      2 / Real.sqrt L = 2 * L ^ ((-1 : ℝ) / 2) := by
        rw [div_eq_mul_inv, hinvSqrt']
      _ < data.cSiegel * L ^ ((1 : ℝ) / 6) *
          L ^ ((-1 : ℝ) / 2) := by
        exact mul_lt_mul_of_pos_right hsiegel
          (Real.rpow_pos_of_pos hLpos _)
      _ = data.cSiegel * L ^ ((-1 : ℝ) / 3) := by
        rw [← hpowid]
        ring
      _ ≤ data.cSiegel * (q : ℝ) ^ ((-1 : ℝ) / E) :=
        mul_le_mul_of_nonneg_left hpowq data.cSiegel_pos.le
  unfold Chen.primitiveZeroFreeWidthAt
  exact lt_min hheightWidth hsiegelWidth
/-- The logarithmic-derivative majorant at the adjustable contour height
still costs only two powers of `log x`; all dependence on the desired
saving is isolated in the explicit coefficient. -/
theorem eq21ClassicalLogDerivMajorant_bvHeight_le
    {E : ℕ} (data : Chen.PrimitiveZeroFreeRegionDataAt E) (K R : ℕ)
    (hR : 1 ≤ R) (hER : 3 * R ≤ E) {x q : ℕ}
    (hxlog : 4 ≤ Real.log (x : ℝ)) (hq : 2 ≤ q)
    (hqR : (q : ℝ) ≤ Real.log (x : ℝ) ^ R) :
    Chen.primitiveLogDerivMajorantAt data q
        (bvSmoothingContourHeight K x) ≤
      (((22 * (K + 1) + R + 4 : ℕ) : ℝ) ^ 2) *
        data.cLogDeriv * Real.log (x : ℝ) ^ 2 := by
  let L : ℝ := Real.log (x : ℝ)
  let N : ℕ := 22 * (K + 1)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hEpos : (0 : ℝ) < E := by
    exact_mod_cast (show 0 < E by omega)
  have hratio : (R : ℝ) / (E : ℝ) ≤ 1 := by
    rw [div_le_one hEpos]
    exact_mod_cast (show R ≤ E by omega)
  have hqpow : (q : ℝ) ^ ((1 : ℝ) / E) ≤ L := by
    calc
      (q : ℝ) ^ ((1 : ℝ) / E) ≤
          (L ^ R) ^ ((1 : ℝ) / E) :=
        Real.rpow_le_rpow hqpos.le hqR (by positivity)
      _ = L ^ ((R : ℝ) / E) := by
        rw [← Real.rpow_natCast L R, ← Real.rpow_mul hLpos.le]
        congr 1
        ring
      _ ≤ L ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hLone hratio
      _ = L := Real.rpow_one L
  have hlogL : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
  have hlogq : Real.log (q : ℝ) ≤ (R : ℝ) * Real.log L := by
    have hle := Real.log_le_log hqpos hqR
    rw [Real.log_pow] at hle
    exact hle
  have hheight_eq : bvSmoothingContourHeight K x = L ^ N := by
    dsimp only [bvSmoothingContourHeight, L, N]
    rw [← pow_mul]
    congr 1
    omega
  have hTone : (1 : ℝ) ≤ L ^ N := one_le_pow₀ hLone
  have hTtwo : L ^ N + 2 ≤ 3 * L ^ N := by linarith
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    nlinarith [Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 3 by norm_num)]
  have hNlog : (N : ℝ) * Real.log L ≤ (N : ℝ) * L :=
    mul_le_mul_of_nonneg_left hlogL (Nat.cast_nonneg N)
  have hlogTtwo : Real.log (L ^ N + 2) ≤ ((N : ℝ) + 2) * L := by
    have hpos : 0 < L ^ N + 2 := by positivity
    have hmono : Real.log (L ^ N + 2) ≤ Real.log (3 * L ^ N) :=
      Real.log_le_log hpos hTtwo
    have heq : Real.log (3 * L ^ N) =
        Real.log 3 + (N : ℝ) * Real.log L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    rw [heq] at hmono
    nlinarith
  have hlogarg : Real.log ((q : ℝ) *
        (bvSmoothingContourHeight K x + 2)) ≤
      ((N : ℝ) + (R : ℝ) + 2) * L := by
    have heq : Real.log ((q : ℝ) *
          (bvSmoothingContourHeight K x + 2)) =
        Real.log (q : ℝ) + Real.log (L ^ N + 2) := by
      have hh : 0 < bvSmoothingContourHeight K x + 2 := by
        linarith [bvSmoothingContourHeight_nonneg K x]
      rw [Real.log_mul hqpos.ne' hh.ne', hheight_eq]
    rw [heq]
    have hqL : (R : ℝ) * Real.log L ≤ (R : ℝ) * L :=
      mul_le_mul_of_nonneg_left hlogL (Nat.cast_nonneg R)
    linarith
  have hbase : (q : ℝ) ^ ((1 : ℝ) / E) +
        Real.log ((q : ℝ) *
          (bvSmoothingContourHeight K x + 2)) + 1 ≤
      ((N : ℝ) + (R : ℝ) + 4) * L := by linarith
  have hbase0 : 0 ≤ (q : ℝ) ^ ((1 : ℝ) / E) +
      Real.log ((q : ℝ) *
        (bvSmoothingContourHeight K x + 2)) + 1 := by
    have hheight0 : 0 ≤ bvSmoothingContourHeight K x :=
      bvSmoothingContourHeight_nonneg K x
    have hlogpos := Chen.primitiveZeroFreeHeightLog_pos hq
      (bvSmoothingContourHeight K x)
    rw [abs_of_nonneg hheight0] at hlogpos
    have hrpow : 0 ≤ (q : ℝ) ^ ((1 : ℝ) / E) :=
      Real.rpow_nonneg (by positivity) _
    linarith
  have hsquare : ((q : ℝ) ^ ((1 : ℝ) / E) +
        Real.log ((q : ℝ) *
          (bvSmoothingContourHeight K x + 2)) + 1) ^ 2 ≤
      (((N : ℝ) + (R : ℝ) + 4) * L) ^ 2 :=
    pow_le_pow_left₀ hbase0 hbase 2
  unfold Chen.primitiveLogDerivMajorantAt
  calc
    data.cLogDeriv * ((q : ℝ) ^ ((1 : ℝ) / E) +
          Real.log ((q : ℝ) *
            (bvSmoothingContourHeight K x + 2)) + 1) ^ 2 ≤
        data.cLogDeriv * (((N : ℝ) + (R : ℝ) + 4) * L) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare data.cLogDeriv_pos.le
    _ = (((22 * (K + 1) + R + 4 : ℕ) : ℝ) ^ 2) *
        data.cLogDeriv * Real.log (x : ℝ) ^ 2 := by
      dsimp only [N, L]
      push_cast
      ring
/-- Pointwise product bound inside the half-width classical zero-free
region.  All three analytic costs (`x^s`, the Mellin kernel, and `L'/L`)
remain explicit for later specialization to vertical and horizontal
edges. -/
theorem norm_bvSmoothedLogDerivIntegrand_le_classical
    {E : ℕ} (data : Chen.PrimitiveZeroFreeRegionDataAt E)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (s : ℂ) (hspos : 0 < s.re)
    (hregion : 1 -
      Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q s.im / 2 ≤
        s.re) :
    ‖bvSmoothedLogDerivIntegrand K x χ s‖ ≤
      (x : ℝ) ^ s.re *
          (s.re⁻¹ *
            ((1 + (s.im /
              Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
        (data.cLogDeriv *
          ((q : ℝ) ^ ((1 : ℝ) / E) +
            Real.log ((q : ℝ) * (|s.im| + 2)) + 1) ^ 2) := by
  have hsrepr : (s.re : ℂ) + (s.im : ℂ) * Complex.I = s := by
    apply Complex.ext <;> simp
  have hk := norm_bvSmoothingMellinKernel_le_quartic
    K hx hlarge hspos s.im
  rw [hsrepr] at hk
  have hL := data.logDeriv_bound q inferInstance χ hq hχ s hregion
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hxnorm : ‖(x : ℂ) ^ s‖ = (x : ℝ) ^ s.re := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.norm_cpow_eq_rpow_re_of_pos hxpos s)
  unfold bvSmoothedLogDerivIntegrand
  simp only [norm_neg, norm_mul]
  rw [hxnorm]
  calc
    (x : ℝ) ^ s.re *
          ‖Chen.lemma6SmoothingMellinKernel
            (bvSmoothingParameter K x) s‖ *
        ‖deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s‖ ≤
      (x : ℝ) ^ s.re *
          (s.re⁻¹ *
            ((1 + (s.im /
              Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
        ‖deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s‖ := by
      gcongr
    _ ≤ _ := by
      gcongr
/-- Uniform pointwise bound on the shifted `gamma`-line up to height
`T`. -/
theorem norm_bvSmoothedLogDerivIntegrand_gamma_le_classical
    {E : ℕ} (data : Chen.PrimitiveZeroFreeRegionDataAt E)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {T ν : ℝ} (hν : |ν| ≤ T)
    (hwidth : 2 / Real.sqrt (Real.log (x : ℝ)) <
      Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q ν) :
    ‖bvSmoothedLogDerivIntegrand K x χ
        (Chen.lemma6Equation21Point x ν)‖ ≤
      2 * (x : ℝ) ^
          (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        Chen.primitiveLogDerivMajorantAt data q T := by
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hγpositive : 0 < γ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hγpos
  have hhalf : 1 -
      Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q ν / 2 ≤ γ := by
    have htwo : 2 / Real.sqrt (Real.log (x : ℝ)) =
        2 * (1 / Real.sqrt (Real.log (x : ℝ))) := by ring
    rw [htwo] at hwidth
    dsimp only [γ]
    linarith
  have hregion : 1 -
      Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q
        (Chen.lemma6Equation21Point x ν).im / 2 ≤
      (Chen.lemma6Equation21Point x ν).re := by
    simpa only [Chen.lemma6Equation21Point_re,
      Chen.lemma6Equation21Point_im, γ] using hhalf
  have hraw := norm_bvSmoothedLogDerivIntegrand_le_classical
    data K hq hx hlarge hχ (Chen.lemma6Equation21Point x ν)
      (by simpa only [Chen.lemma6Equation21Point_re, γ] using hγpositive)
      hregion
  have hγinv : γ⁻¹ ≤ 2 := by
    have := (inv_le_inv₀ hγpositive
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr hγpos
    rwa [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at this
  have hquartic :
      ((1 + (ν /
        Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ ≤ 1 := by
    have hbase : (1 : ℝ) ≤
        (1 + (ν /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2 := by
      nlinarith [sq_nonneg
        (ν / Real.log (x : ℝ) ^ (11 * (K + 1))),
        sq_nonneg (1 +
          (ν / Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2)]
    exact inv_le_one_of_one_le₀ hbase
  have hkernel : γ⁻¹ *
      ((1 + (ν /
        Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ ≤ 2 := by
    calc
      γ⁻¹ *
          ((1 + (ν /
            Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ ≤
        2 * 1 := mul_le_mul hγinv hquartic (by positivity) (by positivity)
      _ = 2 := by ring
  have hargpos : 0 < (q : ℝ) * (|ν| + 2) := by positivity
  have hargle : (q : ℝ) * (|ν| + 2) ≤ (q : ℝ) * (T + 2) := by
    gcongr
  have hlogle : Real.log ((q : ℝ) * (|ν| + 2)) ≤
      Real.log ((q : ℝ) * (T + 2)) :=
    Real.log_le_log hargpos hargle
  have hbase0 : 0 ≤ (q : ℝ) ^ ((1 : ℝ) / E) +
      Real.log ((q : ℝ) * (|ν| + 2)) + 1 := by
    have := Chen.primitiveZeroFreeHeightLog_pos hq ν
    positivity
  have hbasele : (q : ℝ) ^ ((1 : ℝ) / E) +
        Real.log ((q : ℝ) * (|ν| + 2)) + 1 ≤
      (q : ℝ) ^ ((1 : ℝ) / E) +
        Real.log ((q : ℝ) * (T + 2)) + 1 := by linarith
  have hM : data.cLogDeriv *
        ((q : ℝ) ^ ((1 : ℝ) / E) +
          Real.log ((q : ℝ) * (|ν| + 2)) + 1) ^ 2 ≤
      Chen.primitiveLogDerivMajorantAt data q T := by
    unfold Chen.primitiveLogDerivMajorantAt
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hbase0 hbasele 2) data.cLogDeriv_pos.le
  rw [Chen.lemma6Equation21Point_re,
    Chen.lemma6Equation21Point_im] at hraw
  change ‖bvSmoothedLogDerivIntegrand K x χ
      (Chen.lemma6Equation21Point x ν)‖ ≤ 2 * (x : ℝ) ^ γ *
        Chen.primitiveLogDerivMajorantAt data q T
  exact hraw.trans (by
    calc
      (x : ℝ) ^ γ *
            (γ⁻¹ *
              ((1 + (ν /
                Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
          (data.cLogDeriv *
            ((q : ℝ) ^ ((1 : ℝ) / E) +
              Real.log ((q : ℝ) * (|ν| + 2)) + 1) ^ 2) ≤
        (x : ℝ) ^ γ * 2 *
          Chen.primitiveLogDerivMajorantAt data q T := by
        gcongr
        exact mul_nonneg data.cLogDeriv_pos.le (sq_nonneg _)
      _ = 2 * (x : ℝ) ^ γ *
          Chen.primitiveLogDerivMajorantAt data q T := by ring)
/-- The finite shifted vertical segment has the expected
`T * x^gamma * M(q,T)` bound. -/
theorem norm_intervalIntegral_bvSmoothedLogDeriv_gamma_le_classical
    {E : ℕ} (data : Chen.PrimitiveZeroFreeRegionDataAt E)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 0 ≤ T)
    (hwidth : ∀ ν : ℝ, |ν| ≤ T →
      2 / Real.sqrt (Real.log (x : ℝ)) <
        Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q ν) :
    ‖∫ ν : ℝ in (-T)..T,
        bvSmoothedLogDerivIntegrand K x χ
          (Chen.lemma6Equation21Point x ν)‖ ≤
      4 * T * ((x : ℝ) ^
          (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        Chen.primitiveLogDerivMajorantAt data q T) := by
  let C : ℝ := 2 * (x : ℝ) ^
      (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        Chen.primitiveLogDerivMajorantAt data q T
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (Nat.cast_nonneg x) _))
      (Chen.primitiveLogDerivMajorantAt_nonneg data q T)
  have hmain :
      ‖∫ ν : ℝ in (-T)..T,
          bvSmoothedLogDerivIntegrand K x χ
            (Chen.lemma6Equation21Point x ν)‖ ≤ C * |T - (-T)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro ν hνmem
    rw [Set.uIoc_of_le (by linarith)] at hνmem
    have hν : |ν| ≤ T := abs_le.mpr ⟨hνmem.1.le, hνmem.2⟩
    exact norm_bvSmoothedLogDerivIntegrand_gamma_le_classical
      data K hq hx hlarge hγpos hχ hν (hwidth ν hν)
  calc
    ‖∫ ν : ℝ in (-T)..T,
        bvSmoothedLogDerivIntegrand K x χ
          (Chen.lemma6Equation21Point x ν)‖ ≤ C * |T - (-T)| := hmain
    _ = 4 * T * ((x : ℝ) ^
          (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
        Chen.primitiveLogDerivMajorantAt data q T) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)]
      dsimp only [C]
      ring
/-- Uniform pointwise bound on either horizontal edge. -/
theorem norm_bvSmoothedLogDerivIntegrand_horizontal_le_classical
    {E : ℕ} (data : Chen.PrimitiveZeroFreeRegionDataAt E)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {T τ σ : ℝ} (hτ : |τ| = T)
    (hσ : σ ∈ Set.Icc
      (1 - 1 / Real.sqrt (Real.log (x : ℝ)))
      (1 + 1 / Real.log (x : ℝ)))
    (hwidth : 2 / Real.sqrt (Real.log (x : ℝ)) <
      Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q τ) :
    ‖bvSmoothedLogDerivIntegrand K x χ
        ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      (2 * Real.exp 1 * (x : ℝ) *
        Chen.primitiveLogDerivMajorantAt data q T) *
        ((1 + (τ /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ := by
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hσhalf : (1 : ℝ) / 2 ≤ σ := hγpos.trans hσ.1
  have hσpos : 0 < σ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hσhalf
  have hhalf : 1 -
      Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q τ / 2 ≤ σ := by
    have htwo : 2 / Real.sqrt (Real.log (x : ℝ)) =
        2 * (1 / Real.sqrt (Real.log (x : ℝ))) := by ring
    rw [htwo] at hwidth
    linarith [hσ.1]
  have hraw := norm_bvSmoothedLogDerivIntegrand_le_classical
    data K hq hx hlarge hχ ((σ : ℂ) + (τ : ℂ) * Complex.I)
      (by simpa using hσpos) (by simpa using hhalf)
  have hxone : (1 : ℝ) ≤ x := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hxne : (x : ℝ) ≠ 1 := by
    exact_mod_cast (show x ≠ 1 by omega)
  have hxpow : (x : ℝ) ^ σ ≤ Real.exp 1 * (x : ℝ) := by
    calc
      (x : ℝ) ^ σ ≤
          (x : ℝ) ^ (1 + 1 / Real.log (x : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hxone hσ.2
      _ = Real.exp 1 * (x : ℝ) := by
        rw [Real.rpow_add hxpos, Real.rpow_one,
          show (1 : ℝ) / Real.log (x : ℝ) =
            (Real.log (x : ℝ))⁻¹ from one_div _,
          Real.rpow_inv_log hxpos hxne]
        ring
  have hσinv : σ⁻¹ ≤ 2 := by
    have := (inv_le_inv₀ hσpos
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr hσhalf
    rwa [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at this
  rw [show (((σ : ℂ) + (τ : ℂ) * Complex.I).re) = σ by simp,
    show (((σ : ℂ) + (τ : ℂ) * Complex.I).im) = τ by simp] at hraw
  rw [hτ] at hraw
  unfold Chen.primitiveLogDerivMajorantAt
  have hM0 : 0 ≤ data.cLogDeriv *
      ((q : ℝ) ^ ((1 : ℝ) / E) +
        Real.log ((q : ℝ) * (T + 2)) + 1) ^ 2 :=
    mul_nonneg data.cLogDeriv_pos.le (sq_nonneg _)
  have hQ0 : 0 ≤
      ((1 + (τ /
        Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ := by
    positivity
  calc
    ‖bvSmoothedLogDerivIntegrand K x χ
        ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      (x : ℝ) ^ σ *
          (σ⁻¹ *
            ((1 + (τ /
              Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
        (data.cLogDeriv *
          ((q : ℝ) ^ ((1 : ℝ) / E) +
            Real.log ((q : ℝ) * (T + 2)) + 1) ^ 2) := hraw
    _ ≤ (Real.exp 1 * (x : ℝ)) * (2 *
          ((1 + (τ /
            Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
        (data.cLogDeriv *
          ((q : ℝ) ^ ((1 : ℝ) / E) +
            Real.log ((q : ℝ) * (T + 2)) + 1) ^ 2) := by
      gcongr
    _ = (2 * Real.exp 1 * (x : ℝ) *
          (data.cLogDeriv *
            ((q : ℝ) ^ ((1 : ℝ) / E) +
              Real.log ((q : ℝ) * (T + 2)) + 1) ^ 2)) *
        ((1 + (τ /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ := by ring
/-- Each horizontal side is its pointwise bound times the exact width
`alpha - gamma`. -/
theorem norm_intervalIntegral_bvSmoothedLogDeriv_horizontal_le_classical
    {E : ℕ} (data : Chen.PrimitiveZeroFreeRegionDataAt E)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {T τ : ℝ} (hτ : |τ| = T)
    (hwidth : 2 / Real.sqrt (Real.log (x : ℝ)) <
      Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q τ) :
    ‖∫ σ : ℝ in
        (1 - 1 / Real.sqrt (Real.log (x : ℝ)))..
          (1 + 1 / Real.log (x : ℝ)),
        bvSmoothedLogDerivIntegrand K x χ
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      ((2 * Real.exp 1 * (x : ℝ) *
          Chen.primitiveLogDerivMajorantAt data q T) *
        ((1 + (τ /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| := by
  let C : ℝ := (2 * Real.exp 1 * (x : ℝ) *
      Chen.primitiveLogDerivMajorantAt data q T) *
    ((1 + (τ /
      Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσmem
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hγα : 1 - 1 / Real.sqrt (Real.log (x : ℝ)) ≤
      1 + 1 / Real.log (x : ℝ) := by
    have h1 : 0 ≤ 1 / Real.sqrt (Real.log (x : ℝ)) := by positivity
    have h2 : 0 ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  have hσ : σ ∈ Set.Icc
      (1 - 1 / Real.sqrt (Real.log (x : ℝ)))
      (1 + 1 / Real.log (x : ℝ)) := by
    rw [← Set.uIcc_of_le hγα]
    exact Set.uIoc_subset_uIcc hσmem
  exact norm_bvSmoothedLogDerivIntegrand_horizontal_le_classical
    data K hq hx hlarge hγpos hχ hτ hσ hwidth
/-- At the chosen square-scale height, either horizontal side gains the
factor `(log x)^(-44(K+1))`. -/
theorem norm_intervalIntegral_bvSmoothedLogDeriv_horizontal_at_height_le
    {E : ℕ} (data : Chen.PrimitiveZeroFreeRegionDataAt E)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {τ : ℝ} (hτ : |τ| = bvSmoothingContourHeight K x)
    (hwidth : 2 / Real.sqrt (Real.log (x : ℝ)) <
      Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q τ) :
    ‖∫ σ : ℝ in
        (1 - 1 / Real.sqrt (Real.log (x : ℝ)))..
          (1 + 1 / Real.log (x : ℝ)),
        bvSmoothedLogDerivIntegrand K x χ
          ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      ((2 * Real.exp 1 * (x : ℝ) *
          Chen.primitiveLogDerivMajorantAt data q
            (bvSmoothingContourHeight K x)) *
        (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| := by
  let a : ℝ := Real.log (x : ℝ) ^ (11 * (K + 1))
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have ha : 0 < a := by dsimp only [a]; exact pow_pos hlog _
  have hheight : bvSmoothingContourHeight K x = a ^ 2 := rfl
  have hτa : |τ| = a ^ 2 := by rwa [hheight] at hτ
  have hqtail := scaled_quartic_at_sq_le_inv_four ha hτa
  have hbase :=
    norm_intervalIntegral_bvSmoothedLogDeriv_horizontal_le_classical
      data K hq hx hlarge hγpos hχ hτ hwidth
  apply hbase.trans
  have hC0 : 0 ≤ 2 * Real.exp 1 * (x : ℝ) *
      Chen.primitiveLogDerivMajorantAt data q
        (bvSmoothingContourHeight K x) := by
    unfold Chen.primitiveLogDerivMajorantAt
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le)
        (Nat.cast_nonneg x))
      (mul_nonneg data.cLogDeriv_pos.le (sq_nonneg _))
  have hwidth0 : 0 ≤ |(1 + 1 / Real.log (x : ℝ)) -
      (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| := abs_nonneg _
  have ha4 : a ^ 4 = Real.log (x : ℝ) ^ (44 * (K + 1)) := by
    dsimp only [a]
    rw [← pow_mul]
    congr 1
    omega
  calc
    ((2 * Real.exp 1 * (x : ℝ) *
          Chen.primitiveLogDerivMajorantAt data q
            (bvSmoothingContourHeight K x)) *
        ((1 + (τ /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| ≤
      ((2 * Real.exp 1 * (x : ℝ) *
          Chen.primitiveLogDerivMajorantAt data q
            (bvSmoothingContourHeight K x)) * (a ^ 4)⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| := by
      gcongr
    _ = ((2 * Real.exp 1 * (x : ℝ) *
          Chen.primitiveLogDerivMajorantAt data q
            (bvSmoothingContourHeight K x)) *
        (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
        |(1 + 1 / Real.log (x : ℝ)) -
          (1 - 1 / Real.sqrt (Real.log (x : ℝ)))| := by rw [ha4]
/-- On the original `alpha`-line the logarithmic derivative is controlled
by absolute convergence, so this bound is independent of every zero-free
region and of primitivity. -/
theorem norm_bvSmoothedLogDerivIntegrand_alpha_le
    {q : ℕ} [NeZero q] (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) (ν : ℝ) :
    ‖bvSmoothedLogDerivIntegrand K x χ
        (Chen.lemma6AlphaPoint x ν)‖ ≤
      (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
        ((1 + (ν /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ := by
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  have hαpos : 0 < α := by dsimp only [α]; positivity
  have hαone : 1 ≤ α := by
    dsimp only [α]
    have : 0 ≤ (1 : ℝ) / Real.log (x : ℝ) := by positivity
    linarith
  have ex : ‖(x : ℂ) ^ Chen.lemma6AlphaPoint x ν‖ =
      Real.exp 1 * (x : ℝ) :=
    Chen.norm_nat_cpow_eq21AlphaPoint hx ν
  have ek : ‖Chen.lemma6SmoothingMellinKernel
        (bvSmoothingParameter K x) (Chen.lemma6AlphaPoint x ν)‖ ≤
      ((1 + (ν /
        Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ := by
    have hk := norm_bvSmoothingMellinKernel_le_quartic
      K hx hlarge hαpos ν
    have hαinv : α⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hαone
    change ‖Chen.lemma6SmoothingMellinKernel
      (bvSmoothingParameter K x)
      ((α : ℂ) + (ν : ℂ) * Complex.I)‖ ≤ _
    exact hk.trans (by
      calc
        α⁻¹ *
            ((1 + (ν /
              Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ ≤
          1 *
            ((1 + (ν /
              Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hαinv (by positivity)
        _ = _ := one_mul _)
  have eL :
      ‖deriv (DirichletCharacter.LFunction χ)
            (Chen.lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ
            (Chen.lemma6AlphaPoint x ν)‖ ≤
        4 * Real.log (x : ℝ) ^ 2 :=
    (Chen.lemma6_norm_logDeriv_le_majorant χ
      (Chen.one_lt_lemma6AlphaPoint_re hx ν)).trans
        (Chen.lemma6LogDerivMajorant_alpha_le hx ν)
  unfold bvSmoothedLogDerivIntegrand
  simp only [norm_neg, norm_mul]
  have hfirst := mul_le_mul ex.le ek (norm_nonneg _) (by positivity)
  have hall := mul_le_mul hfirst eL (norm_nonneg _) (by positivity)
  exact hall.trans_eq (by ring)
/-- Direct bound for the discarded tails of the original `alpha`-line.
The right side retains the truncation factor, so choosing `T` much larger
than the Mellin scale produces an arbitrary logarithmic saving. -/
theorem norm_integral_bvSmoothedLogDeriv_alpha_compl_Ioc_le
    {q : ℕ} [NeZero q] (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ,
        bvSmoothedLogDerivIntegrand K x χ
          (Chen.lemma6AlphaPoint x ν)‖ ≤
      (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
        ((1 + (T /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2)⁻¹) *
        (Real.log (x : ℝ) ^ (11 * (K + 1)) * Real.pi) := by
  let a : ℝ := Real.log (x : ℝ) ^ (11 * (K + 1))
  let C : ℝ := 4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2
  let g : ℝ → ℝ := fun ν => ((1 + (ν / a) ^ 2) ^ 2)⁻¹
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have ha : 0 < a := by
    dsimp only [a]
    exact pow_pos hlog _
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hg : MeasureTheory.Integrable g := by
    simpa only [g] using integrable_scaled_quartic ha
  have hmajor : MeasureTheory.Integrable (fun ν => C * g ν) :=
    hg.const_mul C
  have hmain :
      ‖∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ,
          bvSmoothedLogDerivIntegrand K x χ
            (Chen.lemma6AlphaPoint x ν)‖ ≤
        ∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, C * g ν := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajor.integrableOn
    filter_upwards with ν
    exact norm_bvSmoothedLogDerivIntegrand_alpha_le
      K hx hlarge χ ν
  have htail := integral_scaled_quartic_compl_Ioc_le ha hT
  calc
    ‖∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ,
        bvSmoothedLogDerivIntegrand K x χ
          (Chen.lemma6AlphaPoint x ν)‖ ≤
        ∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, C * g ν := hmain
    _ = C * (∫ ν : ℝ in (Set.Ioc (-T) T)ᶜ, g ν) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ C * ((1 + (T / a) ^ 2)⁻¹ * (a * Real.pi)) :=
      mul_le_mul_of_nonneg_left (by simpa only [g] using htail) hC0
    _ = (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
        ((1 + (T /
          Real.log (x : ℝ) ^ (11 * (K + 1))) ^ 2)⁻¹) *
        (Real.log (x : ℝ) ^ (11 * (K + 1)) * Real.pi) := by
      dsimp only [C, a]
      ring
/-- At the chosen square-scale contour height, the original-line tail
loses one inverse Mellin scale, namely `(log x)^(-11(K+1))`. -/
theorem norm_integral_bvSmoothedLogDeriv_alpha_tail_le
    {q : ℕ} [NeZero q] (K : ℕ) {x : ℕ} (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (χ : DirichletCharacter ℂ q) :
    ‖∫ ν : ℝ in
        (Set.Ioc (-(bvSmoothingContourHeight K x))
          (bvSmoothingContourHeight K x))ᶜ,
        bvSmoothedLogDerivIntegrand K x χ
          (Chen.lemma6AlphaPoint x ν)‖ ≤
      (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
        ((Real.log (x : ℝ) ^ (11 * (K + 1)))⁻¹ * Real.pi) := by
  let a : ℝ := Real.log (x : ℝ) ^ (11 * (K + 1))
  let C : ℝ := 4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have ha : 0 < a := by dsimp only [a]; exact pow_pos hlog _
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hbase := norm_integral_bvSmoothedLogDeriv_alpha_compl_Ioc_le
    K hx hlarge χ (bvSmoothingContourHeight_nonneg K x)
  have hheight : bvSmoothingContourHeight K x = a ^ 2 := by
    rfl
  have hratio : a ^ 2 / a = a := by field_simp [ha.ne']
  have hcore : (1 + a ^ 2)⁻¹ * a ≤ a⁻¹ := by
    field_simp [ha.ne']
    nlinarith [sq_nonneg a]
  have htail :
      (1 + (bvSmoothingContourHeight K x / a) ^ 2)⁻¹ *
          (a * Real.pi) ≤ a⁻¹ * Real.pi := by
    rw [hheight, hratio]
    calc
      (1 + a ^ 2)⁻¹ * (a * Real.pi) =
          ((1 + a ^ 2)⁻¹ * a) * Real.pi := by ring
      _ ≤ a⁻¹ * Real.pi :=
        mul_le_mul_of_nonneg_right hcore Real.pi_pos.le
  apply hbase.trans
  change C *
      ((1 + (bvSmoothingContourHeight K x / a) ^ 2)⁻¹) *
        (a * Real.pi) ≤ C * (a⁻¹ * Real.pi)
  calc
    C * ((1 + (bvSmoothingContourHeight K x / a) ^ 2)⁻¹) *
          (a * Real.pi) =
        C * (((1 + (bvSmoothingContourHeight K x / a) ^ 2)⁻¹) *
          (a * Real.pi)) := by ring
    _ ≤ C * (a⁻¹ * Real.pi) :=
      mul_le_mul_of_nonneg_left htail hC0
/-- Finite-contour replacement for the full adjustable Perron integral.
The shifted vertical segment, both horizontal sides, and the original-line
tail are all retained as explicit errors at the chosen contour height. -/
theorem norm_integral_bvSmoothedLogDeriv_alpha_le_finite_classical
    {E : ℕ} (data : Chen.PrimitiveZeroFreeRegionDataAt E)
    {x q : ℕ} [NeZero q] (K : ℕ) (hq : 2 ≤ q) (hx : 2 ≤ x)
    (hlarge : (10 : ℝ) ^ 4 ≤
      Real.log (x : ℝ) ^ (10 * (K + 1)))
    (hγpos : (1 : ℝ) / 2 ≤
      1 - 1 / Real.sqrt (Real.log (x : ℝ)))
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (hwidth : ∀ t : ℝ, |t| ≤ bvSmoothingContourHeight K x →
      2 / Real.sqrt (Real.log (x : ℝ)) <
        Chen.primitiveZeroFreeWidthAt E data.cHeight data.cSiegel q t) :
    ‖∫ t : ℝ,
        bvSmoothedLogDerivIntegrand K x χ
          (Chen.lemma6AlphaPoint x t)‖ ≤
      4 * bvSmoothingContourHeight K x *
          ((x : ℝ) ^
            (1 - 1 / Real.sqrt (Real.log (x : ℝ))) *
            Chen.primitiveLogDerivMajorantAt data q
              (bvSmoothingContourHeight K x)) +
        2 * (((2 * Real.exp 1 * (x : ℝ) *
            Chen.primitiveLogDerivMajorantAt data q
              (bvSmoothingContourHeight K x)) *
            (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
          |(1 + 1 / Real.log (x : ℝ)) -
            (1 - 1 / Real.sqrt (Real.log (x : ℝ)))|) +
        (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
          ((Real.log (x : ℝ) ^ (11 * (K + 1)))⁻¹ * Real.pi) := by
  let T : ℝ := bvSmoothingContourHeight K x
  let γ : ℝ := 1 - 1 / Real.sqrt (Real.log (x : ℝ))
  let α : ℝ := 1 + 1 / Real.log (x : ℝ)
  let F : ℂ → ℂ := bvSmoothedLogDerivIntegrand K x χ
  let A : ℂ := ∫ t : ℝ in (-T)..T,
    F ((α : ℂ) + (t : ℂ) * Complex.I)
  let G : ℂ := ∫ t : ℝ in (-T)..T,
    F ((γ : ℂ) + (t : ℂ) * Complex.I)
  let bot : ℂ := ∫ σ : ℝ in γ..α,
    F ((σ : ℂ) - (T : ℂ) * Complex.I)
  let top : ℂ := ∫ σ : ℝ in γ..α,
    F ((σ : ℂ) + (T : ℂ) * Complex.I)
  let tail : ℂ := ∫ t : ℝ in (Set.Ioc (-T) T)ᶜ,
    F ((α : ℂ) + (t : ℂ) * Complex.I)
  have hT : 0 ≤ T := by
    dsimp only [T]
    exact bvSmoothingContourHeight_nonneg K x
  have hαI := integrable_bvSmoothedLogDerivIntegrand_alpha
    K hx hlarge χ
  have hsplit : A + tail = ∫ t : ℝ,
      bvSmoothedLogDerivIntegrand K x χ
        (Chen.lemma6AlphaPoint x t) := by
    have hs := MeasureTheory.integral_add_compl
      (s := Set.Ioc (-T) T) measurableSet_Ioc hαI
    rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T)] at hs
    simpa only [A, tail, F, α, Chen.lemma6AlphaPoint] using hs
  have hrect : bot - top + Complex.I • A - Complex.I • G = 0 := by
    simpa only [bot, top, A, G, F, γ, α] using
      (bvSmoothedLogDeriv_finite_rectangle_classical
        data K hq hx hγpos hχ hT hwidth)
  have hIA : Complex.I • A = Complex.I • G - bot + top := by
    linear_combination hrect
  have hAG : ‖A‖ ≤ ‖G‖ + ‖bot‖ + ‖top‖ := by
    calc
      ‖A‖ = ‖Complex.I • A‖ := by simp
      _ = ‖Complex.I • G - bot + top‖ := congrArg norm hIA
      _ ≤ ‖Complex.I • G - bot‖ + ‖top‖ := norm_add_le _ _
      _ ≤ (‖Complex.I • G‖ + ‖bot‖) + ‖top‖ := by
        linarith [norm_sub_le (Complex.I • G) bot]
      _ = ‖G‖ + ‖bot‖ + ‖top‖ := by simp
  have hG : ‖G‖ ≤
      4 * T * ((x : ℝ) ^ γ *
        Chen.primitiveLogDerivMajorantAt data q T) := by
    simpa only [G, F, γ, T, Chen.lemma6Equation21Point] using
      (norm_intervalIntegral_bvSmoothedLogDeriv_gamma_le_classical
        data K hq hx hlarge hγpos hχ hT hwidth)
  have htop : ‖top‖ ≤
      ((2 * Real.exp 1 * (x : ℝ) *
          Chen.primitiveLogDerivMajorantAt data q T) *
        (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
        |α - γ| := by
    simpa only [top, F, γ, α, T, abs_of_nonneg hT] using
      (norm_intervalIntegral_bvSmoothedLogDeriv_horizontal_at_height_le
        data K hq hx hlarge hγpos hχ
          (abs_of_nonneg hT) (hwidth T (by rw [abs_of_nonneg hT])))
  have hbot : ‖bot‖ ≤
      ((2 * Real.exp 1 * (x : ℝ) *
          Chen.primitiveLogDerivMajorantAt data q T) *
        (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
        |α - γ| := by
    have hb :=
      norm_intervalIntegral_bvSmoothedLogDeriv_horizontal_at_height_le
        data K hq hx hlarge hγpos hχ
          (show |-T| = bvSmoothingContourHeight K x by
            rw [abs_neg, abs_of_nonneg hT])
          (hwidth (-T) (by rw [abs_neg, abs_of_nonneg hT]))
    simpa only [bot, F, γ, α, T, Complex.ofReal_neg, neg_mul,
      sub_eq_add_neg] using hb
  have htail : ‖tail‖ ≤
      (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
        ((Real.log (x : ℝ) ^ (11 * (K + 1)))⁻¹ * Real.pi) := by
    simpa only [tail, F, α, T, Chen.lemma6AlphaPoint] using
      (norm_integral_bvSmoothedLogDeriv_alpha_tail_le
        K hx hlarge χ)
  calc
    ‖∫ t : ℝ,
        bvSmoothedLogDerivIntegrand K x χ
          (Chen.lemma6AlphaPoint x t)‖ = ‖A + tail‖ :=
      congrArg norm hsplit.symm
    _ ≤ ‖A‖ + ‖tail‖ := norm_add_le _ _
    _ ≤ (‖G‖ + ‖bot‖ + ‖top‖) + ‖tail‖ := by linarith
    _ ≤
        4 * T * ((x : ℝ) ^ γ *
          Chen.primitiveLogDerivMajorantAt data q T) +
          2 * (((2 * Real.exp 1 * (x : ℝ) *
              Chen.primitiveLogDerivMajorantAt data q T) *
              (Real.log (x : ℝ) ^ (44 * (K + 1)))⁻¹) *
            |α - γ|) +
          (4 * Real.exp 1 * (x : ℝ) * Real.log (x : ℝ) ^ 2) *
            ((Real.log (x : ℝ) ^ (11 * (K + 1)))⁻¹ *
              Real.pi) := by
      linarith [hG, hbot, htop, htail]
    _ = _ := by
      dsimp only [T, γ, α]
end Chen.BombieriVinogradov

end

