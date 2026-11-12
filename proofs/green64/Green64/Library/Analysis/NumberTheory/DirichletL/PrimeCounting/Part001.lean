module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part012
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Function.Floor
public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.IdealLogDerivative.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part019
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part011
public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.UnitRows
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part022
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part006

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / PrimeCounting / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.PrimeCounting.AnnularPrimeMass -/

section

namespace OAI

namespace SevenEighths.PNT.AnnularPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter MeasureTheory
open SevenEighths.IdealMangoldt SevenEighths.PNT.IdealPrimeMass
open scoped BigOperators Classical Topology ContDiff

noncomputable section

def cumulative (f : ℕ → ℝ) (t : ℝ) : ℝ := cumsum f (⌊t⌋₊ + 1)

def scaledCumulative (f : ℕ → ℝ) (x y : ℝ) : ℝ := cumulative f (x * y) / x

theorem cumulative_ratio_tendsto {f : ℕ → ℝ} {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A)) :
    Tendsto (fun t : ℝ => cumulative f t / t) atTop (𝓝 A) := by
  have ht : Tendsto (fun t : ℝ => ⌊t⌋₊ + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_succ _) tendsto_nat_floor_atTop
  have hr : Tendsto (fun t : ℝ => ((⌊t⌋₊ + 1 : ℕ) : ℝ) / t) atTop (𝓝 1) := by
    convert (tendsto_nat_floor_div_atTop (R := ℝ)).add
      (show Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) by simpa only [one_div] using tendsto_inv_atTop_zero) using 1 <;> simp [add_div]
  convert (h.comp ht).mul hr using 1
  · ext t
    simp only [Function.comp_def, cumulative]
    field_simp
  · simp

theorem scaledCumulative_tendsto {f : ℕ → ℝ} {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ => scaledCumulative f x y) atTop (𝓝 (A * y)) := by
  have ht : Tendsto (fun x : ℝ => x * y) atTop atTop := tendsto_id.atTop_mul_const hy
  apply ((cumulative_ratio_tendsto h).comp ht).mul_const y |>.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold scaledCumulative
  dsimp only [Function.comp_def]
  field_simp

theorem cumulative_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (t : ℝ) :
    0 ≤ cumulative f t := cumsum_nonneg hf _

theorem scaledCumulative_bound {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    {x y b : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (hyb : y ≤ b) :
    ‖scaledCumulative f x y‖ ≤ C * (b + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [scaledCumulative, Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (cumulative_nonneg hf _) hx0.le)]
  calc
    cumulative f (x * y) / x ≤ (C * (⌊x * y⌋₊ + 1 : ℕ)) / x := by
      exact div_le_div_of_nonneg_right (hbound _) hx0.le
    _ ≤ (C * (x * y + 1)) / x := by
      gcongr
      push_cast
      linarith [Nat.floor_le (mul_nonneg hx0.le hy)]
    _ ≤ C * (b + 1) := by
      rw [div_le_iff₀ hx0]
      nlinarith [mul_le_mul_of_nonneg_left hyb hx0.le,
        mul_nonneg hC (sub_nonneg.mpr hx)]

theorem measurable_cumulative (f : ℕ → ℝ) : Measurable (cumulative f) :=
  (measurable_of_countable (cumsum f)).comp (measurable_id.nat_floor.add_const 1)

theorem measurable_scaledCumulative (f : ℕ → ℝ) (x : ℝ) :
    Measurable (scaledCumulative f x) :=
  ((measurable_cumulative f).comp (measurable_const.mul measurable_id)).div_const x

def annularSum (f : ℕ → ℝ) (φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊x * a⌋₊ ⌊x * b⌋₊, f n * φ (n / x)

theorem annularSum_div_eq_integral (f : ℕ → ℝ) (φ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    {a b x : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x)
    (hφa : φ a = 0) (hφb : φ b = 0) :
    annularSum f φ a b x / x =
      -(∫ y in a..b, deriv φ y * scaledCumulative f x y) := by
  let g : ℝ → ℝ := fun t => φ (t / x)
  have hg (t : ℝ) : HasDerivAt g (deriv φ (t / x) / x) t := by
    convert (hφ (t / x)).hasDerivAt.comp t ((hasDerivAt_id t).div_const x) using 1 <;>
      simp only [g, Function.comp_def, div_eq_mul_inv, id_eq, one_mul]
  have hgc : Continuous (deriv g) := by
    have heq : deriv g = fun t => deriv φ (t / x) / x := funext (fun t => (hg t).deriv)
    rw [heq]
    exact (hφ'.comp (continuous_id.div_const x)).div_const x
  have h := sum_mul_eq_sub_sub_integral_mul f (a := x * a) (b := x * b)
    (mul_nonneg hx.le ha) (mul_le_mul_of_nonneg_left hab hx.le)
    (fun t _ => (hg t).differentiableAt) hgc.integrableOn_Icc
  have hcum (t : ℝ) : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, f k) = cumulative f t := by
    simp only [cumulative, cumsum, Nat.range_succ_eq_Icc_zero]
  simp_rw [hcum, (hg _).deriv] at h
  have hga : g (x * a) = 0 := by simp only [g, mul_div_cancel_left₀ _ hx.ne', hφa]
  have hgb : g (x * b) = 0 := by simp only [g, mul_div_cancel_left₀ _ hx.ne', hφb]
  rw [hga, hgb, zero_mul, zero_mul, sub_zero, zero_sub,
    ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hx.le)] at h
  have hs : annularSum f φ a b x =
      -(∫ t in x * a..x * b, (deriv φ (t / x) / x) * cumulative f t) := by
    rw [← h]
    unfold annularSum g
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hs, neg_div]
  congr 1
  have hi := intervalIntegral.integral_comp_mul_left
    (fun t => (deriv φ (t / x) / x) * cumulative f t) hx.ne' (a := a) (b := b)
  simp only [smul_eq_mul, ← div_eq_inv_mul] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro y hy
  simp only [mul_div_cancel_left₀ _ hx.ne', scaledCumulative]
  ring

theorem integral_scaledCumulative_tendsto {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {A C a b : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (ha : 0 < a) (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun x : ℝ => ∫ y in a..b, g y * scaledCumulative f x y) atTop
      (𝓝 (∫ y in a..b, g y * (A * y))) := by
  simp_rw [intervalIntegral.integral_of_le hab]
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖g y‖ * (C * (b + 1)))
  · exact Eventually.of_forall (fun x =>
      (hg.measurable.mul (measurable_scaledCumulative f x)).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (scaledCumulative_bound hf hC hbound hx (ha.le.trans hy.1.le) hy.2) (norm_nonneg _)
  · exact (hg.norm.mul_const _).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact (scaledCumulative_tendsto hmass (ha.trans hy.1)).const_mul (g y)

theorem annularSum_div_tendsto {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {A C a b : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => annularSum f φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  have h := (integral_scaledCumulative_tendsto hf hC hbound hmass ha hab (deriv φ) hφ').neg
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => y) (u' := fun _ => (1 : ℝ)) (v := φ) (v' := deriv φ)
    (fun y _ => hasDerivAt_id y) (fun y _ => (hφ y).hasDerivAt)
    (continuous_const.intervalIntegrable a b) (hφ'.intervalIntegrable a b)
  have heq : -(∫ y in a..b, deriv φ y * (A * y)) = A * ∫ y in a..b, φ y := by
    have hfun : (fun y => deriv φ y * (A * y)) = fun y => A * (y * deriv φ y) := by
      ext y
      ring
    rw [hfun, intervalIntegral.integral_const_mul, hibp, hφa, hφb]
    simp
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (annularSum_div_eq_integral f φ hφ hφ' ha.le hab hx hφa hφb).symm

def annularPrimeIdeals (C : Set (Ideal O)) (a b x : ℝ) : Finset (Ideal O) :=
  (primeIdealsBelow C (⌊x * b⌋₊ + 1)).filter (fun P => ⌊x * a⌋₊ < Ideal.absNorm P)

@[simp] theorem mem_annularPrimeIdeals (C : Set (Ideal O)) (a b x : ℝ) (P : Ideal O) :
    P ∈ annularPrimeIdeals C a b x ↔
      P ∈ C ∧ Prime P ∧ ⌊x * a⌋₊ < Ideal.absNorm P ∧ Ideal.absNorm P ≤ ⌊x * b⌋₊ := by
  simp only [annularPrimeIdeals, Finset.mem_filter, mem_primeIdealsBelow, Nat.lt_succ_iff]
  tauto

def primeAnnularSum (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ P ∈ annularPrimeIdeals C a b x, φ (Ideal.absNorm P / x)

def primeLogAnnularSum (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P) * φ (Ideal.absNorm P / x)

theorem primeLogAnnularSum_eq (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) :
    primeLogAnnularSum C φ a b x = annularSum (primeClassCoeff C) φ a b x := by
  have hmap : ∀ P ∈ annularPrimeIdeals C a b x,
      Ideal.absNorm P ∈ Finset.Ioc ⌊x * a⌋₊ ⌊x * b⌋₊ := by
    intro P hP
    exact Finset.mem_Ioc.mpr ((mem_annularPrimeIdeals C a b x P).mp hP).2.2
  rw [primeLogAnnularSum, ← Finset.sum_fiberwise_of_maps_to hmap]
  unfold annularSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeClassCoeff_eq_sum_log, Finset.sum_mul]
  apply Finset.sum_congr
  · ext P
    simp only [Finset.mem_filter, mem_annularPrimeIdeals, mem_normFiber]
    constructor
    · rintro ⟨⟨hC, hP, hN⟩, heq⟩
      exact ⟨heq, hC, hP⟩
    · rintro ⟨heq, hC, hP⟩
      exact ⟨⟨hC, hP, heq ▸ Finset.mem_Ioc.mp hn⟩, heq⟩
  · intro P hP
    rw [(mem_normFiber n P).mp (Finset.mem_filter.mp hP).1]

theorem primeClassCoeff_chebyshev (C : Set (Ideal O)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N := by
  obtain ⟨B, hB⟩ := classCoeff_chebyshev {I | I ∈ C ∧ Prime I}
  have hbound (N : ℕ) : cumsum (primeClassCoeff C) N ≤ B * N := by
    convert hB N using 1
    congr 1
    funext n
    exact (Complex.norm_of_nonneg (primeClassCoeff_nonneg C n)).symm
  refine ⟨B, ?_, hbound⟩
  have h := (cumsum_nonneg (primeClassCoeff_nonneg C) 1).trans (hbound 1)
  simpa only [Nat.cast_one, mul_one, Pi.zero_apply] using h

theorem primeLogAnnularSum_div_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => primeLogAnnularSum C φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  obtain ⟨B, hB, hbound⟩ := primeClassCoeff_chebyshev C
  simpa only [primeLogAnnularSum_eq] using annularSum_div_tendsto
    (primeClassCoeff_nonneg C) hB hbound (primeClassCoeff_ratio_tendsto C hmass)
    φ hφ hφ' ha hab hφa hφb

theorem norm_bounds_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    x * a < (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ x * b := by
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  exact ⟨(Nat.floor_lt (mul_nonneg hx.le ha)).mp h.2.2.1,
    (Nat.le_floor_iff (mul_nonneg hx.le (ha.trans hab))).mp h.2.2.2⟩

theorem ratio_mem_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    (Ideal.absNorm P : ℝ) / x ∈ Set.Icc a b := by
  obtain ⟨hl, hu⟩ := norm_bounds_of_mem_annularPrimeIdeals ha hab hx hP
  exact ⟨(le_div_iff₀ hx).mpr (by nlinarith), (div_le_iff₀ hx).mpr (by nlinarith)⟩

theorem log_norm_difference_bound {a b x : ℝ} (ha : 0 < a) (_hab : a ≤ b)
    (hx : 0 < x) {n : ℕ} (hn : (n : ℝ) / x ∈ Set.Icc a b) :
    |Real.log x - Real.log n| ≤ |Real.log a| + |Real.log b| := by
  have hn0 : 0 < (n : ℝ) := by
    have h := (le_div_iff₀ hx).mp hn.1
    exact (mul_pos ha hx).trans_le h
  have hl := Real.log_le_log ha hn.1
  have hu := Real.log_le_log (ha.trans_le hn.1) hn.2
  rw [Real.log_div hn0.ne' hx.ne'] at hl hu
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
    le_abs_self (Real.log b), neg_abs_le (Real.log b), abs_nonneg (Real.log a),
    abs_nonneg (Real.log b)]

theorem annularPrime_card_div_bound (C : Set (Ideal O)) {B a b x : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N)
    (ha : 0 < a) (hab : a ≤ b) (hx : 1 ≤ x) (hxa : 1 < x * a) :
    ((annularPrimeIdeals C a b x).card : ℝ) / x ≤ B * (b + 1) / Real.log (x * a) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 < Real.log (x * a) := Real.log_pos hxa
  have hlower : Real.log (x * a) * (annularPrimeIdeals C a b x).card ≤
      ∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P) := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro P hP
    exact Real.log_le_log (mul_pos hx0 ha)
      (norm_bounds_of_mem_annularPrimeIdeals ha.le hab hx0 hP).1.le
  have hupper : (∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P)) ≤
      cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) := by
    rw [← primeLogMass_eq_cumsum, primeLogMass]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro P hP _
    rw [← value_prime ((mem_primeIdealsBelow C _ P).mp hP).2.1]
    exact value_nonneg P
  have hnorm := scaledCumulative_bound (primeClassCoeff_nonneg C) hB hbound hx
    (ha.le.trans hab) (le_refl b)
  have hcum : cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) / x ≤ B * (b + 1) :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, scaledCumulative, cumulative] using hnorm)
  apply (le_div_iff₀ hlog).mpr
  calc
    ((annularPrimeIdeals C a b x).card : ℝ) / x * Real.log (x * a) =
        (Real.log (x * a) * (annularPrimeIdeals C a b x).card) / x := by ring
    _ ≤ (∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P)) / x :=
      div_le_div_of_nonneg_right hlower hx0.le
    _ ≤ cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) / x :=
      div_le_div_of_nonneg_right hupper hx0.le
    _ ≤ _ := hcum

theorem primeAnnularSum_log_error_bound (C : Set (Ideal O)) (φ : ℝ → ℝ)
    {B M a b x : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N)
    (hM : 0 ≤ M) (hφ : ∀ y ∈ Set.Icc a b, |φ y| ≤ M)
    (ha : 0 < a) (hab : a ≤ b) (hx : 1 ≤ x) (hxa : 1 < x * a) :
    ‖Real.log x * primeAnnularSum C φ a b x / x - primeLogAnnularSum C φ a b x / x‖ ≤
      ((|Real.log a| + |Real.log b|) * M) * (B * (b + 1) / Real.log (x * a)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have heq : Real.log x * primeAnnularSum C φ a b x - primeLogAnnularSum C φ a b x =
      ∑ P ∈ annularPrimeIdeals C a b x,
        (Real.log x - Real.log (Ideal.absNorm P)) * φ (Ideal.absNorm P / x) := by
    simp only [primeAnnularSum, primeLogAnnularSum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      sub_mul]
  rw [← sub_div, heq, norm_div, Real.norm_of_nonneg hx0.le]
  calc
    _ ≤ (∑ P ∈ annularPrimeIdeals C a b x,
        ‖(Real.log x - Real.log (Ideal.absNorm P)) * φ (Ideal.absNorm P / x)‖) / x :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) hx0.le
    _ ≤ (∑ _P ∈ annularPrimeIdeals C a b x, (|Real.log a| + |Real.log b|) * M) / x := by
      apply div_le_div_of_nonneg_right _ hx0.le
      apply Finset.sum_le_sum
      intro P hP
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hratio := ratio_mem_of_mem_annularPrimeIdeals ha.le hab hx0 hP
      exact mul_le_mul (log_norm_difference_bound ha hab hx0 hratio) (hφ _ hratio)
        (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ((|Real.log a| + |Real.log b|) * M) * ((annularPrimeIdeals C a b x).card / x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (annularPrime_card_div_bound C hB hbound ha hab hx hxa)
      (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hM)

theorem primeAnnularSum_log_error_tendsto (C : Set (Ideal O)) (φ : ℝ → ℝ)
    (hφ : Continuous φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ => Real.log x * primeAnnularSum C φ a b x / x -
      primeLogAnnularSum C φ a b x / x) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := primeClassCoeff_chebyshev C
  obtain ⟨M, hMbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ.continuousOn
  have hM : 0 ≤ M := (norm_nonneg _).trans (hMbound a ⟨le_rfl, hab⟩)
  have hup : Tendsto (fun x : ℝ => ((|Real.log a| + |Real.log b|) * M) *
      (B * (b + 1) / Real.log (x * a))) atTop (𝓝 0) := by
    have hi := tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp (tendsto_id.atTop_mul_const ha))
    convert (hi.const_mul (B * (b + 1))).const_mul ((|Real.log a| + |Real.log b|) * M)
      using 1 <;> simp only [div_eq_mul_inv, mul_zero, Function.comp_def, id_eq]
  apply squeeze_zero_norm' _ hup
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_id.atTop_mul_const ha).eventually_gt_atTop 1] with x hx hxa
  exact primeAnnularSum_log_error_bound C φ hB hbound hM
    (fun y hy => by simpa only [Real.norm_eq_abs] using hMbound y hy) ha hab hx hxa

theorem primeAnnularSum_log_div_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => Real.log x * primeAnnularSum C φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  have h := (primeAnnularSum_log_error_tendsto C φ hφ.continuous ha hab).add
    (primeLogAnnularSum_div_tendsto C hmass φ hφ hφ' ha hab hφa hφb)
  simpa only [sub_add_cancel, zero_add] using h

theorem contDiff_powerWeight (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    {a b : ℝ} (ha : 0 < a) (hsupp : Function.support W ⊆ Set.Ioo a b) (r : ℝ) :
    ContDiff ℝ ∞ (fun y => W y * y ^ r) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst y
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ha] with y hy
    have hWy : W y = 0 := Function.notMem_support.mp (by
      intro h
      exact (not_lt_of_ge (hsupp h).1.le) hy)
    simp only [hWy, zero_mul]
  · exact hW.contDiffAt.mul (Real.contDiffAt_rpow_const_of_ne hy)

def weightedPrimeAnnularSum (C : Set (Ideal O)) (W : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ P ∈ annularPrimeIdeals C a b x,
    W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ)

theorem weightedPrimeAnnularSum_normalization (C : Set (Ideal O)) (W : ℝ → ℝ)
    (a b : ℝ) {x : ℝ} (hx : 0 < x) :
    Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeAnnularSum C W a b x =
      Real.log x * primeAnnularSum C (fun y => W y * y ^ (-5 / 6 : ℝ)) a b x / x := by
  have heq : primeAnnularSum C (fun y => W y * y ^ (-5 / 6 : ℝ)) a b x =
      weightedPrimeAnnularSum C W a b x / x ^ (-5 / 6 : ℝ) := by
    unfold primeAnnularSum weightedPrimeAnnularSum
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro P hP
    dsimp only
    rw [Real.div_rpow (Nat.cast_nonneg _) hx.le]
    ring
  have hp : x ^ (-5 / 6 : ℝ) * x = x ^ (1 / 6 : ℝ) := by
    calc
      _ = x ^ (-5 / 6 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((-5 / 6 : ℝ) + 1) := (Real.rpow_add hx _ _).symm
      _ = _ := by norm_num
  rw [heq, mul_div_assoc, div_div, hp]
  ring

theorem weightedPrimeAnnularSum_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (ha : 0 < a) (hab : a ≤ b) (hsupp : Function.support W ⊆ Set.Ioo a b) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeAnnularSum C W a b x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  let φ : ℝ → ℝ := fun y => W y * y ^ (-5 / 6 : ℝ)
  have hφ : ContDiff ℝ ∞ φ := contDiff_powerWeight W hW ha hsupp _
  have hWa : W a = 0 := Function.notMem_support.mp (fun h => (hsupp h).1.false)
  have hWb : W b = 0 := Function.notMem_support.mp (fun h => (hsupp h).2.false)
  have hφa : φ a = 0 := by simp only [φ, hWa, zero_mul]
  have hφb : φ b = 0 := by simp only [φ, hWb, zero_mul]
  have hint : (∫ y in a..b, φ y) = ∫ y, φ y := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hWy : W y = 0 := Function.notMem_support.mp
      (fun h => hy ⟨(hsupp h).1, (hsupp h).2.le⟩)
    simp only [φ, hWy, zero_mul]
  have h := primeAnnularSum_log_div_tendsto C hmass φ (hφ.differentiable (by simp))
    (hφ.continuous_deriv (by simp)) ha hab hφa hφb
  rw [hint] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (weightedPrimeAnnularSum_normalization C W a b hx).symm

theorem weightedPrimeAnnularSum_nat_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (ha : 0 < a) (hab : a ≤ b) (hsupp : Function.support W ⊆ Set.Ioo a b) :
    Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 6 : ℝ) *
      weightedPrimeAnnularSum C W a b N) atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) :=
  (weightedPrimeAnnularSum_tendsto C hmass W hW ha hab hsupp).comp tendsto_natCast_atTop_atTop

theorem exists_positive_support_annulus (W : ℝ → ℝ) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ Function.support W ⊆ Set.Ioo a b := by
  by_cases hne : (tsupport W).Nonempty
  · obtain ⟨m, hm, hmin⟩ := hc.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨M, hM, hmax⟩ := hc.exists_isMaxOn hne continuous_id.continuousOn
    have hm0 : 0 < m := hp hm
    have hmM : m ≤ M := hmin hM
    refine ⟨m / 2, M + 1, by positivity, by linarith, ?_⟩
    intro y hy
    have hyt : y ∈ tsupport W := subset_closure hy
    have hl : m ≤ y := hmin hyt
    have hu : y ≤ M := hmax hyt
    exact ⟨by linarith, by linarith⟩
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    intro y hy
    exact (hne ⟨y, subset_closure hy⟩).elim

theorem mem_annularPrimeIdeals_of_weight_ne_zero {C : Set (Ideal O)} {W : ℝ → ℝ}
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x)
    {P : Ideal O} (hC : P ∈ C) (hP : Prime P) (hW : W (Ideal.absNorm P / x) ≠ 0) :
    P ∈ annularPrimeIdeals C a b x := by
  have hy := hsupp hW
  apply (mem_annularPrimeIdeals C a b x P).mpr
  refine ⟨hC, hP, ?_, ?_⟩
  · apply (Nat.floor_lt (mul_nonneg hx.le ha.le)).mpr
    have h := (lt_div_iff₀ hx).mp hy.1
    nlinarith
  · apply (Nat.le_floor_iff (mul_nonneg hx.le (ha.le.trans hab))).mpr
    have h := (div_lt_iff₀ hx).mp hy.2
    nlinarith

def primeWeightTerm (C : Set (Ideal O)) (W : ℝ → ℝ) (x : ℝ) (P : Ideal O) : ℝ :=
  if P ∈ C ∧ Prime P then W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ) else 0

def weightedPrimeSum (C : Set (Ideal O)) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ᶠ P : Ideal O, primeWeightTerm C W x P

theorem primeWeightTerm_support_subset (C : Set (Ideal O)) (W : ℝ → ℝ)
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    Function.support (primeWeightTerm C W x) ⊆ (annularPrimeIdeals C a b x : Set (Ideal O)) := by
  intro P hP
  change primeWeightTerm C W x P ≠ 0 at hP
  unfold primeWeightTerm at hP
  split_ifs at hP with h
  · exact mem_annularPrimeIdeals_of_weight_ne_zero ha hab hsupp hx h.1 h.2
      (left_ne_zero_of_mul hP)
  · exact (hP rfl).elim

theorem primeWeightTerm_hasFiniteSupport (C : Set (Ideal O)) (W : ℝ → ℝ)
    (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0) {x : ℝ} (hx : 0 < x) :
    (Function.support (primeWeightTerm C W x)).Finite := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  exact (annularPrimeIdeals C a b x).finite_toSet.subset
    (primeWeightTerm_support_subset C W ha hab.le hsupp hx)

theorem weightedPrimeSum_eq_annular (C : Set (Ideal O)) (W : ℝ → ℝ)
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    weightedPrimeSum C W x = weightedPrimeAnnularSum C W a b x := by
  rw [weightedPrimeSum, finsum_eq_finsetSum_of_support_subset _
    (primeWeightTerm_support_subset C W ha hab hsupp hx)]
  apply Finset.sum_congr rfl
  intro P hP
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  simp only [primeWeightTerm, h.1, h.2.1, and_self, ite_true]

theorem weightedPrimeSum_tendsto (C : Set (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSum C W x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  apply (weightedPrimeAnnularSum_tendsto C hmass W hW ha hab.le hsupp).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [weightedPrimeSum_eq_annular C W ha hab.le hsupp hx]

def weightedPrimeSumDeleted (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ᶠ P : Ideal O, if P ∈ S then 0 else primeWeightTerm C W x P

theorem finite_prime_weights_eventually_zero (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    ∀ᶠ x : ℝ in atTop, ∀ P ∈ S, primeWeightTerm C W x P = 0 := by
  have hz : ∀ᶠ y in 𝓝 (0 : ℝ), W y = 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h => (show (0 : ℝ) < 0 from hp h).false)
  rw [eventually_all_finset]
  intro P hP
  have ht : Tendsto (fun x : ℝ => (Ideal.absNorm P : ℝ) / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul (Ideal.absNorm P : ℝ)
  filter_upwards [ht hz] with x hx
  change W (Ideal.absNorm P / x) = 0 at hx
  simp only [primeWeightTerm, hx, zero_mul, ite_self]

theorem fixed_prime_deletion_eventually_eq (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    weightedPrimeSumDeleted C S W =ᶠ[atTop] weightedPrimeSum C W := by
  filter_upwards [finite_prime_weights_eventually_zero C S W hp] with x hx
  unfold weightedPrimeSumDeleted weightedPrimeSum
  congr 1
  ext P
  by_cases hP : P ∈ S
  · simp only [hP, ite_true, hx P hP]
  · simp only [hP, ite_false]

theorem finite_prime_deleted_mass_eventually_zero (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    ∀ᶠ x : ℝ in atTop, (∑ P ∈ S, primeWeightTerm C W x P) = 0 := by
  filter_upwards [finite_prime_weights_eventually_zero C S W hp] with x hx
  exact Finset.sum_eq_zero hx

theorem weightedPrimeSumDeleted_tendsto (C : Set (Ideal O)) (S : Finset (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSumDeleted C S W x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  apply (weightedPrimeSum_tendsto C hmass W hW hc hp).congr'
  filter_upwards [fixed_prime_deletion_eventually_eq C S W hp] with x hx
  rw [hx]

theorem weightedPrimeSumDeleted_eq_annular (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    weightedPrimeSumDeleted C S W x =
      ∑ P ∈ annularPrimeIdeals C a b x \ S,
        W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ) := by
  have hsub : Function.support (fun P => if P ∈ S then 0 else primeWeightTerm C W x P) ⊆
      (↑(annularPrimeIdeals C a b x \ S) : Set (Ideal O)) := by
    intro P hP
    change (if P ∈ S then 0 else primeWeightTerm C W x P) ≠ 0 at hP
    by_cases hPS : P ∈ S
    · simp only [hPS, ite_true, ne_self_iff_false] at hP
    · simp only [hPS, ite_false] at hP
      exact Finset.mem_sdiff.mpr ⟨primeWeightTerm_support_subset C W ha hab hsupp hx hP, hPS⟩
  rw [weightedPrimeSumDeleted, finsum_eq_finsetSum_of_support_subset _ hsub]
  apply Finset.sum_congr rfl
  intro P hP
  have hS := (Finset.mem_sdiff.mp hP).2
  have h := (mem_annularPrimeIdeals C a b x P).mp (Finset.mem_sdiff.mp hP).1
  simp only [hS, ite_false, primeWeightTerm, h.1, h.2.1, and_self, ite_true]

theorem powerWeight_integral_pos (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    0 < ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ) := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  have hφ := contDiff_powerWeight W hW ha hsupp (-5 / 6)
  obtain ⟨y, hy⟩ : ∃ y : ℝ, W y ≠ 0 := by
    by_contra h
    push Not at h
    exact hWne (funext h)
  have hy0 : 0 < y := hp (subset_closure hy)
  apply hφ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hc.mul_right
  · intro z
    by_cases hz : W z = 0
    · simp only [hz, zero_mul, Pi.zero_apply, le_refl]
    · have hz0 : 0 < z := hp (subset_closure hz)
      exact mul_nonneg (hW0 z) (Real.rpow_nonneg hz0.le _)
  · exact mul_ne_zero hy (Real.rpow_pos_of_pos hy0 _).ne'

theorem weightedPrimeSumDeleted_eventually_lower_bound (C : Set (Ideal O))
    (S : Finset (Ideal O)) {A : ℝ} (hA : 0 < A)
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (1 / 6 : ℝ) / Real.log x ≤ weightedPrimeSumDeleted C S W x := by
  let L : ℝ := A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ)
  have hL : 0 < L := mul_pos hA (powerWeight_integral_pos W hW hc hp hW0 hWne)
  refine ⟨L / 2, half_pos hL, ?_⟩
  have ht := weightedPrimeSumDeleted_tendsto C S hmass W hW hc hp
  have he := ht (Ioi_mem_nhds (half_lt_self hL))
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  change L / 2 < Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSumDeleted C S W x at hx
  have hxp : 0 < x ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _
  apply (div_le_iff₀ (Real.log_pos hx1)).mpr
  have hmul := (le_div_iff₀ hxp).mp (show L / 2 ≤
      (Real.log x * weightedPrimeSumDeleted C S W x) / x ^ (1 / 6 : ℝ) by
    convert hx.le using 1; ring)
  nlinarith

theorem weightedPrimeSumDeleted_eventually_pos (C : Set (Ideal O))
    (S : Finset (Ideal O)) {A : ℝ} (hA : 0 < A)
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∀ᶠ x : ℝ in atTop, 0 < weightedPrimeSumDeleted C S W x := by
  obtain ⟨c, hc0, he⟩ := weightedPrimeSumDeleted_eventually_lower_bound C S hA hmass
    W hW hc hp hW0 hWne
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  exact (div_pos (mul_pos hc0 (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _))
    (Real.log_pos hx1)).trans_le hx

theorem weightedPrimeSum_nat_tendsto (C : Set (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 6 : ℝ) * weightedPrimeSum C W N)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) :=
  (weightedPrimeSum_tendsto C hmass W hW hc hp).comp tendsto_natCast_atTop_atTop

end

end SevenEighths.PNT.AnnularPrimeMass

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeCounting.RayAsymptotic -/

section

namespace OAI

namespace SevenEighths.PNT.RayAsymptotic

open ActualEisensteinCubic RayOrthogonality Filter
open scoped BigOperators Classical Topology

noncomputable section

variable (M : Ideal O) [Finite (O ⧸ M)]

def classCoeff (n : ℕ) : ℝ := IdealMangoldt.classCoeff (principalIdeals M) n

theorem sum_coeff (n : ℕ) :
    (∑ χ : rayCharacters M, IdealLogDerivative.coeff (idealCharacter M χ) n) =
      (rayCard M : ℂ) * (classCoeff M n : ℂ) := by
  unfold IdealLogDerivative.coeff ShortDraftHeckeBridge.normFiberCoeff
  rw [Finset.sum_comm]
  unfold classCoeff IdealMangoldt.classCoeff IdealMangoldt.coeff IdealMangoldt.normFiber
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [← Finset.mul_sum, sum_idealCharacters]
  by_cases hI : I ∈ principalIdeals M
  · simp only [hI, ite_true, one_mul, mul_comm]
  · simp only [hI, ite_false, zero_mul, Complex.ofReal_zero, mul_zero]

theorem average_coeff (n : ℕ) :
    (classCoeff M n : ℂ) =
      (∑ χ : rayCharacters M, IdealLogDerivative.coeff (idealCharacter M χ) n) /
        (rayCard M : ℂ) := by
  rw [sum_coeff]
  have hc : (rayCard M : ℂ) ≠ 0 := by exact_mod_cast (rayCard_pos M).ne'
  exact (mul_div_cancel_left₀ _ hc).symm

theorem classCoeff_LSeries (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (classCoeff M n : ℂ)) s =
      (∑ χ : rayCharacters M, LSeries (IdealLogDerivative.coeff (idealCharacter M χ)) s) /
        (rayCard M : ℂ) := by
  have heq : (fun n => (classCoeff M n : ℂ)) =
      (rayCard M : ℂ)⁻¹ • ∑ χ : rayCharacters M, IdealLogDerivative.coeff (idealCharacter M χ) := by
    funext n
    rw [average_coeff]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, LSeries_smul, LSeries_sum]
  · rw [div_eq_mul_inv, mul_comm]
  · intro χ _
    exact IdealLogDerivative.coeff_summable _ (norm_idealCharacter_le_one M χ) s hs

def principalRegularization (F : ℂ → ℂ) (residue : ℂ) : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * F s) 1 residue

omit [Finite (O ⧸ M)] in
theorem principalRegularization_eventuallyEq (F : ℂ → ℂ) (residue : ℂ)
    {s : ℂ} (hs : s ≠ 1) :
    principalRegularization F residue =ᶠ[𝓝 s] (fun z => (z - 1) * F z) := by
  refine eventuallyEq_iff_exists_mem.mpr ?_
  exact ⟨_, isOpen_ne.mem_nhds hs, fun z hz => Function.update_of_ne (Set.mem_ofPred.mp hz) ..⟩

omit [Finite (O ⧸ M)] in
theorem principalRegularization_analyticAt (F : ℂ → ℂ) (residue : ℂ)
    {s : ℂ} (hs : s ≠ 1) (hF : AnalyticAt ℂ F s) :
    AnalyticAt ℂ (principalRegularization F residue) s :=
  ((analyticAt_id.sub analyticAt_const).mul hF).congr
    (principalRegularization_eventuallyEq F residue hs).symm

omit [Finite (O ⧸ M)] in

theorem principalRegularization_analyticAt_of_local (F R : ℂ → ℂ)
    (hR : AnalyticAt ℂ R 1)
    (hFR : ∀ᶠ s in 𝓝 (1 : ℂ), s ≠ 1 → (s - 1) * F s = R s) :
    AnalyticAt ℂ (principalRegularization F (R 1)) 1 := by
  apply hR.congr
  filter_upwards [hFR] with s hs
  by_cases hs1 : s = 1
  · subst s
    simp only [principalRegularization, Function.update_self]
  · rw [principalRegularization, Function.update_of_ne hs1]
    exact (hs hs1).symm

omit [Finite (O ⧸ M)] in
theorem principalRegularization_logDeriv (F : ℂ → ℂ) (residue : ℂ)
    {s : ℂ} (hs : s ≠ 1) (hF : AnalyticAt ℂ F s) (hF0 : F s ≠ 0) :
    -deriv (principalRegularization F residue) s / principalRegularization F residue s =
      -deriv F s / F s - 1 / (s - 1) := by
  have hd := (principalRegularization_eventuallyEq F residue hs).deriv_eq
  rw [hd, principalRegularization, Function.update_of_ne hs,
    deriv_fun_mul (by fun_prop) hF.differentiableAt, deriv_sub_const, deriv_id'', one_mul]
  field_simp
  ring

def regularizedFamily (F : rayCharacters M → ℂ → ℂ) (residue : ℂ)
    (χ : rayCharacters M) : ℂ → ℂ :=
  if χ = 1 then principalRegularization (F χ) residue else F χ

def remainder (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) (s : ℂ) : ℂ :=
  (∑ χ : rayCharacters M,
    -deriv (regularizedFamily M F residue χ) s / regularizedFamily M F residue χ s) /
      (rayCard M : ℂ)

structure AnalyticFamily (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) : Prop where
  eq_series : ∀ (χ : rayCharacters M) (s : ℂ), 1 < s.re →
    F χ s = IdealEuler.series (idealCharacter M χ) s
  analytic : ∀ (χ : rayCharacters M) (s : ℂ), 1 ≤ s.re →
    χ ≠ 1 ∨ s ≠ 1 → AnalyticAt ℂ (F χ) s
  nonzero : ∀ (χ : rayCharacters M) (s : ℂ), 1 ≤ s.re →
    χ ≠ 1 ∨ s ≠ 1 → F χ s ≠ 0
  pole_analytic : AnalyticAt ℂ (principalRegularization (F 1) residue) 1
  residue_ne_zero : residue ≠ 0

theorem regularizedFamily_analyticAt {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) (χ : rayCharacters M) (s : ℂ) (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (regularizedFamily M F residue χ) s := by
  by_cases hχ : χ = 1
  · subst χ
    rw [regularizedFamily, ite_eq_left rfl]
    by_cases hs1 : s = 1
    · subst s
      exact hF.pole_analytic
    · exact principalRegularization_analyticAt _ _ hs1 (hF.analytic 1 s hs (Or.inr hs1))
  · rw [regularizedFamily, ite_eq_right hχ]
    exact hF.analytic χ s hs (Or.inl hχ)

theorem regularizedFamily_ne_zero {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) (χ : rayCharacters M) (s : ℂ) (hs : 1 ≤ s.re) :
    regularizedFamily M F residue χ s ≠ 0 := by
  by_cases hχ : χ = 1
  · subst χ
    rw [regularizedFamily, ite_eq_left rfl]
    by_cases hs1 : s = 1
    · subst s
      simpa only [principalRegularization, Function.update_self] using hF.residue_ne_zero
    · rw [principalRegularization, Function.update_of_ne hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) (hF.nonzero 1 s hs (Or.inr hs1))
  · rw [regularizedFamily, ite_eq_right hχ]
    exact hF.nonzero χ s hs (Or.inl hχ)

theorem remainder_continuousOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    ContinuousOn (remainder M F residue) {s : ℂ | 1 ≤ s.re} := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div_const
  apply tendsto_finsetSum
  intro χ _
  have h := regularizedFamily_analyticAt M hF χ s hs
  exact h.deriv.continuousAt.neg.div h.continuousAt (regularizedFamily_ne_zero M hF χ s hs)

theorem regularizedFamily_logDeriv {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) (χ : rayCharacters M) (s : ℂ) (hs : 1 < s.re) :
    -deriv (regularizedFamily M F residue χ) s / regularizedFamily M F residue χ s =
      -deriv (F χ) s / F χ s - (if χ = 1 then 1 / (s - 1) else 0) := by
  by_cases hχ : χ = 1
  · rw [regularizedFamily, ite_eq_left hχ, ite_eq_left hχ]
    have hs1 : s ≠ 1 := by intro heq; simp only [heq, Complex.one_re] at hs; linarith
    exact principalRegularization_logDeriv _ _ hs1
      (hF.analytic χ s hs.le (Or.inr hs1)) (hF.nonzero χ s hs.le (Or.inr hs1))
  · simp only [regularizedFamily, hχ, ite_false, sub_zero]

theorem remainder_eqOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Set.EqOn (remainder M F residue)
      (fun s => LSeries (fun n => (classCoeff M n : ℂ)) s -
        (rayCard M : ℂ)⁻¹ / (s - 1)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change remainder M F residue s = LSeries (fun n => (classCoeff M n : ℂ)) s -
    (rayCard M : ℂ)⁻¹ / (s - 1)
  rw [remainder, classCoeff_LSeries M s hs]
  simp_rw [regularizedFamily_logDeriv M hF _ s hs]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ χ : rayCharacters M, if χ = 1 then 1 / (s - 1) else (0 : ℂ)) =
      1 / (s - 1) := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum]
  have hlog (χ : rayCharacters M) : -deriv (F χ) s / F χ s =
      LSeries (IdealLogDerivative.coeff (idealCharacter M χ)) s :=
    (IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _
      (norm_idealCharacter_le_one M χ) (F χ) (hF.eq_series χ) s hs).symm
  simp_rw [hlog]
  ring

theorem classCoeff_ratio_tendsto {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Tendsto (fun N : ℕ => cumsum (classCoeff M) N / N)
      atTop (𝓝 ((rayCard M : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (IdealMangoldt.classCoeff_nonneg (principalIdeals M))
    (fun σ hσ => IdealMangoldt.classCoeff_summable_nterm (principalIdeals M) hσ)
    (IdealMangoldt.classCoeff_chebyshev (principalIdeals M))
    (remainder_continuousOn M hF)
  simpa only [classCoeff, Complex.ofReal_inv, Complex.ofReal_natCast] using remainder_eqOn M hF

section Quotient

variable (H : Subgroup (O ⧸ M)ˣ) (hH : globalUnits M ≤ H)

def quotientClassCoeff (n : ℕ) : ℝ := IdealMangoldt.classCoeff (RayQuotient.identityClass M H) n

theorem quotient_sum_coeff (n : ℕ) :
    (∑ χ : RayQuotient.Characters M H,
      IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ) n) =
      (RayQuotient.classNumber M H : ℂ) * (quotientClassCoeff M H n : ℂ) := by
  unfold IdealLogDerivative.coeff ShortDraftHeckeBridge.normFiberCoeff
  rw [Finset.sum_comm]
  unfold quotientClassCoeff IdealMangoldt.classCoeff IdealMangoldt.coeff IdealMangoldt.normFiber
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [← Finset.mul_sum, RayQuotient.sum_idealCharacters]
  by_cases hI : I ∈ RayQuotient.identityClass M H
  · simp only [hI, ite_true, one_mul, mul_comm]
  · simp only [hI, ite_false, zero_mul, Complex.ofReal_zero, mul_zero]

theorem quotient_average_coeff (n : ℕ) :
    (quotientClassCoeff M H n : ℂ) =
      (∑ χ : RayQuotient.Characters M H,
        IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ) n) /
          (RayQuotient.classNumber M H : ℂ) := by
  rw [quotient_sum_coeff]
  have hc : (RayQuotient.classNumber M H : ℂ) ≠ 0 := by
    exact_mod_cast (RayQuotient.classNumber_pos M H).ne'
  exact (mul_div_cancel_left₀ _ hc).symm

theorem quotientClassCoeff_LSeries (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (quotientClassCoeff M H n : ℂ)) s =
      (∑ χ : RayQuotient.Characters M H,
        LSeries (IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ)) s) /
          (RayQuotient.classNumber M H : ℂ) := by
  have heq : (fun n => (quotientClassCoeff M H n : ℂ)) =
      (RayQuotient.classNumber M H : ℂ)⁻¹ • ∑ χ : RayQuotient.Characters M H,
        IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ) := by
    funext n
    rw [quotient_average_coeff M H hH]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, LSeries_smul, LSeries_sum]
  · rw [div_eq_mul_inv, mul_comm]
  · intro χ _
    exact IdealLogDerivative.coeff_summable _ (RayQuotient.norm_idealCharacter_le_one M H hH χ) s hs

def quotientRemainder (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) (s : ℂ) : ℂ :=
  (∑ χ : RayQuotient.Characters M H,
    -deriv (regularizedFamily M F residue (RayQuotient.toFullRay M H hH χ)) s /
      regularizedFamily M F residue (RayQuotient.toFullRay M H hH χ) s) /
        (RayQuotient.classNumber M H : ℂ)

theorem quotientRemainder_continuousOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    ContinuousOn (quotientRemainder M H hH F residue) {s : ℂ | 1 ≤ s.re} := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div_const
  apply tendsto_finsetSum
  intro χ _
  have h := regularizedFamily_analyticAt M hF (RayQuotient.toFullRay M H hH χ) s hs
  exact h.deriv.continuousAt.neg.div h.continuousAt
    (regularizedFamily_ne_zero M hF (RayQuotient.toFullRay M H hH χ) s hs)

theorem quotientRemainder_eqOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Set.EqOn (quotientRemainder M H hH F residue)
      (fun s => LSeries (fun n => (quotientClassCoeff M H n : ℂ)) s -
        (RayQuotient.classNumber M H : ℂ)⁻¹ / (s - 1)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change quotientRemainder M H hH F residue s =
    LSeries (fun n => (quotientClassCoeff M H n : ℂ)) s -
      (RayQuotient.classNumber M H : ℂ)⁻¹ / (s - 1)
  rw [quotientRemainder, quotientClassCoeff_LSeries M H hH s hs]
  simp_rw [regularizedFamily_logDeriv M hF _ s hs, RayQuotient.toFullRay_eq_one]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ χ : RayQuotient.Characters M H, if χ = 1 then 1 / (s - 1) else (0 : ℂ)) =
      1 / (s - 1) := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum]
  have hlog (χ : RayQuotient.Characters M H) :
      -deriv (F (RayQuotient.toFullRay M H hH χ)) s / F (RayQuotient.toFullRay M H hH χ) s =
        LSeries (IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ)) s := by
    rw [RayQuotient.idealCharacter_eq_fullRay]
    exact (IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _
      (norm_idealCharacter_le_one M _) (F _) (hF.eq_series _) s hs).symm
  simp_rw [hlog]
  ring

include hH in

theorem quotientClassCoeff_ratio_tendsto {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Tendsto (fun N : ℕ => cumsum (quotientClassCoeff M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (IdealMangoldt.classCoeff_nonneg (RayQuotient.identityClass M H))
    (fun σ hσ => IdealMangoldt.classCoeff_summable_nterm (RayQuotient.identityClass M H) hσ)
    (IdealMangoldt.classCoeff_chebyshev (RayQuotient.identityClass M H))
    (quotientRemainder_continuousOn M H hH hF)
  simpa only [quotientClassCoeff, Complex.ofReal_inv, Complex.ofReal_natCast]
    using quotientRemainder_eqOn M H hH hF

end Quotient

end
end SevenEighths.PNT.RayAsymptotic

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.RayPrimes -/

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeRayPrimes
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem analytic_family : PNT.RayAsymptotic.AnalyticFamily M
    (fun χ => LFunction (HeckeRayFamily.character M χ))
    (HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1) 1) := by
  refine ⟨?_, ?_, ?_, ?_, HeckeRayFamily.principal_pole_ne_zero M⟩
  · intro χ s hs
    exact LFunction_eq_series _ hs
  · intro χ s hs hpole
    rcases hpole with hχ | hs1
    · exact (HeckeRayFamily.character_entire M χ hχ).analyticAt s
    · apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
      filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1] with z hz0 hz1
      exact LFunction_differentiableAt _ hz0 (Or.inl hz1)
  · intro χ s hs hpole
    exact HeckeRayFamily.character_boundary_ne_zero M χ hs hpole.symm
  · apply PNT.RayAsymptotic.principalRegularization_analyticAt_of_local
      _ (HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1))
      ((HeckeOrigin.poleRemoved_entire _).analyticAt 1)
    filter_upwards [isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0)] with s hs0
    intro hs1
    exact (HeckeOrigin.poleRemoved_eq _ hs0 hs1).symm

theorem classCoeff_ratio_tendsto :
    Tendsto (fun N : ℕ => cumsum (PNT.RayAsymptotic.classCoeff M) N / N)
      atTop (𝓝 ((RayOrthogonality.rayCard M : ℝ)⁻¹)) :=
  PNT.RayAsymptotic.classCoeff_ratio_tendsto M (analytic_family M)

theorem quotientClassCoeff_ratio_tendsto
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H) :
    Tendsto (fun N : ℕ => cumsum (PNT.RayAsymptotic.quotientClassCoeff M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) :=
  PNT.RayAsymptotic.quotientClassCoeff_ratio_tendsto M H hH (analytic_family M)

theorem primeLogMass_ratio_tendsto :
    Tendsto (fun N : ℕ => PNT.IdealPrimeMass.primeLogMass (RayOrthogonality.principalIdeals M) N / N)
      atTop (𝓝 ((RayOrthogonality.rayCard M : ℝ)⁻¹)) :=
  PNT.IdealPrimeMass.primeLogMass_ratio_tendsto _ (classCoeff_ratio_tendsto M)

theorem quotientPrimeLogMass_ratio_tendsto
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H) :
    Tendsto (fun N : ℕ => PNT.IdealPrimeMass.primeLogMass (RayQuotient.identityClass M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) :=
  PNT.IdealPrimeMass.primeLogMass_ratio_tendsto _ (quotientClassCoeff_ratio_tendsto M H hH)

end SevenEighths.HeckeRayPrimes

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.Character -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve ProbePhysical
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def rowMaskElement : O := 2*λ₀

theorem rowMaskElement_ne_zero : rowMaskElement≠0 :=
  mul_ne_zero (by norm_num) PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero

def rawRow (u : FreeRow) : Character := Classical.choose
  (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
    rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))

theorem rawRow_coeff (u : FreeRow) (I : Ideal O) :
    idealCoeff (rawRow u) I=idealCoeff (fixedSourcePrincipal ∅ (by simp)) I*
      idealRowHom (rowMaskElement^6*u.val) I := by
  have he := (Classical.choose_spec
    (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
      rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2
  simpa only [one_pow,mul_one] using idealCoeff_eq_row _ (rawRow u) rowMaskElement 1 u.val he I

theorem outside_good_coprime (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (P : ProbePhysical.PrimeIdeal) (hP : P.val∉S) :
    λ₀∉P.val ∧ IsCoprime P.val (Ideal.span {rowMaskElement}) := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have hn : P.val∉fixedBadPrimes := fun hh => hP (hbad hh)
  have hg := (prime_good_iff_not_bad P.val).mpr hn
  refine ⟨hg.1,?_⟩
  have hc := (prime_coprime_fixedProduct S hS P).mpr hP
  rw [IsCoprime.prod_right_iff] at hc
  have hLam : Ideal.span {λ₀}∈S := hbad (Finset.mem_insert_self _ _)
  have h2 : Ideal.span {(2 : O)}∈S := hbad (by simp [fixedBadPrimes])
  unfold rowMaskElement
  rw [←Ideal.span_singleton_mul_span_singleton]
  exact (hc _ h2).mul_right (hc _ hLam)

theorem rawRow_prime_outside (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) (hP : P.val∉S) :
    idealCoeff (rawRow u) P.val=idealRowHom u.val P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  obtain ⟨hg,hc⟩ := outside_good_coprime S hS hbad P hP
  rw [rawRow_coeff,fixedSourcePrincipal_prime]
  rw [ite_eq_right (by simp),one_mul]
  rw [idealRowHom_argument_mul,idealRowHom_prime_sixth_mask rowMaskElement P.val hg,
    ite_eq_left hc,one_mul]

def rowCharacter (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) : Character :=
  (rawRow u).excludePrimes S hS

def sourceRowCoeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) : Ideal O→*₀ℂ where
  toFun I := highExclusion S hS I*idealRowHom u.val I
  map_zero' := by rw [(idealRowHom u.val).map_zero, mul_zero]
  map_one' := by rw [map_one,map_one,mul_one]
  map_mul' I J := by simp only [map_mul]; ring

theorem hom_eq_of_primes (f g : Ideal O→*₀ℂ) (h : ∀P : ProbePhysical.PrimeIdeal,f P.val=g P.val) : f=g := by
  ext I
  by_cases hI : I=0
  · subst I; rw [map_zero,map_zero]
  have hf := congrArg (fun F : Ideal O→*₀ℂ => F I) (IdealEuler.primeValueHom_eq f)
  have hg := congrArg (fun F : Ideal O→*₀ℂ => F I) (IdealEuler.primeValueHom_eq g)
  rw [←hf,←hg]
  change (if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map f).prod)=
    (if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map g).prod)
  rw [ite_eq_right hI,ite_eq_right hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  exact h ⟨P,UniqueFactorizationMonoid.prime_of_normalized_factor P hP⟩

theorem rowCharacter_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    idealCoeff (rowCharacter S hS u) I=highExclusion S hS I*idealRowHom u.val I := by
  have he : idealCoeff (rowCharacter S hS u)=sourceRowCoeff S hS u := by
    apply hom_eq_of_primes
    intro P
    change idealCoeff ((rawRow u).excludePrimes S hS) P.val=
      highExclusion S hS P.val*idealRowHom u.val P.val
    rw [excludedTarget_prime,highExclusion_prime]
    by_cases hP : P.val∈S
    · simp only [ite_eq_left hP,zero_mul]
    · simp only [ite_eq_right hP,one_mul]
      exact rawRow_prime_outside S hS hbad u P hP
  exact congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem target_inverseRow_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) :
    idealCoeff ((η.product (rawRow u).inverse).excludePrimes S hS) P.val=
      if P.val∈S then 0 else idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val) := by
  rw [excludedTarget_prime,idealCoeff_product,idealCoeff_inverse_conj]
  by_cases hP : P.val∈S
  · simp only [ite_eq_left hP]
  · rw [ite_eq_right hP,ite_eq_right hP,rawRow_prime_outside S hS hbad u P hP]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.Euler -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def targetRow (η : Character) (u : FreeRow) : Character := η.product (rawRow u).inverse

theorem rowCharacter_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : ProbePhysical.PrimeIdeal // P.val∉S} =>
      (1-idealRowHom u.val P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction (rowCharacter S hS u) s) := by
  apply LFunction_hasProd_outside (rowCharacter S hS u) S (idealRowHom u.val) _ s hs
  intro P
  rw [rowCharacter_coeff S hS hbad,highExclusion_prime]
  split_ifs <;> simp only [zero_mul,one_mul]

theorem targetRow_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : ProbePhysical.PrimeIdeal // P.val∉S} =>
      (1-idealCoeff η P.val.val*starRingEnd ℂ (idealRowHom u.val P.val.val)*
        CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction ((targetRow η u).excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S (fun P => idealCoeff η P*starRingEnd ℂ (idealRowHom u.val P))
    (target_inverseRow_coeff S hS hbad η u) s hs

def localCorrection (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowHighLocalFactor η u.val P.val x w z *
    (1-CubicEisenstein.fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*CubicEisenstein.fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*CubicEisenstein.fullIdealWeight x P.val)

def globalCorrection (S : Finset (Ideal O)) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : ProbePhysical.PrimeIdeal // P.val∉S},localCorrection η u P.val x w z

theorem localCorrection_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : ProbePhysical.PrimeIdeal // P.val∉S} =>localCorrection η u P.val x w z)
      (markedIdealHighSeries S 1 η u.val x w z *
        (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹ * (LFunction (rowCharacter S hS u) w)⁻¹ *
          LFunction ((targetRow η u).excludePrimes S hS) x) := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re]; linarith
  have hF := excludedIdealHighSeries_row_hasProd_outside S hS η u.val x w z hx hw hz
  have hZ := (fixedSourcePrincipal_hasProd S hS (6*z) hz1).inv₀
    (LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1)
  have hW := (rowCharacter_hasProd S hS hbad u w hw1).inv₀
    (LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1)
  have hD := targetRow_hasProd S hS hbad η u x hx1
  have he := ((hF.mul hZ).mul hW).mul hD
  simpa only [localCorrection,inv_inv,div_eq_mul_inv] using he

theorem globalCorrection_multipliable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Multipliable (fun P : {P : ProbePhysical.PrimeIdeal // P.val∉S} =>localCorrection η u P.val x w z) :=
  (localCorrection_hasProd S hS hbad η u x w z hx hw hz).multipliable

theorem high_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η u.val x w z=
      LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (rowCharacter S hS u) w /
        LFunction ((targetRow η u).excludePrimes S hS) x * globalCorrection S η u x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re]; linarith
  have hZ := LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := LFunction_ne_zero_of_one_lt_re ((targetRow η u).excludePrimes S hS) hx1
  rw [globalCorrection,(localCorrection_hasProd S hS hbad η u x w z hx hw hz).tprod_eq]
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.Conductor -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure ProbePhysical
local notation "O" => HeckeFamily.O

def conductorConstant : ℕ :=
  (Ideal.span {rowMaskElement}:Ideal O).absNorm*(Ideal.span {(72 : O)}:Ideal O).absNorm

theorem rawRow_conductor (u : FreeRow) :
    (rawRow u).modulus.absNorm≤ conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm := by
  have hb := (Classical.choose_spec
    (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
      rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).1
  change (rawRow u).modulus.absNorm≤_ at hb
  simpa [rowConductorBound,conductorConstant,fixedSourcePrincipal,HeckeRayFamily.character,
    Character.ofResidue] using hb

theorem rowCharacter_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) :
    (rowCharacter S hS u).modulus.absNorm≤
      conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm*(∏P∈S,P).absNorm := by
  change ((rawRow u).modulus*(∏P∈S,P)).absNorm≤_
  rw [map_mul]
  exact Nat.mul_le_mul_right _ (rawRow_conductor u)

theorem targetRow_conductor (η : Character) (u : FreeRow) :
    (targetRow η u).modulus.absNorm≤η.modulus.absNorm*conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Finite (O ⧸ (rawRow u).modulus) := Ring.HasFiniteQuotients.finiteQuotient (rawRow u).modulus_ne_bot
  change (η.modulus⊓(rawRow u).modulus).absNorm≤_
  calc
    _ ≤ η.modulus.absNorm*(rawRow u).modulus.absNorm :=
      FiniteConductor.absNorm_inf_le_mul _ _
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left η.modulus.absNorm (rawRow_conductor u)

theorem targetRow_excluded_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) :
    ((targetRow η u).excludePrimes S hS).modulus.absNorm≤
      η.modulus.absNorm*conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm*(∏P∈S,P).absNorm := by
  change ((targetRow η u).modulus*(∏P∈S,P)).absNorm≤_
  rw [map_mul]
  exact Nat.mul_le_mul_right _ (targetRow_conductor η u)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RowRadicalConductor -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeRowRadicalConductor
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem canonicalPrimePower_descent (P : Ideal O) [P.IsMaximal]
    (hg : λ₀ ∉ P) {c : ℕ} (hc : 1 ≤ c) (x : O ⧸ P ^ c) :
    CenteredMomentCanonical.canonicalPrimePowerCharacter P hg hc x =
      (CompletedGauss.actualSextic P hg ^ c)
        (CenteredMomentCorrelation.primePowerReduction P hc x) := rfl

theorem idealRowHom_congr_radical (I : Ideal O) (x y : O)
    (hxy : x-y ∈ I.radical) : idealRowHom x I = idealRowHom y I := by
  by_cases hI : I = 0
  · subst I
    simp only [map_zero]
  change (if I=0 then 0 else _) = (if I=0 then 0 else _)
  rw [ite_eq_right hI, ite_eq_right hI]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  have hp := Ideal.isPrime_of_prime (prime_of_normalized_factor P hP)
  have hle : I.radical ≤ P := hp.radical_le_iff.mpr
    (((Ideal.mem_normalizedFactors_iff hI).mp hP).2)
  unfold localRowValue
  split_ifs with hg
  · let : P.IsMaximal := hg.1
    congr 1
    exact Ideal.Quotient.eq.mpr (hle hxy)
  · rfl

theorem radical_ne_bot (I : Ideal O) (hI : I ≠ ⊥) : I.radical ≠ ⊥ := by
  intro h
  exact hI (bot_unique (h ▸ I.le_radical))

theorem movingNumeratorRow_radical_periodic (r : O)
    (hr : Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {r}).radical
      (movingNumeratorRow r hr) := idealRowHom_congr_radical _

theorem actualPeriodicRow_radical_periodic (Ψ : O →* ℂ) (Q : Ideal O)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (m : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo
      (Q * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical)
      (actualPeriodicRow Ψ m u a b r hr) := by
  intro x y hxy
  have hQ : x-y ∈ Q := Ideal.mul_le_left (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hm : x-y ∈ Ideal.span {m} := Ideal.mul_le_right (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have h72 : x-y ∈ Ideal.span {(72 : O)} := Ideal.mul_le_right (Ideal.mul_le_left hxy)
  have hrxy : x-y ∈ (Ideal.span {r}).radical := Ideal.mul_le_right hxy
  change ((Ψ x * coprimalityMask m x) * numeratorBadTwist u a b r hr x) *
      movingNumeratorRow r hr x =
    ((Ψ y * coprimalityMask m y) * numeratorBadTwist u a b r hr y) *
      movingNumeratorRow r hr y
  rw [hΨ x y hQ, coprimalityMask_periodic m x y hm,
    numeratorBadTwist_periodic u a b r hr x y h72,
    movingNumeratorRow_radical_periodic r hr x y hrxy]

theorem rowTwist_radical_periodic (η : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r-1) (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r) :
    CanonicalCoefficientClass.FactorsModulo
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical)
      (rowTwist (elementHom η) m f z) := by
  refine periodic_of_primary _ ?_ _ (actualPeriodicRow (elementHom η) m u a b r hr)
    (actualPeriodicRow_radical_periodic _ _ (elementHom_periodic η) _ _ _ _ _ hr)
    (rowTwist_unit_mul η m f z) ?_ ?_
  · have hd3 : λ₀ ^ 2 ∣ (3 : O) := ActualEisensteinCubic.lambda_sq_dvd_three
    have hd72 : λ₀ ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hd72))
  · intro n hn
    apply rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2
    intro hs
    exact ((supported_span_iff n).mp hs).1 hn
  · exact rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx

theorem rowTwist_nonzero_radical_unit (η : Character) (m f z n : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r)
    (hn : rowTwist (elementHom η) m f z n ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical) n) := by
  have hu := rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx hn
  have hle : η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r} ≤
      η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical :=
    Ideal.mul_mono_right (Ideal.span {r}).le_radical
  exact hu.map (Ideal.Quotient.factor hle)

theorem exists_row_character_radical (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character,
      χ.modulus.absNorm ≤ η.modulus.absNorm * (Ideal.span {m}).absNorm *
        (Ideal.span {(72 : O)}).absNorm * (Ideal.span {f^4*z}).radical.absNorm ∧
      ∀ n : O, elementCoeff χ n = rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, _, _, _, _⟩ :=
    exists_actual_periodic_row (elementHom η) η.modulus η.modulus_ne_bot
      (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  change f^4*z = (u : O)*λ₀^a*(2 : O)^b*r at hx
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * (Ideal.span {r}).radical
  have hM : M ≠ ⊥ := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot
      (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    (radical_ne_bot _ hr.1)
  have hG := rowTwist_radical_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨HeckeRowClosure.rowCharacter M hM _ hG (rowTwist_unit η m f z), ?_, ?_⟩
  · change M.absNorm ≤ _
    have hfr : Ideal.span {f^4*z} ≤ (Ideal.span {r} : Ideal O) := by
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact Ideal.mem_span_singleton.mpr ⟨(u : O)*λ₀^a*(2 : O)^b, by rw [hx]; ring⟩
    have hF : (Ideal.span {f^4*z} : Ideal O).radical ≠ ⊥ :=
      radical_ne_bot _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (pow_ne_zero _ hf) hz))
    let : Finite (O ⧸ (Ideal.span {f^4*z} : Ideal O).radical) :=
      Ring.HasFiniteQuotients.finiteQuotient hF
    have hn := FiniteConductor.absNorm_le_of_le (Ideal.radical_mono hfr)
    simpa only [M, map_mul] using Nat.mul_le_mul_left
      (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm) hn
  · intro n
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · exact Eq.symm (not_not.mp (fun h => hn
        (rowTwist_nonzero_radical_unit η m f z n hmLam hm2 u a b r hx h)))

theorem periodic_sup (G : O →* ℂ) (I J : Ideal O)
    (hI : CanonicalCoefficientClass.FactorsModulo I G)
    (hJ : CanonicalCoefficientClass.FactorsModulo J G) :
    CanonicalCoefficientClass.FactorsModulo (I ⊔ J) G := by
  intro x y hxy
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxy
  calc
    G x = G (x-a) := hI _ _ (by convert ha using 1; ring)
    _ = G y := hJ _ _ (by convert hb using 1; linear_combination -hab)

theorem primitive_of_equal_elements (χ θ : Character)
    (hel : ∀ n : O, elementCoeff χ n = elementCoeff θ n) :
    ∃ ψ : Character, χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ θ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  have hθ : CanonicalCoefficientClass.FactorsModulo θ.modulus (elementHom χ) := by
    intro x y hxy
    change elementCoeff χ x = elementCoeff χ y
    rw [hel x, hel y]
    exact elementHom_periodic θ x y hxy
  let M := χ.modulus ⊔ θ.modulus
  have hM : M ≠ ⊥ := fun h => χ.modulus_ne_bot (bot_unique (h ▸ le_sup_left))
  have hG := periodic_sup (elementHom χ) χ.modulus θ.modulus (elementHom_periodic χ) hθ
  have hu : ∀ u : Oˣ, elementHom χ (u : O) = 1 := fun u => χ.unit_trivial u
  let ρ := HeckeRowClosure.rowCharacter M hM (elementHom χ) hG hu
  have hr (n : O) : elementCoeff ρ n = elementCoeff χ n := by
    change elementCoeff (HeckeRowClosure.rowCharacter M hM _ hG hu) n = _
    rw [elementCoeff_rowCharacter]
    split_ifs with hn
    · rfl
    · have hz : elementCoeff χ n = 0 := by
        by_contra hne
        have hu : IsUnit (Ideal.Quotient.mk χ.modulus n) := MulChar.apply_ne_zero_iff.mp hne
        exact hn (hu.map (Ideal.Quotient.factor (show χ.modulus ≤ M from le_sup_left)))
      exact hz.symm
  obtain ⟨ψ, hψ, hp, hn, hmask⟩ := exists_primitive_character ρ
  refine ⟨ψ, le_sup_left.trans hψ, hp, ?_, ?_⟩
  · let : Finite (O ⧸ θ.modulus) := Ring.HasFiniteQuotients.finiteQuotient θ.modulus_ne_bot
    exact hn.trans (FiniteConductor.absNorm_le_of_le (show θ.modulus ≤ M from le_sup_right))
  · intro I
    by_cases hI : I = 0
    · subst I
      simp only [map_zero, ite_self]
    let n := ConcretePrimeRowBridge.idealGenerator I
    have hn0 : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
    have hs : Ideal.span {n} = I := ConcretePrimeRowBridge.span_idealGenerator I
    have hre : idealCoeff ρ I = idealCoeff χ I := by
      rw [← hs, idealCoeff_span _ hn0, idealCoeff_span _ hn0, hr]
    by_cases hc : IsCoprime I χ.modulus
    · have hu : IsUnit (Ideal.Quotient.mk χ.modulus n) :=
        (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr (hs.symm ▸ hc)
      have huM : IsUnit (Ideal.Quotient.mk M n) :=
        hu.map (Ideal.Quotient.factor (show χ.modulus ≤ M from le_sup_left))
      have hcM : IsCoprime I M := hs ▸ (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp huM
      simpa only [hre, show ρ.modulus = M from rfl, hcM, hc, ite_true] using hmask I
    · rw [ite_eq_right hc]
      simpa only [hc, ite_false] using idealCoeff_source_mask χ I

theorem rawRow_small_presentation (u : HeckeInverseAmplification.FreeRow) :
    ∃ θ : Character,
      θ.modulus.absNorm ≤ ProbeHighRowFamily.conductorConstant *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ n : O, elementCoeff (ProbeHighRowFamily.rawRow u) n = elementCoeff θ n := by
  obtain ⟨θ, hn, he⟩ := exists_row_character_radical
    (ProbePhysical.fixedSourcePrincipal ∅ (by simp)) ProbeHighRowFamily.rowMaskElement 1 u.val
    ProbeHighRowFamily.rowMaskElement_ne_zero one_ne_zero u.property.1
    (dvd_mul_left _ _) (dvd_mul_right _ _)
  refine ⟨θ, ?_, ?_⟩
  · simpa [ProbeHighRowFamily.conductorConstant, ProbePhysical.fixedSourcePrincipal,
      HeckeRayFamily.character, Character.ofResidue] using hn
  · intro n
    have ho := (Classical.choose_spec
      (exists_row_character_with_conductor (ProbePhysical.fixedSourcePrincipal ∅ (by simp))
        ProbeHighRowFamily.rowMaskElement 1 u.val ProbeHighRowFamily.rowMaskElement_ne_zero
        one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2 n
    exact ho.trans (he n).symm

theorem rawRow_primitive_radical (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rawRow u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ ProbeHighRowFamily.conductorConstant *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rawRow u) I =
        if IsCoprime I (ProbeHighRowFamily.rawRow u).modulus then idealCoeff ψ I else 0 := by
  obtain ⟨θ, hn, he⟩ := rawRow_small_presentation u
  obtain ⟨ψ, hle, hp, hb, hmask⟩ := primitive_of_equal_elements _ θ he
  exact ⟨ψ, hle, hp, hb.trans hn, hmask⟩

theorem equal_elements_excludePrimes (χ θ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff θ n)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (n : O) :
    elementCoeff (χ.excludePrimes S hS) n = elementCoeff (θ.excludePrimes S hS) n := by
  have hc : IsCoprime (Ideal.span {n}) χ.modulus ↔ IsCoprime (Ideal.span {n}) θ.modulus := by
    have huχ : elementCoeff χ n ≠ 0 ↔ IsCoprime (Ideal.span {n}) χ.modulus :=
      MulChar.apply_ne_zero_iff.trans (IdealCharacter.isUnit_mk_iff_isCoprime _ _)
    have huθ : elementCoeff θ n ≠ 0 ↔ IsCoprime (Ideal.span {n}) θ.modulus :=
      MulChar.apply_ne_zero_iff.trans (IdealCharacter.isUnit_mk_iff_isCoprime _ _)
    rw [he n] at huχ
    exact huχ.symm.trans huθ
  simp only [Character.excludePrimes, elementCoeff_refineModulus,
    IdealCharacter.isUnit_mk_iff_isCoprime, IsCoprime.mul_right_iff, hc, he n]

def fixedConductorConstant (S : Finset (Ideal O)) : ℕ :=
  ProbeHighRowFamily.conductorConstant * (∏ P ∈ S, P).absNorm

theorem rowCharacter_primitive_radical (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0 := by
  obtain ⟨θ, hn, he⟩ := rawRow_small_presentation u
  obtain ⟨ψ, hle, hp, hb, hmask⟩ := primitive_of_equal_elements
    (ProbeHighRowFamily.rowCharacter S hS u) (θ.excludePrimes S hS)
    (equal_elements_excludePrimes _ θ he S hS)
  refine ⟨ψ, hle, hp, hb.trans ?_, hmask⟩
  change (θ.modulus * ∏ P ∈ S, P).absNorm ≤ _
  rw [map_mul]
  simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm] using
    Nat.mul_le_mul_right ((∏ P ∈ S, P).absNorm) hn

theorem prod_le_radical_prod_pow {ι : Type*} (T : Finset ι)
    (P : ι → Ideal O) (e : ι → ℕ) (he : ∀ i ∈ T, 1 ≤ e i) :
    (∏ i ∈ T, P i) ≤ (∏ i ∈ T, P i ^ e i).radical := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hei : e i ≠ 0 := by have := he i (Finset.mem_insert_self i T); omega
    have hpow : (P i ^ e i).radical = (P i).radical := Ideal.radical_pow (P i) hei
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Ideal.radical_mul, hpow]
    exact Ideal.mul_le_inf.trans (inf_le_inf (P i).le_radical
      (ih (fun j hj => he j (Finset.mem_insert_of_mem hj))))

theorem radical_norm_selected_deficit {ι : Type*} [Fintype ι]
    (I : Ideal O) (hI : I ≠ 0) (P : ι → Ideal O)
    (hP : ∀ i, Prime (P i)) (hdis : Function.Injective P)
    (e : ι → ℕ) (he : ∀ i, 1 ≤ e i) (hdiv : ∀ i, P i ^ e i ∣ I) :
    I.radical.absNorm * ∏ i, (P i).absNorm ^ (e i - 1) ≤ I.absNorm := by
  let (i : ι) : (P i).IsMaximal := (Ideal.isPrime_of_prime (hP i)).isMaximal (hP i).ne_zero
  have hcop : Pairwise (fun i j => IsCoprime (P i ^ e i) (P j ^ e j)) := by
    intro i j hij
    exact (Ideal.isCoprime_of_isMaximal (hdis.ne hij)).pow
  obtain ⟨B, hB⟩ := Fintype.prod_dvd_of_coprime hcop hdiv
  have hB0 : B ≠ 0 := by
    intro hz
    apply hI
    rw [hB, hz, mul_zero]
  have hsmall0 : (∏ i, P i) * B ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => (hP i).ne_zero)) hB0
  have hsmall : (∏ i, P i) * B ≤ I.radical := by
    rw [hB, Ideal.radical_mul]
    exact Ideal.mul_le_inf.trans (inf_le_inf
      (prod_le_radical_prod_pow Finset.univ P e (fun i _ => he i)) B.le_radical)
  let : Finite (O ⧸ (∏ i, P i) * B) := Ring.HasFiniteQuotients.finiteQuotient hsmall0
  have hn := FiniteConductor.absNorm_le_of_le hsmall
  have hprod : (∏ i, P i) * (∏ i, P i ^ (e i-1)) = ∏ i, P i ^ e i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_succ']
    congr 1
    exact Nat.sub_add_cancel (he i)
  calc
    I.radical.absNorm * ∏ i, (P i).absNorm ^ (e i-1) ≤
        ((∏ i, P i) * B).absNorm * (∏ i, P i ^ (e i-1)).absNorm := by
      simpa only [map_prod, map_pow] using Nat.mul_le_mul_right
        (∏ i, (P i).absNorm ^ (e i-1)) hn
    _ = I.absNorm := by
      rw [← map_mul]
      congr 1
      calc
        ((∏ i, P i) * B) * (∏ i, P i ^ (e i-1)) =
            ((∏ i, P i) * (∏ i, P i ^ (e i-1))) * B := by ring
        _ = I := by rw [hprod, ← hB]

theorem rowCharacter_primitive_selected_deficit (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
          (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
          ψ.modulus.absNorm * ∏ i, (P i).absNorm ^ (e i-1) ≤
            fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).absNorm := by
  obtain ⟨ψ, hle, hp, hn, hm⟩ := rowCharacter_primitive_radical S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis e he hdiv
  have hb := radical_norm_selected_deficit (Ideal.span {u.val})
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1) P hP hdis e
    (fun i => (by have := he i; omega)) hdiv
  calc
    _ ≤ (fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).radical.absNorm) *
        ∏ i, (P i).absNorm ^ (e i-1) := Nat.mul_le_mul_right _ hn
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left (fixedConductorConstant S) hb

theorem canonicalCRT_radical_congr {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (e : ι → ℕ) (he : ∀ i, 1 ≤ e i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) (x y : O)
    (hxy : x-y ∈ (∏ i, P i ^ e i).radical) :
    CenteredMomentCanonical.canonicalCRTCharacter P hg e he hcop
        (Ideal.Quotient.mk (∏ i, P i ^ e i) x) =
      CenteredMomentCanonical.canonicalCRTCharacter P hg e he hcop
        (Ideal.Quotient.mk (∏ i, P i ^ e i) y) := by
  rw [CenteredMomentCanonical.canonicalCRTCharacter_mk,
    CenteredMomentCanonical.canonicalCRTCharacter_mk]
  exact idealRowHom_congr_radical _ x y hxy

theorem fixedConductorConstant_pos (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : 0 < fixedConductorConstant S := by
  have hnorm (I : Ideal O) (hI : I ≠ 0) : 0 < I.absNorm :=
    Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  unfold fixedConductorConstant ProbeHighRowFamily.conductorConstant
  exact mul_pos (mul_pos
    (hnorm _ (Ideal.span_singleton_eq_bot.not.mpr ProbeHighRowFamily.rowMaskElement_ne_zero))
    (hnorm _ (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))))
    (hnorm _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)))

theorem sourceRow_primitive_radical (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ I : Ideal O, ProbePhysical.highExclusion S hS I * idealRowHom u.val I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0 := by
  obtain ⟨ψ, hle, hp, hn, hm⟩ := rowCharacter_primitive_radical S hS u
  refine ⟨ψ, hle, hp, hn, ?_⟩
  intro I
  rw [← ProbeHighRowFamily.rowCharacter_coeff S hS hbad u I]
  exact hm I

theorem rowCharacter_primitive_selected_div (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : HeckeInverseAmplification.FreeRow) :
    ∃ ψ : Character, (ProbeHighRowFamily.rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (ProbeHighRowFamily.rowCharacter S hS u) I =
        if IsCoprime I (ProbeHighRowFamily.rowCharacter S hS u).modulus
        then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
          (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
          (ψ.modulus.absNorm : ℝ) ≤
            ((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) /
              ∏ i, ((P i).absNorm : ℝ) ^ (e i-1) := by
  obtain ⟨ψ, hle, hp, hm, hb⟩ := rowCharacter_primitive_selected_deficit S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis e he hdiv
  have hpos : 0 < ∏ i, ((P i).absNorm : ℝ) ^ (e i-1) := by
    apply Finset.prod_pos
    intro i _
    apply pow_pos
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hP i).ne_zero)
  apply (le_div_iff₀ hpos).mpr
  exact_mod_cast hb k P hP hdis e he hdiv

end SevenEighths.ProbeRowRadicalConductor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.MarkedProduct -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp
local notation "O" => HeckeFamily.O

def markExclusions (S : Finset (Ideal O)) (T : Finset ProbePhysical.PrimeIdeal) : Finset (Ideal O) :=
  S∪T.image Subtype.val

theorem markExclusions_prime (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset ProbePhysical.PrimeIdeal) : ∀P∈markExclusions S T,Prime P := by
  intro P hP
  rcases Finset.mem_union.mp hP with hP|hP
  · exact hS P hP
  · obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    exact Q.property

@[simp] theorem mem_markExclusions (S : Finset (Ideal O)) (T : Finset ProbePhysical.PrimeIdeal) (P : ProbePhysical.PrimeIdeal) :
    P.val∈markExclusions S T ↔ P.val∈S ∨ P∈T := by
  simp only [markExclusions,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro (h|⟨Q,hQ,he⟩)
    · exact Or.inl h
    · exact Or.inr ((Subtype.ext he : Q=P) ▸ hQ)
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr ⟨P,h,rfl⟩

theorem markedRowSeries_eq_finite_replacement (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u x w z=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,idealRowMarkedLocalFactor η u P x w z := by
  let R := fun P : ProbePhysical.PrimeIdeal=>if P∈T then idealRowMarkedLocalFactor η u P x w z else 1
  have hR : HasProd R (∏P∈T,idealRowMarkedLocalFactor η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional ProbePhysical.PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := (excludedIdealHighSeries_row_hasProd (markExclusions S T)
    (markExclusions_prime S hS T) η u x w z hx hw hz).mul hR
  have heq (P : ProbePhysical.PrimeIdeal) :
      (∑'b : HighValuation,markedIdealHighSummand (markExclusions S T) 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*R P=
      ∑'b : HighValuation,markedLocal T completedValuationMark
        (excludedRowPrimeTerm S η u x w z) P b := by
    rw [excludedRowHighLocalFactor _ (markExclusions_prime S hS T) η u x w z hx hw hz]
    by_cases hP : P∈T
    · rw [ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hP)),
        selectedRowLocal_outside S hS T η u P (hT P hP) x w z hx hw hz,ite_eq_left hP]
      simp only [R,ite_eq_left hP,one_mul]
    · simp only [R,ite_eq_right hP,mul_one,markedLocal,one_mul]
      change _=∑'b : HighValuation,markedIdealHighSummand S 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)
      rw [excludedRowHighLocalFactor S hS η u x w z hx hw hz]
      simp only [mem_markExclusions,hP,or_false]
  have he' : HasProd (fun P : ProbePhysical.PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedRowPrimeTerm S η u x w z) P b)
      (markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,idealRowMarkedLocalFactor η u P x w z) := by
    convert he using 1
    funext P
    exact (heq P).symm
  exact (markedRowSeries_hasProd S hS T η u x w z hx hw hz).unique he'

theorem markedRowSeries_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let S' := markExclusions S T
    let hS' := markExclusions_prime S hS T
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z=
      (LFunction (fixedSourcePrincipal S' hS') (6*z)*LFunction (rowCharacter S' hS' u) w/
        LFunction ((targetRow η u).excludePrimes S' hS') x*globalCorrection S' η u x w z)*
        ∏P∈T,idealRowMarkedLocalFactor η u.val P x w z := by
  dsimp only
  rw [markedRowSeries_eq_finite_replacement S hS T hT η u.val x w z hx hw hz,
    high_L_factorization (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.MarkedNormalization -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def localNormalization (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) (x w z : ℂ) : ℂ :=
  (1-CubicEisenstein.fullIdealWeight (6*z) P.val)*
    (1-idealRowHom u.val P.val*CubicEisenstein.fullIdealWeight w P.val)/
    (1-idealCoeff η P.val*starRingEnd ℂ (idealRowHom u.val P.val)*CubicEisenstein.fullIdealWeight x P.val)

def markedLocalCorrection (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) (x w z : ℂ) : ℂ :=
  idealRowMarkedLocalFactor η u.val P x w z*localNormalization η u P x w z

theorem localCorrection_eq_normalization (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) (x w z : ℂ) :
    localCorrection η u P x w z=idealRowHighLocalFactor η u.val P.val x w z*
      localNormalization η u P x w z := by
  unfold localCorrection localNormalization
  ring

lemma lift_outside_hasProd (S : Finset (Ideal O)) (f : ProbePhysical.PrimeIdeal→ℂ) (a : ℂ)
    (h : HasProd (fun P : {P : ProbePhysical.PrimeIdeal // P.val∉S}=>f P.val) a) :
    HasProd (fun P : ProbePhysical.PrimeIdeal=>if P.val∈S then 1 else f P) a := by
  have hh := (hasProd_subtype_iff_mulIndicator (s:={P : ProbePhysical.PrimeIdeal | P.val∉S}) (f:=f)).mp h
  convert hh using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

theorem localNormalization_hasProd (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 1<x.re) (hw : 1<w.re) (hz : 1<(6*z).re) :
    HasProd (fun P : ProbePhysical.PrimeIdeal=>if P.val∈S then 1 else localNormalization η u P x w z)
      ((LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
        (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x) := by
  apply lift_outside_hasProd
  have hZ := (fixedSourcePrincipal_hasProd S hS (6*z) hz).inv₀
    (LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz)
  have hW := (rowCharacter_hasProd S hS hbad u w hw).inv₀
    (LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw)
  have hD := targetRow_hasProd S hS hbad η u x hx
  simpa only [localNormalization,inv_inv,div_eq_mul_inv] using (hZ.mul hW).mul hD

theorem markedRowSeries_normalized (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z*
      ((LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
        (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x)=
      globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,markedLocalCorrection η u P x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hleft := (markedRowSeries_hasProd S hS T η u.val x w z hx hw hz).mul
    (localNormalization_hasProd S hS hbad η u x w z hx1 hw1 hz1)
  have hbase := lift_outside_hasProd (markExclusions S T) (fun P=>localCorrection η u P x w z) _
    (globalCorrection_multipliable (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz).hasProd
  let R := fun P : ProbePhysical.PrimeIdeal=>if P∈T then markedLocalCorrection η u P x w z else 1
  have hR : HasProd R (∏P∈T,markedLocalCorrection η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional ProbePhysical.PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have heq (P : ProbePhysical.PrimeIdeal) :
      (∑'b : HighValuation,markedLocal T completedValuationMark (excludedRowPrimeTerm S η u.val x w z) P b)*
        (if P.val∈S then 1 else localNormalization η u P x w z)=
      (if P.val∈markExclusions S T then 1 else localCorrection η u P x w z)*R P := by
    by_cases hP : P∈T
    · rw [selectedRowLocal_outside S hS T η u.val P (hT P hP) x w z hx hw hz,
        ite_eq_left hP,ite_eq_right (hT P hP),ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hP))]
      simp only [R,ite_eq_left hP,one_mul,markedLocalCorrection]
    · simp only [markedLocal,ite_eq_right hP,one_mul,R,mul_one]
      change (∑'b : HighValuation,markedIdealHighSummand S 1 η u.val x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*_=_
      rw [excludedRowHighLocalFactor S hS η u.val x w z hx hw hz]
      simp only [mem_markExclusions,hP,or_false]
      by_cases hPS : P.val∈S
      · simp only [ite_eq_left hPS,one_mul]
      · simp only [ite_eq_right hPS,localCorrection_eq_normalization]
  have hright := hbase.mul hR
  apply hleft.unique
  convert hright using 1
  · funext P
    exact heq P
  · rfl

theorem markedRowSeries_original_L_factorization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η u.val x w z=
      (LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (rowCharacter S hS u) w/
        LFunction ((targetRow η u).excludePrimes S hS) x)*
      (globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,markedLocalCorrection η u P x w z) := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hZ := LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := LFunction_ne_zero_of_one_lt_re ((targetRow η u).excludePrimes S hS) hx1
  rw [←markedRowSeries_normalized S hS hbad T hT η u x w z hx hw hz]
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.FiniteNormalization -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def globalNormalization (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  (LFunction (fixedSourcePrincipal S hS) (6*z))⁻¹*
    (LFunction (rowCharacter S hS u) w)⁻¹*LFunction ((targetRow η u).excludePrimes S hS) x

theorem globalNormalization_finite_split (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 1<x.re) (hw : 1<w.re) (hz : 1<(6*z).re) :
    globalNormalization S hS η u x w z=
      globalNormalization (markExclusions S T) (markExclusions_prime S hS T) η u x w z*
        ∏P∈T,localNormalization η u P x w z := by
  have hleft := localNormalization_hasProd S hS hbad η u x w z hx hw hz
  have hbase := localNormalization_hasProd (markExclusions S T) (markExclusions_prime S hS T)
    (hbad.trans Finset.subset_union_left) η u x w z hx hw hz
  let R := fun P : ProbePhysical.PrimeIdeal=>if P∈T then localNormalization η u P x w z else 1
  have hR : HasProd R (∏P∈T,localNormalization η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R)
      (L:=SummationFilter.unconditional ProbePhysical.PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  apply hleft.unique
  convert hbase.mul hR using 1
  · funext P
    by_cases hP : P∈T
    · simp only [ite_eq_right (hT P hP),mem_markExclusions,hP,or_true,ite_true,R,ite_eq_left hP,one_mul]
    · simp only [mem_markExclusions,hP,or_false,R,ite_eq_right hP,mul_one]
  · rfl

theorem finite_replacement_normalized (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow) (x w z : ℂ)
    (g : ProbePhysical.PrimeIdeal→ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    (markedIdealHighSeries (markExclusions S T) 1 η u.val x w z*∏P∈T,g P)*
      globalNormalization S hS η u x w z=
      globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,g P*localNormalization η u P x w z := by
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  rw [globalNormalization_finite_split S hS hbad T hT η u x w z (by linarith) (by linarith) hz1,
    globalCorrection,(localCorrection_hasProd (markExclusions S T) (markExclusions_prime S hS T)
      (hbad.trans Finset.subset_union_left) η u x w z hx hw hz).tprod_eq,
    Finset.prod_mul_distrib,globalNormalization]
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.Moments -/

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CanonicalRowCompletion
open ProbePhysical

def momentData (η : Character) : RowData where
  η := η
  m := rowMaskElement
  f := 1
  m_ne_zero := rowMaskElement_ne_zero
  f_ne_zero := one_ne_zero
  lambda_dvd := dvd_mul_left _ _
  two_dvd := dvd_mul_right _ _

def momentElement (u : FreeRow) : NonzeroElement := ⟨u.val,u.property.1⟩

theorem momentData_coeff (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((momentData η).character (momentElement u)) I=
      idealCoeff η I*idealRowHom (rowMaskElement^6*u.val) I := by
  simpa only [momentData,momentElement,one_pow,mul_one] using
    idealCoeff_eq_row η ((momentData η).character (momentElement u)) rowMaskElement 1 u.val
      ((momentData η).character_spec (momentElement u)) I

theorem momentData_prime_outside (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (P : ProbePhysical.PrimeIdeal) (hP : P.val∉S) :
    idealCoeff ((momentData η).character (momentElement u)) P.val=
      idealCoeff η P.val*idealRowHom u.val P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  obtain ⟨hg,hc⟩ := outside_good_coprime S hS hbad P hP
  rw [momentData_coeff,idealRowHom_argument_mul,
    idealRowHom_prime_sixth_mask rowMaskElement P.val hg,ite_eq_left hc,one_mul]

theorem numerator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    idealCoeff (rowCharacter S hS u) I=
      idealCoeff ((momentData (fixedSourcePrincipal S hS)).character (momentElement u)) I := by
  have he : idealCoeff (rowCharacter S hS u)=
      idealCoeff ((momentData (fixedSourcePrincipal S hS)).character (momentElement u)) := by
    apply hom_eq_of_primes
    intro P
    change idealCoeff ((rawRow u).excludePrimes S hS) P.val=_
    rw [excludedTarget_prime]
    by_cases hP : P.val∈S
    · rw [ite_eq_left hP,momentData_coeff,fixedSourcePrincipal_prime,ite_eq_left hP,zero_mul]
    · rw [ite_eq_right hP,rawRow_prime_outside S hS hbad u P hP,
        momentData_prime_outside S hS hbad _ u P hP,
        fixedSourcePrincipal_prime,ite_eq_right hP,one_mul]
  exact congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem denominator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((targetRow η u).excludePrimes S hS) I=
      conj (idealCoeff ((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)) I) := by
  have he : idealCoeff ((targetRow η u).excludePrimes S hS)=
      idealCoeff (((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)).inverse) := by
    apply hom_eq_of_primes
    intro P
    rw [idealCoeff_inverse_conj]
    change idealCoeff ((η.product (rawRow u).inverse).excludePrimes S hS) P.val=_
    rw [target_inverseRow_coeff S hS hbad]
    by_cases hP : P.val∈S
    · rw [ite_eq_left hP,momentData_coeff,excludedTarget_prime,ite_eq_left hP,zero_mul,map_zero]
    · rw [ite_eq_right hP,momentData_prime_outside S hS hbad _ u P hP,
        excludedTarget_prime,ite_eq_right hP,idealCoeff_inverse_conj,map_mul]
      simp only [starRingEnd_self_apply]
  simpa only [idealCoeff_inverse_conj] using congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem numerator_moment_polynomial (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    HeckeDyadic.polynomial (rowCharacter S hS u) inv W D σ freq=
      HeckeDyadic.polynomial ((momentData (fixedSourcePrincipal S hS)).character
        (momentElement u)) inv W D σ freq :=
  HeckeDetectorCoefficientTransfer.polynomial_eq_of_idealCoeff _ _
    (numerator_moment_coeff S hS hbad u) inv W D σ freq

theorem denominator_moment_norm (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖HeckeDyadic.polynomial ((targetRow η u).excludePrimes S hS) inv W D σ freq‖=
      ‖HeckeDyadic.polynomial ((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)) inv (fun x=>conj (W x)) D σ (-freq)‖ :=
  HeckeDetectorCoefficientTransfer.norm_of_oriented_coefficients _ _ true
    (denominator_moment_coeff S hS hbad η u) inv W D σ freq hD

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.Principal -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalRowCompletion
open CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma rawRow_elementCoeff (u : FreeRow) (n : O) :
    elementCoeff (rawRow u) n = rowTwist (HeckeRowClosure.elementHom
      (fixedSourcePrincipal ∅ (by simp))) rowMaskElement 1 u.val n :=
  (Classical.choose_spec (HeckeRowClosure.exists_row_character_with_conductor
    (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
    rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2 n

lemma rowCharacter_principal_iff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) :
    (rowCharacter S hS u).residue=1 ↔ (rawRow u).residue=1 :=
  HeckeFiniteDeletion.principal_iff_of_mask _ _ (excludePrimes_mask (rawRow u) S hS)

lemma supported_coprime_row_fixed (r : O) (hr : Supported (Ideal.span {r})) :
    IsCoprime (Ideal.span {r})
      ((fixedSourcePrincipal ∅ (by simp)).modulus*Ideal.span {rowMaskElement}*
        Ideal.span {(72:O)}) := by
  have hl : IsCoprime λ₀ r :=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
      ((supported_span_iff r).mp hr).1
  have hn : IsCoprime (-2:O) r := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff r).mp hr).2)
  have h2 : IsCoprime (2:O) r := hn.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  have h9 : IsCoprime (9:O) r := ShortDraftCRT.nine_coprime_of_not_lambda_dvd r
    ((supported_span_iff r).mp hr).1
  have h72 : IsCoprime (72:O) r := by
    convert (h2.pow_left (m:=3)).mul_left h9 using 1; norm_num
  have hm := (h2.mul_left hl).symm
  have hmod : (fixedSourcePrincipal ∅ (by simp)).modulus=(1:Ideal O) := by
    simp [fixedSourcePrincipal,HeckeRayFamily.character,Character.ofResidue]
  rw [hmod,one_mul]
  exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr hm).mul_right
    ((Ideal.isCoprime_span_singleton_iff _ _).mpr h72.symm)

theorem rawRow_principal_supported_isUnit (u : FreeRow)
    (hu : Supported (Ideal.span {u.val})) (hp : (rawRow u).residue=1) : IsUnit u.val := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val hu
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hu
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*λ₀^0*(2:O)^0*r := by
    simp [r]
  have hempty : normalizedFactors (Ideal.span {r})=0 := by
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro P hP
    have hcop : IsCoprime
        ((fixedSourcePrincipal ∅ (by simp)).modulus*Ideal.span {rowMaskElement}*Ideal.span {(72:O)}) P :=
      (supported_coprime_row_fixed r hr).symm.of_isCoprime_of_dvd_right (dvd_of_mem_normalizedFactors hP)
    have hd := HeckeRowNonprincipal.principal_row_multiplicity
      (fixedSourcePrincipal ∅ (by simp)) (rawRow u) rowMaskElement 1 u.val
      (dvd_mul_left _ _) (dvd_mul_right _ _) v⁻¹ 0 0 r hr hv hx (rawRow_elementCoeff u) hp P hP hcop
    have hlt : (normalizedFactors (Ideal.span {r})).count P<6 := by
      rw [hspan]
      exact u.property.2 P
    exact Nat.not_dvd_of_pos_of_lt (Multiset.count_pos.mpr hP) hlt hd
  have hone : (Ideal.span {u.val}:Ideal O)=1 := by
    rw [←hspan,←Ideal.prod_normalizedFactors_eq_self hr.1,hempty,Multiset.prod_zero]
  exact Ideal.span_singleton_eq_top.mp (by simpa only [Ideal.one_eq_top] using hone)

lemma idealCoeff_principal_eq_one (χ : Character) (hχ : χ.residue=1)
    (I : Ideal O) (hI : idealCoeff χ I≠0) : idealCoeff χ I=1 := by
  change IdealCharacter.value χ.modulus χ.residue I=1
  change IdealCharacter.value χ.modulus χ.residue I≠0 at hI
  unfold IdealCharacter.value at *
  split_ifs at * with hzero
  · exact False.elim (hI rfl)
  · have hu := MulChar.apply_ne_zero_iff.mp hI
    rw [hχ,MulChar.one_apply hu]

theorem rowCharacter_unit_nonprincipal (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (v : Oˣ) (hu : u.val=(v:O)) (hv : v≠1) :
    (rowCharacter S hS u).residue≠1 := by
  obtain ⟨P,hmax,hPS,hN,hg,hodd,hval0,hval1⟩ := UnitSexticWitness.exists_unit_witness v hv S 0
  let : P.IsMaximal := hmax
  have hP0 : P≠0 := by
    intro he
    simp [he] at hN
  let Q : ProbePhysical.PrimeIdeal := ⟨P,Ideal.prime_of_isPrime hP0 hmax.isPrime⟩
  have he : idealCoeff (rowCharacter S hS u) P=idealRowHom (v:O) P := by
    rw [rowCharacter_coeff S hS hbad,highExclusion_prime S hS Q,ite_eq_right hPS,one_mul,hu]
  intro hp
  have hv0 : idealCoeff (rowCharacter S hS u) P≠0 := he ▸ hval0
  exact hval1 (he.symm.trans (idealCoeff_principal_eq_one _ hp P hv0))

theorem rowCharacter_principal_supported_eq_one (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (hu : Supported (Ideal.span {u.val})) (hp : (rowCharacter S hS u).residue=1) : u.val=1 := by
  obtain ⟨v,hv⟩ := rawRow_principal_supported_isUnit u hu ((rowCharacter_principal_iff S hS u).mp hp)
  by_contra hn
  have hv1 : v≠1 := by
    intro he
    subst v
    exact hn hv.symm
  exact rowCharacter_unit_nonprincipal S hS hbad u v hv.symm hv1 hp

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.ReciprocalGrowth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem targetRow_reciprocal_growth (e δ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hδ : 0<δ) (hδ' : δ≤2) (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (x : ℂ),
      HeckeZeroSupremum.beta+8*e≤x.re →
      ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS) x‖≤
        C*(η.modulus.absNorm:ℝ)^δ*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ*(3+|x.im|)^2 := by
  obtain ⟨D,hD,hmain⟩ := HeckeReciprocalGrowth.reciprocal_subpower e (δ/2) he he' (by linarith)
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨D*(2:ℝ)^(δ/2)*(1+A^δ),by positivity,?_⟩
  intro η u x hx
  let q : ℝ := η.modulus.absNorm
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hq : 0≤q := by dsimp [q];positivity
  have hN : 0≤N := by dsimp [N];positivity
  have hQ : (((targetRow η u).excludePrimes S hS).modulus.absNorm:ℝ)≤A*q*N := by
    have hh := targetRow_excluded_conductor S hS η u
    dsimp [A,q,N]
    exact_mod_cast (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hh)
  have hc := HeckeDyadic.presentationComplexity_le_of_modulus_le
    ((targetRow η u).excludePrimes S hS) (A*q*N) x.im hQ
  have ht : 0≤3+|x.im| := by positivity
  have hpow : (2*(A*q*N)^2*(3+|x.im|)^2)^(δ/2)=
      (2:ℝ)^(δ/2)*A^δ*q^δ*N^δ*(3+|x.im|)^δ := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity),
      ←Real.rpow_natCast_mul (mul_nonneg (mul_nonneg hA hq) hN),
      ←Real.rpow_natCast_mul ht]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(δ/2)=δ by ring,
      Real.mul_rpow (mul_nonneg hA hq) hN,Real.mul_rpow hA hq]
    ring
  have hbase := hmain ((targetRow η u).excludePrimes S hS) x hx
  calc
    _ ≤ D*(2*(A*q*N)^2*(3+|x.im|)^2)^(δ/2) := by
      apply hbase.trans
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact Real.rpow_le_rpow (by unfold HeckeReciprocalGrowth.presentationComplexity HeckeLogarithmic.complexity;positivity) hc (by linarith)
    _ = D*(2:ℝ)^(δ/2)*A^δ*q^δ*N^δ*(3+|x.im|)^δ := by rw [hpow];ring
    _ ≤ D*(2:ℝ)^(δ/2)*(1+A^δ)*q^δ*N^δ*(3+|x.im|)^2 := by
      have hh : (3+|x.im|)^δ≤(3+|x.im|)^2 := by
        simpa only [Real.rpow_ofNat] using
          (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg x.im] : (1:ℝ)≤3+|x.im|) hδ')
      apply mul_le_mul _ hh (Real.rpow_nonneg ht δ) (by positivity)
      gcongr
      linarith

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.Unramified -/

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem localCorrection_coordinates (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (x w z : ℂ) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u.val)
    localCorrection η u ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ x w z=
      idealRowHighLocalFactor η u.val (Ideal.span {p}) x w z *
        (1-coordV Q z)*(1-coordW Q rho w)/(1-coordD Q (targetMonoid η p) rho x) := by
  dsimp only
  have hP0 : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  unfold localCorrection coordV coordW coordD
  simp only [CubicEisenstein.fullIdealWeight,hP0,ite_false,Complex.ofReal_natCast]
  rw [idealCoeff_span η hp.ne_zero,idealRowHom_prime u.val (Ideal.span {p}) hg]
  rw [show -(6*z)=(-6 : ℂ)*z by ring]
  rfl

theorem localCorrection_unramified (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : CanonicalQuadraticSieve.Supported (Ideal.span {p})) (hu : IsCoprime u.val p)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ x w z=
      actualUnramifiedClosed η p u.val hg x w z := by
  rw [localCorrection_coordinates η u p hp hg]
  rw [idealRowHighLocalFactor_unramified η p hp hg hc hprimary hs u.val hu x w z hx hw hz]
  have hgeom := row_initial_geometric η p hp hg hc u.val hu x w z hx hw hz
  dsimp only at hgeom
  have hV := one_sub_ne_zero_of_norm_lt_one _ hgeom.1
  have hW := one_sub_ne_zero_of_norm_lt_one _ hgeom.2.2.1
  have hD := one_sub_ne_zero_of_norm_lt_one _ hgeom.2.2.2
  unfold actualUnramifiedClosed
  change _=unramifiedClosed _ _ (targetMonoid η p) _ x w z
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.Ideal -/

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def idealUnramifiedCorrection (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) (x w z : ℂ) : ℂ :=
  unramifiedClosed P.val.absNorm (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) (idealRowHom u.val P.val) x w z

theorem localCorrection_unramified_ideal (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hcop : IsCoprime P.val (Ideal.span {u.val}))
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=idealUnramifiedCorrection η u P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  have hu : IsCoprime u.val p := ((Ideal.isCoprime_span_singleton_iff p u.val).mp
    (by rw [hspan]; exact hcop)).symm
  have he := localCorrection_unramified η u p hp hg.1 hg.2 hprimary hsp hu x w z hx hw hz
  have hP : (⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ : ProbePhysical.PrimeIdeal)=P := Subtype.ext hspan
  rw [hP] at he
  unfold actualUnramifiedClosed at he
  rw [←idealCoeff_span η hp.ne_zero,←idealRowHom_prime u.val (Ideal.span {p}) hg.1,hspan] at he
  exact he

theorem localCorrection_outside_unramified (S : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (P : ProbePhysical.PrimeIdeal) (hP : P.val∉S) (hcop : IsCoprime P.val (Ideal.span {u.val}))
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=idealUnramifiedCorrection η u P x w z :=
  localCorrection_unramified_ideal η u P (outside_prime_supported S hbad P hP) hcop x w z hx hw hz

theorem localCorrection_ramified (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    localCorrection η u P x w z=
      idealRowHighLocalFactor η u.val P.val x w z*(1-CubicEisenstein.fullIdealWeight (6*z) P.val) := by
  have hu : u.val∈P.val := (Ideal.dvd_iff_le.mp hP) (Ideal.subset_span (by simp))
  have hr : idealRowHom u.val P.val=0 := idealRowHom_zero_of_dvd u.val P.property (dvd_refl _) hu
  simp only [localCorrection,hr,map_zero,mul_zero,zero_mul,sub_zero,mul_one,div_one]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.Ramified -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def ramifiedCorrection (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  letI : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    x w z (multiplicity p u.val)

theorem ramifiedCorrection_bound (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4 : ℝ)≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (19/20 : ℝ)≤w.re) (hz : (33/200 : ℝ)≤z.re) :
    ‖ramifiedCorrection η u P hs x w z‖≤193 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have ha : ‖actualACube η p‖≤1 := by
    have h := actualAPhase_norm_le_one η p
    rw [←actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube η p)]
  exact ramifiedClosed_bound p hp hg.1 hg.2 _ _ _ x w z
    (hspan.symm ▸ hQ) (targetMonoid_norm_le_one η p) ha
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz _

theorem localCorrection_eq_ramified (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hPu : P.val∣Ideal.span {u.val})
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=ramifiedCorrection η u P hs x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  have hdiv : p∣u.val := Ideal.span_singleton_le_span_singleton.mp
    (by rw [hspan]; exact Ideal.dvd_iff_le.mp hPu)
  have hj0 : multiplicity p u.val≠0 := ne_of_gt (multiplicity_pos_of_dvd hdiv
    (FiniteMultiplicity.of_prime_left hp u.property.1))
  have hρ := actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)
  have hgeom := row_initial_geometric η p hp hg.1 hg.2 (unitPart u p hp)
    (unitPart_coprime u p hp) x w z hx hw hz
  dsimp only at hgeom
  have hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    have hpos : (0 : ℝ)<Ideal.absNorm (Ideal.span {p}) :=
      HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
    have he := evenRatio_eq_coordR _ hpos (actualACube η p) x z
    simp only [Complex.ofReal_natCast] at he
    rw [he]
    exact hgeom.2.1
  rw [localCorrection_ramified η u P hPu,←hspan,
    idealRowHighLocalFactor_canonical η u p hp hg.1 hg.2 hprimary hsp]
  have he := sourceRowSeries_ramified p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p) _ x w z hρ hgeom.1 hR
    hgeom.2.2.1 (multiplicity p u.val) hj0 (multiplicity_lt_six u p hp)
  have hP0 : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  convert he using 1
  · simp only [sourceRowSeries,CubicEisenstein.fullIdealWeight,
      hP0,ite_false,Complex.ofReal_natCast,coordV]
    rw [show -(6*z)=(-6 : ℂ)*z by ring]
  · rfl

def ramifiedPrimes (S : Finset (Ideal O)) (u : FreeRow) : Finset ProbePhysical.PrimeIdeal :=
  (SmoothMobiusCorrection.primeSet (Ideal.span {u.val})).filter (fun P => P.val∉S)

theorem ramified_product_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (η : Character) (u : FreeRow) (x w z : ℂ),
      (7/8 : ℝ)≤x.re → (19/20 : ℝ)≤w.re → (33/200 : ℝ)≤z.re →
      ‖∏ P∈(ramifiedPrimes S u).attach,
        ramifiedCorrection η u P.val
          (outside_prime_supported S hS.bad P.val (Finset.mem_filter.mp P.property).2) x w z‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeDeletionBounds.constant_pow_primeSupport_bound 193 ε (by norm_num) hε
  refine ⟨C,hC,?_⟩
  intro S hS η u x w z hx hw hz
  rw [norm_prod]
  calc
    _ ≤ ∏ P∈(ramifiedPrimes S u).attach,(193 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P hP
      exact ramifiedCorrection_bound η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (Finset.mem_filter.mp P.property).2) x w z hx hw hz
    _ = (193 : ℝ)^(ramifiedPrimes S u).card := by simp
    _ ≤ (193 : ℝ)^(IdealMobiusDivisorSum.primeSupport (Ideal.span {u.val})).card := by
      apply pow_le_pow_right₀ (by norm_num)
      rw [←HeckeDeletionBounds.primeSet_card]
      exact Finset.card_filter_le _ _
    _ ≤ _ := hbound _ (Ideal.span_singleton_eq_bot.not.mpr u.property.1)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.Product -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

def unramifiedFactor (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) (x w z : ℂ) : ℂ :=
  if P.val∣Ideal.span {u.val} then 1 else idealUnramifiedCorrection η u P x w z

def unramifiedProduct (S : Finset (Ideal O)) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : ProbePhysical.PrimeIdeal // P.val∉S},unramifiedFactor η u P.val x w z

theorem unramifiedFactor_defect (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hP : 4≤P.val.absNorm) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    ‖unramifiedFactor η u P x w z-1‖≤globalPrimeDefectBound P := by
  unfold unramifiedFactor
  split_ifs
  · simpa using globalPrimeDefectBound_nonneg P
  · apply unramifiedClosed_open_region_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · exact idealRowHom_norm u.val _
    · exact hx
    · exact hw
    · exact hz

theorem unramifiedProduct_defect (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    ‖unramifiedProduct S η u x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P => unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

theorem unramifiedProduct_multipliable (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    Multipliable (fun P : {P : ProbePhysical.PrimeIdeal // P.val∉S} =>unramifiedFactor η u P.val x w z) := by
  let F := fun P : {P : ProbePhysical.PrimeIdeal // P.val∉S} => unramifiedFactor η u P.val x w z
  let B := fun P : {P : ProbePhysical.PrimeIdeal // P.val∉S} => globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤B P :=
    unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem unramifiedProduct_analytic_x (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (w z : ℂ) (hw : (9/10 : ℝ)≤w.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun x =>unramifiedProduct S η u x w z) {x : ℂ | 7/8<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply unramifiedClosed_analytic_x
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hz
  · intro P x hx
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem unramifiedProduct_analytic_w (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x z : ℂ) (hx : (7/8 : ℝ)≤x.re) (hz : (4/25 : ℝ)≤z.re) :
    AnalyticOnNhd ℂ (fun w =>unramifiedProduct S η u x w z) {w : ℂ | 9/10<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [unramifiedFactor,ite_eq_right h]
      apply unramifiedClosed_analytic_w
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hx
      · exact hz
  · intro P w hw
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem unramifiedProduct_analytic_z (S : Finset (Ideal O)) (hS : CorrectionTail S)
    (η : Character) (u : FreeRow) (x w : ℂ) (hx : (7/8 : ℝ)≤x.re) (hw : (9/10 : ℝ)≤w.re) :
    AnalyticOnNhd ℂ (fun z =>unramifiedProduct S η u x w z) {z : ℂ | 4/25<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    change AnalyticOnNhd ℂ (fun z : ℂ => if P.val.val∣Ideal.span {u.val} then 1
      else idealUnramifiedCorrection η u P.val x w z) _
    by_cases h : P.val.val∣Ideal.span {u.val}
    · simpa only [unramifiedFactor,ite_eq_left h] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) _)
    · simp only [ite_eq_right h]
      apply unramifiedClosed_analytic_z
      · exact_mod_cast hS.norm_four P.val P.property
      · exact actualAPhase_norm_le_one η _
      · exact idealCoeff_norm_le_one η _
      · exact idealRowHom_norm u.val _
      · exact hx
  · intro P z hz
    exact unramifiedFactor_defect η u P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

