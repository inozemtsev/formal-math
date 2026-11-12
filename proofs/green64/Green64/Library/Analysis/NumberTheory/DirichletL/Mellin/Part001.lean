module

public import Green64.Library.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Mellin / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace CubicReflectionKernel

section
open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

theorem reflectedLogProfile_deriv_bound (logSource : SchwartzMap ℝ ℂ) (j : ℕ) (y : ℝ) :
    ‖iteratedDeriv j (reflectedLogProfile logSource) y‖ ≤
      (2 * Real.pi) ^ j * ∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖ := by
  rw [reflectedLogProfile_deriv]
  have hb := VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ)
    (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u) y
  change ‖𝓕 (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u) y‖ ≤ _ at hb
  refine hb.trans_eq ?_
  have hnorm (u : ℝ) :
      ‖(-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u‖ =
        (2 * Real.pi) ^ j * (‖u‖ ^ j * ‖(𝓕 logSource) u‖) := by
    simp only [norm_mul, norm_pow, spectralProfile_norm, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  simp_rw [hnorm]
  exact integral_const_mul _ _

def momentScale : ℝ :=
  2 ^ (volume : Measure ℝ).integrablePower *
    ∫ u : ℝ, (1 + ‖u‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)

theorem momentScale_nonneg : 0 ≤ momentScale := by
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro u
  positivity

theorem reflectedLogProfile_source_bound (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (logSource : SchwartzMap ℝ ℂ) (y : ℝ),
        ‖iteratedDeriv j (reflectedLogProfile logSource) y‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by
  let m := j + (volume : Measure ℝ).integrablePower
  let S : Finset (ℕ × ℕ) := {(0, 0), (m, 0)}
  obtain ⟨s, C, hC, hbound⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control (E := ℝ)
    (FourierTransform.fourierCLM ℝ (SchwartzMap ℝ ℂ)) S
  refine ⟨s, (2 * Real.pi) ^ j * (momentScale + 1) * (2 * C), by
    have := momentScale_nonneg
    positivity, ?_⟩
  intro logSource y
  have h0' : schwartzSeminormFamily ℝ ℝ ℂ (0, 0) ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
    Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S])
  have hm' : schwartzSeminormFamily ℝ ℝ ℂ (m, 0) ≤
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
    Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S])
  have h0 := Seminorm.le_def.mp h0' (𝓕 logSource)
  have hm := Seminorm.le_def.mp hm' (𝓕 logSource)
  change SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) ≤ _ at h0
  change SchwartzMap.seminorm ℝ m 0 (𝓕 logSource) ≤ _ at hm
  have hs := hbound logSource
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (𝓕 logSource) ≤ _ at hs
  have hsum : SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) + SchwartzMap.seminorm ℝ m 0 (𝓕 logSource) ≤
      2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by linarith
  have hmoment := FourierBridge.fourier_coefficient_moment logSource j
  change (∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖) ≤ momentScale *
    (SchwartzMap.seminorm ℝ 0 0 (𝓕 logSource) + SchwartzMap.seminorm ℝ m 0 (𝓕 logSource)) at hmoment
  calc
    _ ≤ (2 * Real.pi) ^ j * ∫ u : ℝ, ‖u‖ ^ j * ‖(𝓕 logSource) u‖ :=
      reflectedLogProfile_deriv_bound logSource j y
    _ ≤ (2 * Real.pi) ^ j * (momentScale *
        (2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource)) := by
      exact mul_le_mul_of_nonneg_left
        (hmoment.trans (mul_le_mul_of_nonneg_left hsum momentScale_nonneg)) (by positivity)
    _ ≤ _ := by
      have hpos : 0 ≤ 2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource := by positivity
      calc
        _ ≤ (2 * Real.pi) ^ j * ((momentScale + 1) *
            (2 * C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) logSource)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right zero_le_one) hpos) (by positivity)
        _ = _ := by ring

end

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

def paperScale : ℝ := (2 * Real.pi) ^ 4 / 27

theorem paperScale_pos : 0 < paperScale := by
  unfold paperScale
  positivity

def paperKernel (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  mellinInv 0 (fun t => mellin V (-t) * gammaMultiplier t) (paperScale * x)

theorem logProfile_compact (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) :
    HasCompactSupport (fun u : ℝ => V (Real.exp u)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (Real.log a) (Real.log b)) isCompact_Icc
  intro u hu
  have huv : V (Real.exp u) ≠ 0 := hu
  have hm := hsupp huv
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log ha hm.1
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hm.2

def logSchwartz (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    SchwartzMap ℝ ℂ :=
  (logProfile_compact V a b ha hsupp).toSchwartzMap (hV.comp Real.contDiff_exp)

@[simp] theorem logSchwartz_apply (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (u : ℝ) :
    logSchwartz V a b ha hsupp hV u = V (Real.exp u) := rfl

theorem compact_source_mellin_convergent
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) : MellinConvergent V s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

theorem mellin_axis_eq_fourier (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (u : ℝ) :
    mellin V (-((2 * Real.pi * u : ℝ) * Complex.I)) = (𝓕 logSource) u := by
  rw [mellin_eq_fourier]
  have hfreq : (-((2 * Real.pi * u : ℝ) * Complex.I) : ℂ).im / (2 * Real.pi) = -u := by
    simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    field_simp
  rw [hfreq]
  have hfun : (fun v : ℝ => Real.exp
      (-(-((2 * Real.pi * u : ℝ) * Complex.I) : ℂ).re * v) • V (Real.exp (-v))) =
      (logSource : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ := by
    funext v
    simp [hL]
  rw [hfun, Real.fourier_comp_linearIsometry]
  simp
  rfl

theorem paperKernel_eq_logFourier (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (x : ℝ) (hx : 0 < x) :
    paperKernel V x = reflectedLogProfile logSource (Real.log (paperScale * x)) := by
  unfold paperKernel
  rw [mellinInv_eq_fourierInv 0 _ (mul_pos paperScale_pos hx)]
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul]
  rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have hfun : (fun y : ℝ => mellin V (-(0 + 2 * Real.pi * y * Complex.I)) *
      gammaMultiplier (0 + 2 * Real.pi * y * Complex.I)) = spectralProfile logSource := by
    funext y
    have hy : (0 + 2 * Real.pi * y * Complex.I : ℂ) =
        ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hy, mellin_axis_eq_fourier V logSource hL]
    exact mul_comm _ _
  rw [hfun]
  rfl

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

theorem kernel_vertical_eq_spectralProfile (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (y : ℝ) :
    mellin V (-(y * Complex.I)) * gammaMultiplier (y * Complex.I) =
      spectralProfile logSource (y / (2 * Real.pi)) := by
  have hy : 2 * Real.pi * (y / (2 * Real.pi)) = y := by field_simp
  rw [spectralProfile, axisMultiplier, ← mellin_axis_eq_fourier V logSource hL, hy]
  exact mul_comm _ _

theorem kernel_vertical_integrable (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) :
    Complex.VerticalIntegrable (fun t => mellin V (-t) * gammaMultiplier t) 0 := by
  have hi : Integrable (spectralProfile logSource) := by
    simpa using spectralProfile_pow_integrable logSource 0
  have hscaled := hi.comp_div (R := 2 * Real.pi) (by positivity)
  simpa only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add,
    kernel_vertical_eq_spectralProfile V logSource hL] using hscaled

theorem paperKernel_integrable (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (x : ℝ) (hx : 0 < x) :
    Integrable (fun y : ℝ => ((paperScale * x : ℝ) : ℂ) ^ (-(y * Complex.I)) *
      (mellin V (-(y * Complex.I)) * gammaMultiplier (y * Complex.I))) := by
  have hcx := mul_pos paperScale_pos hx
  have hi := kernel_vertical_integrable V logSource hL
  simp only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add] at hi
  apply hi.bdd_mul (c := 1)
  · exact ((show Continuous (fun y : ℝ => -(y * Complex.I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hcx)))).aestronglyMeasurable
  · filter_upwards [] with y
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hcx]
    simp

theorem paperKernel_contDiffOn (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) :
    ContDiffOn ℝ ∞ (paperKernel V) (Set.Ioi 0) := by
  have hg : ContDiffOn ℝ ∞
      (fun x => reflectedLogProfile logSource (Real.log (paperScale * x))) (Set.Ioi 0) := by
    intro x hx
    apply (reflectedLogProfile_smooth logSource).contDiffAt.comp_contDiffWithinAt x
    exact ((contDiffAt_const.mul contDiffAt_id).log
      (ne_of_gt (mul_pos paperScale_pos hx))).contDiffWithinAt
  apply hg.congr
  intro x hx
  exact paperKernel_eq_logFourier V logSource hL x hx

theorem paperKernel_euler_eq (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    LocalLogFourier.eulerDeriv (paperKernel V) j x =
      iteratedDeriv j (reflectedLogProfile logSource) (Real.log (paperScale * x)) := by
  have hfun : (fun t : ℝ => paperKernel V (x * Real.exp t)) =
      (fun t : ℝ => reflectedLogProfile logSource (Real.log (paperScale * x) + t)) := by
    funext t
    rw [paperKernel_eq_logFourier V logSource hL _ (mul_pos hx (Real.exp_pos t))]
    rw [← mul_assoc, Real.log_mul (ne_of_gt (mul_pos paperScale_pos hx))
      (ne_of_gt (Real.exp_pos t)), Real.log_exp]
  rw [LocalLogFourier.eulerDeriv, hfun, iteratedDeriv_comp_const_add]
  simp

theorem paperKernel_source_euler_bound (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
        (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
        (x : ℝ), 0 < x →
        ‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (logSchwartz V a b ha hsupp hV) := by
  obtain ⟨s, C, hC, hb⟩ := reflectedLogProfile_source_bound j
  refine ⟨s, C, hC, ?_⟩
  intro V a b ha hsupp hV x hx
  rw [paperKernel_euler_eq V (logSchwartz V a b ha hsupp hV) (by intro u; rfl) j x hx]
  exact hb _ _

theorem paperKernel_compact_source_integrable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (x : ℝ) (hx : 0 < x) :
    Integrable (fun y : ℝ => ((paperScale * x : ℝ) : ℂ) ^ (-(y * Complex.I)) *
      (mellin V (-(y * Complex.I)) * gammaMultiplier (y * Complex.I))) :=
  paperKernel_integrable V (logSchwartz V a b ha hsupp hV) (by intro u; rfl) x hx

theorem paperKernel_compact_source_smooth
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (paperKernel V) (Set.Ioi 0) :=
  paperKernel_contDiffOn V (logSchwartz V a b ha hsupp hV) (by intro u; rfl)

theorem reflectedLogProfile_deriv_vanish (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    Tendsto (iteratedDeriv j (reflectedLogProfile logSource)) (cocompact ℝ) (𝓝 0) := by
  rw [reflectedLogProfile_deriv]
  exact Real.zero_at_infty_fourier _

theorem paperKernel_euler_vanish_infty (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) :
    Tendsto (LocalLogFourier.eulerDeriv (paperKernel V) j) atTop (𝓝 0) := by
  have hd := (reflectedLogProfile_deriv_vanish logSource j).mono_left atTop_le_cocompact
  have hlog : Tendsto (fun x : ℝ => Real.log (paperScale * x)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Tendsto.const_mul_atTop paperScale_pos tendsto_id)
  apply (hd.comp hlog).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (paperKernel_euler_eq V logSource hL j x hx).symm

theorem paperKernel_euler_vanish_zero (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) :
    Tendsto (LocalLogFourier.eulerDeriv (paperKernel V) j) (𝓝[>] 0) (𝓝 0) := by
  have hd := (reflectedLogProfile_deriv_vanish logSource j).mono_left atBot_le_cocompact
  have hmul : Tendsto (fun x : ℝ => paperScale * x) (𝓝[>] 0) (𝓝[>] 0) := by
    have hm : Tendsto (fun x : ℝ => paperScale * x)
        (comap (fun x : ℝ => paperScale * x) (𝓝[>] 0)) (𝓝[>] 0) := tendsto_comap
    rwa [comap_mulLeft_nhdsGT_zero paperScale_pos] at hm
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hmul
  apply (hd.comp hlog).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (paperKernel_euler_eq V logSource hL j x hx).symm

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

theorem compact_source_mellin_hasDerivAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) :
    HasDerivAt (mellin V) (mellin (fun t => Real.log t • V t) s) s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact (mellin_hasDerivAt_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)).2

theorem compact_source_mellin_differentiable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    Differentiable ℂ (mellin V) :=
  fun s => (compact_source_mellin_hasDerivAt V a b ha hsupp hV s).differentiableAt

theorem Gamma_differentiableAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem gammaMultiplier_differentiableAt (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ gammaMultiplier s := by
  have h1 := (Gamma_differentiableAt_of_re_pos ((7 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h2 := (Gamma_differentiableAt_of_re_pos ((5 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h3 := (Complex.differentiable_one_div_Gamma ((7 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  have h4 := (Complex.differentiable_one_div_Gamma ((5 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  convert ((h1.mul h2).mul (h3.mul h4)) using 1
  ext z
  simp only [gammaMultiplier, Function.comp_def, div_eq_mul_inv, mul_inv_rev, Pi.mul_apply]
  ring

theorem kernelMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (fun t => mellin V (-t) * gammaMultiplier t) s := by
  exact ((compact_source_mellin_differentiable V a b ha hsupp hV (-s)).comp s
    differentiableAt_id.neg).mul (gammaMultiplier_differentiableAt s hs)

end CubicReflectionKernel

open scoped BigOperators Classical

namespace DescentWeightedCauchy

theorem weighted_cauchy_sq {ι : Type*} (s : Finset ι)
    (w U V : ι → ℂ) :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ^ 2 ≤
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  have hnorm : ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      ∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖ := by
    simpa only [norm_mul, norm_star] using
      norm_sum_le s (fun i => w i * U i * star (V i))
  calc
    _ ≤ (∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖) ^ 2 :=
      sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => by positivity)) |>.mpr hnorm
    _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i _ => by positivity) (fun i _ => by positivity)
      (fun i _ => by ring_nf; exact le_rfl)

theorem weighted_cauchy {ι : Type*} (s : Finset ι)
    (w U V : ι → ℂ) :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  have h1 : 0 ≤ ∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have h2 : 0 ≤ ∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hs := weighted_cauchy_sq s w U V
  have he1 := Real.sq_sqrt h1
  have he2 := Real.sq_sqrt h2
  have hp : (Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2)) ^ 2 =
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by rw [mul_pow, he1, he2]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hp ▸ hs)

theorem weighted_energy_pushforward {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι → κ) (w : ι → ℂ)
    (P : κ → ℂ) (B : κ → ℝ)
    (hmap : ∀ i ∈ s, f i ∈ t)
    (hfib : ∀ y ∈ t, (∑ i ∈ s with f i = y, ‖w i‖) ≤ B y) :
    (∑ i ∈ s, ‖w i‖ * ‖P (f i)‖ ^ 2) ≤
      ∑ y ∈ t, B y * ‖P y‖ ^ 2 := by
  calc
    _ = ∑ y ∈ t, ∑ i ∈ s with f i = y, ‖w i‖ * ‖P (f i)‖ ^ 2 := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hmap _
    _ = ∑ y ∈ t, (∑ i ∈ s with f i = y, ‖w i‖) * ‖P y‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ _ := Finset.sum_le_sum (fun y hy =>
      mul_le_mul_of_nonneg_right (hfib y hy) (sq_nonneg _))

theorem bounded_energy_pushforward {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (f : ι → κ) (w : ι → ℂ)
    (P : κ → ℂ) (C : ℝ)
    (hmap : ∀ i ∈ s, f i ∈ t) (hw : ∀ i ∈ s, ‖w i‖ ≤ C) :
    (∑ i ∈ s, ‖w i‖ * ‖P (f i)‖ ^ 2) ≤
      ∑ y ∈ t, C * (s.filter (fun i => f i = y)).card * ‖P y‖ ^ 2 := by
  apply weighted_energy_pushforward s t f w P _ hmap
  intro y hy
  calc
    _ ≤ ∑ i ∈ s with f i = y, C := Finset.sum_le_sum
      (fun i hi => hw i (Finset.mem_filter.mp hi).1)
    _ = _ := by simp [mul_comm]

abbrev O := ActualEisensteinCubic.O

def firstRowMap (E : Ideal O) (x : Ideal O × Ideal O) : Ideal O :=
  x.2 * x.1 ^ 2 * E

theorem firstRowMap_fst_dvd (E : Ideal O) (x : Ideal O × Ideal O) :
    x.1 ∣ firstRowMap E x := by
  refine ⟨x.2 * x.1 * E, ?_⟩
  simp only [firstRowMap]
  ring

theorem firstRowMap_fst_injective_on_fiber
    (s : Finset (Ideal O × Ideal O)) (E Y : Ideal O) (hY : Y ≠ ⊥) :
    Set.InjOn (Prod.fst : Ideal O × Ideal O → Ideal O)
      {x | x ∈ s ∧ firstRowMap E x = Y} := by
  intro x hx z hz hfst
  have hx' := hx.2
  have hz' := hz.2
  have hfac : x.1 ^ 2 * E ≠ 0 := by
    intro he
    apply hY
    rw [← hx']
    simp [firstRowMap, mul_assoc, he]
  apply Prod.ext hfst
  apply mul_right_cancel₀ hfac
  calc
    x.2 * (x.1 ^ 2 * E) = Y := by simpa [firstRowMap, mul_assoc] using hx'
    _ = z.2 * (x.1 ^ 2 * E) := by simpa [firstRowMap, mul_assoc, hfst] using hz'.symm

theorem firstRowMap_fiber_card_le
    (s : Finset (Ideal O × Ideal O)) (E Y : Ideal O) (hY : Y ≠ ⊥) :
    (s.filter (fun x => firstRowMap E x = Y)).card ≤
      (IdealMobiusDivisorSum.idealDivisors Y).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    change x.1 ∈ IdealMobiusDivisorSum.idealDivisors Y
    rw [IdealMobiusDivisorSum.mem_idealDivisors hY]
    rw [← (Finset.mem_filter.mp hx).2]
    exact firstRowMap_fst_dvd E x
  · intro x hx z hz he
    exact firstRowMap_fst_injective_on_fiber s E Y hY
      (Finset.mem_filter.mp hx) (Finset.mem_filter.mp hz) he

theorem first_energy_pushforward
    (s : Finset (Ideal O × Ideal O)) (t : Finset (Ideal O))
    (E : Ideal O) (w : Ideal O × Ideal O → ℂ) (P : Ideal O → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hmap : ∀ x ∈ s, firstRowMap E x ∈ t)
    (ht : ∀ Y ∈ t, Y ≠ ⊥) (hw : ∀ x ∈ s, ‖w x‖ ≤ C) :
    (∑ x ∈ s, ‖w x‖ * ‖P (firstRowMap E x)‖ ^ 2) ≤
      ∑ Y ∈ t, C * (IdealMobiusDivisorSum.idealDivisors Y).card * ‖P Y‖ ^ 2 := by
  apply (bounded_energy_pushforward s t (firstRowMap E) w P C hmap hw).trans
  apply Finset.sum_le_sum
  intro Y hY
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast firstRowMap_fiber_card_le s E Y (ht Y hY)) hC)
    (sq_nonneg _)

def firstElementRowMap (e : O) (x : Ideal O × O) : O :=
  x.2 * ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e

theorem firstElementRowMap_label_dvd (e : O) (x : Ideal O × O) :
    x.1 ∣ Ideal.span {firstElementRowMap e x} := by
  rw [← ConcretePrimeRowBridge.span_idealGenerator x.1]
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
  refine ⟨x.2 * ConcretePrimeRowBridge.idealGenerator x.1 * e, ?_⟩
  simp only [firstElementRowMap]
  ring

theorem firstElementRowMap_fiber_card_le
    (s : Finset (Ideal O × O)) (e y : O) (hy : y ≠ 0) :
    (s.filter (fun x => firstElementRowMap e x = y)).card ≤
      (IdealMobiusDivisorSum.idealDivisors (Ideal.span {y})).card := by
  have hyI : (Ideal.span {y} : Ideal O) ≠ ⊥ := by
    intro h
    have hm : y ∈ (Ideal.span {y} : Ideal O) := Ideal.subset_span (by simp)
    rw [h] at hm
    exact hy hm
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    change x.1 ∈ IdealMobiusDivisorSum.idealDivisors (Ideal.span {y})
    rw [IdealMobiusDivisorSum.mem_idealDivisors hyI,
      ← (Finset.mem_filter.mp hx).2]
    exact firstElementRowMap_label_dvd e x
  · intro x hx z hz hfst
    have hx' := (Finset.mem_filter.mp hx).2
    have hz' := (Finset.mem_filter.mp hz).2
    have hfac : ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e ≠ 0 := by
      intro he
      apply hy
      rw [← hx']
      simp [firstElementRowMap, mul_assoc, he]
    apply Prod.ext hfst
    apply mul_right_cancel₀ hfac
    calc
      x.2 * (ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e) = y := by
        simpa [firstElementRowMap, mul_assoc] using hx'
      _ = z.2 * (ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e) := by
        simpa [firstElementRowMap, mul_assoc, hfst] using hz'.symm

theorem first_element_energy_pushforward
    (s : Finset (Ideal O × O)) (t : Finset O)
    (e : O) (w : Ideal O × O → ℂ) (P : O → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hmap : ∀ x ∈ s, firstElementRowMap e x ∈ t)
    (ht : ∀ y ∈ t, y ≠ 0) (hw : ∀ x ∈ s, ‖w x‖ ≤ C) :
    (∑ x ∈ s, ‖w x‖ * ‖P (firstElementRowMap e x)‖ ^ 2) ≤
      ∑ y ∈ t, C * (IdealMobiusDivisorSum.idealDivisors (Ideal.span {y})).card *
        ‖P y‖ ^ 2 := by
  apply (bounded_energy_pushforward s t (firstElementRowMap e) w P C hmap hw).trans
  apply Finset.sum_le_sum
  intro y hyt
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (by exact_mod_cast firstElementRowMap_fiber_card_le s e y (ht y hyt)) hC)
    (sq_nonneg _)

end DescentWeightedCauchy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace SquarefreeDivisorBound
open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum

abbrev O := ActualEisensteinCubic.O

theorem squarefree_divisor_card_le (I : Ideal O) (hI : I ≠ ⊥) :
    ((idealDivisors I).filter Squarefree).card ≤ 2 ^ (primeSupport I).card := by
  rw [squarefree_divisors_eq_image I hI]
  exact Finset.card_image_le.trans_eq (Finset.card_powerset _)

theorem prime_support_subsets_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal O, I ≠ ⊥ →
      (2 : ℝ) ^ (primeSupport I).card ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  let small : Finset (Ideal O) :=
    (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset
  refine ⟨(2 : ℝ) ^ small.card, by positivity, ?_⟩
  intro I hI
  let S := primeSupport I
  let A := S ∩ small
  let B := S \ small
  have hBS : B ⊆ primeSupport I := Finset.sdiff_subset
  have hlarge (P : Ideal O) (hP : P ∈ B) : (2 : ℝ) ≤ (Ideal.absNorm P : ℝ) ^ ε := by
    apply hN
    have hn : P ∉ small := (Finset.mem_sdiff.mp hP).2
    have hgt : N < Ideal.absNorm P := by
      apply Nat.lt_of_not_ge
      intro hp
      exact hn (by simpa [small] using hp)
    exact hgt.le
  have hpowB : (2 : ℝ) ^ B.card ≤ (Ideal.absNorm (∏ P ∈ B, P) : ℝ) ^ ε := by
    calc
      _ = ∏ P ∈ B, (2 : ℝ) := by simp
      _ ≤ ∏ P ∈ B, (Ideal.absNorm P : ℝ) ^ ε :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) hlarge
      _ = (∏ P ∈ B, (Ideal.absNorm P : ℝ)) ^ ε :=
        (Real.finsetProd_rpow B (fun P => (Ideal.absNorm P : ℝ))
          (fun _ _ => by positivity) ε)
      _ = _ := by simp only [map_prod, Nat.cast_prod]
  have hNI : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hnorm : Ideal.absNorm (∏ P ∈ B, P) ≤ Ideal.absNorm I :=
    Nat.le_of_dvd hNI (map_dvd Ideal.absNorm (support_product_dvd hI hBS))
  have hpowBI : (2 : ℝ) ^ B.card ≤ (Ideal.absNorm I : ℝ) ^ ε :=
    hpowB.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnorm) hε.le)
  have hAc : A.card ≤ small.card := Finset.card_le_card Finset.inter_subset_right
  have hcard : S.card = A.card + B.card := by
    simp [A, B]
  change (2 : ℝ) ^ S.card ≤ _
  rw [hcard, pow_add]
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hAc) hpowBI
    (by positivity) (by positivity)

theorem squarefree_divisor_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal O, I ≠ ⊥ →
      (((idealDivisors I).filter Squarefree).card : ℝ) ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := prime_support_subsets_bound ε hε
  refine ⟨C, hC, fun I hI => ?_⟩
  have hc : (((idealDivisors I).filter Squarefree).card : ℝ) ≤
      (2 : ℝ) ^ (primeSupport I).card := by
    exact_mod_cast squarefree_divisor_card_le I hI
  exact hc.trans (h I hI)

open DescentWeightedCauchy

theorem first_element_squarefree_fiber
    (s : Finset (Ideal O × O)) (hs : ∀ x ∈ s, Squarefree x.1)
    (e y : O) (hy : y ≠ 0) :
    (s.filter (fun x => firstElementRowMap e x = y)).card ≤
      ((idealDivisors (Ideal.span {y})).filter Squarefree).card := by
  have hyI : (Ideal.span {y} : Ideal O) ≠ ⊥ := by
    intro h
    have hm : y ∈ (Ideal.span {y} : Ideal O) := Ideal.subset_span (by simp)
    rw [h] at hm
    exact hy hm
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    change x.1 ∈ (idealDivisors (Ideal.span {y})).filter Squarefree
    have hx' := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, hs x hx'.1⟩
    rw [mem_idealDivisors hyI, ← hx'.2]
    exact firstElementRowMap_label_dvd e x
  · intro x hx z hz hfst
    have hx' := (Finset.mem_filter.mp hx).2
    have hz' := (Finset.mem_filter.mp hz).2
    have hfac : ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e ≠ 0 := by
      intro he
      apply hy
      rw [← hx']
      simp [firstElementRowMap, mul_assoc, he]
    apply Prod.ext hfst
    apply mul_right_cancel₀ hfac
    calc
      x.2 * (ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e) = y := by
        simpa [firstElementRowMap, mul_assoc] using hx'
      _ = z.2 * (ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e) := by
        simpa [firstElementRowMap, mul_assoc, hfst] using hz'.symm

theorem first_element_fiber_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal O × O)),
      (∀ x ∈ s, Squarefree x.1) → ∀ e y : O, y ≠ 0 →
      ((s.filter (fun x => firstElementRowMap e x = y)).card : ℝ) ≤
        C * (Ideal.absNorm (Ideal.span {y}) : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := squarefree_divisor_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro s hs e y hy
  have hyI : (Ideal.span {y} : Ideal O) ≠ ⊥ := by
    intro he
    have hm : y ∈ (Ideal.span {y} : Ideal O) := Ideal.subset_span (by simp)
    rw [he] at hm
    exact hy hm
  have hc : ((s.filter (fun x => firstElementRowMap e x = y)).card : ℝ) ≤
      (((idealDivisors (Ideal.span {y})).filter Squarefree).card : ℝ) := by
    exact_mod_cast first_element_squarefree_fiber s hs e y hy
  exact hc.trans (h _ hyI)

theorem first_element_energy_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal O × O)) (t : Finset O)
      (e : O) (w : Ideal O × O → ℂ) (P : O → ℂ) (B Y : ℝ),
      0 ≤ B → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, firstElementRowMap e x ∈ t) → (∀ y ∈ t, y ≠ 0) →
      (∀ y ∈ t, (Ideal.absNorm (Ideal.span {y}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (firstElementRowMap e x)‖ ^ 2) ≤
        B * C * Y ^ ε * ∑ y ∈ t, ‖P y‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := first_element_fiber_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro s t e w P B Y hB hY hs hmap ht hnorm hw
  have hpush := bounded_energy_pushforward s t (firstElementRowMap e) w P B hmap hw
  apply hpush.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hcard := (hc s hs e y (ht y hy)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hnorm y hy) hε.le) hC.le)
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard hB) (sq_nonneg ‖P y‖)
  simpa only [mul_assoc] using hterm

end SquarefreeDivisorBound

namespace VerticalContourShift
open MeasureTheory Filter Set
open scoped Topology

theorem horizontal_integral_tendsto_zero
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    Tendsto (fun t : ℝ => ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hz : Tendsto (fun t : ℝ => C / (1 + t ^ 2) * |b - a|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop ht).mul_const |b - a|
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro t
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  exact hbound σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ)) t

theorem integral_eq_of_strip_decay
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * Complex.I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * Complex.I)))
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + t * Complex.I) := by
  let H (t : ℝ) : ℂ := ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I)
  let V (σ t : ℝ) : ℂ := ∫ u : ℝ in -t..t, f ((σ : ℂ) + u * Complex.I)
  have htop : Tendsto H atTop (𝓝 0) := horizontal_integral_tendsto_zero f a b C hab hbound
  have hbottom : Tendsto (fun t : ℝ => H (-t)) atTop (𝓝 0) := by
    let g (z : ℂ) := f (star z)
    have hg : ∀ σ ∈ Icc a b, ∀ t : ℝ,
        ‖g ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
      intro σ hσ t
      simpa [g] using hbound σ hσ (-t)
    convert horizontal_integral_tendsto_zero g a b C hab hg using 1 ;
      simp [g, H]
  have hVa : Tendsto (V a) atTop
      (𝓝 (∫ t : ℝ, f ((a : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (V b) atTop
      (𝓝 (∫ t : ℝ, f ((b : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect (t : ℝ) : H (-t) - H t + Complex.I * V b t - Complex.I * V a t = 0 := by
    have hd : DifferentiableOn ℂ f
        (uIcc (((a : ℂ) - t * Complex.I).re) (((b : ℂ) + t * Complex.I).re) ×ℂ
         uIcc (((a : ℂ) - t * Complex.I).im) (((b : ℂ) + t * Complex.I).im)) := by
      intro z hz
      apply (hdiff z ?_ ?_).differentiableWithinAt
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.1
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.2
    have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - t * Complex.I) ((b : ℂ) + t * Complex.I) hd
    simpa [H, V, smul_eq_mul] using hr
  have hlim : Tendsto
      (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
      atTop (𝓝 (0 - 0 + Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)))) :=
    ((hbottom.sub htop).add (tendsto_const_nhds.mul hVb)).sub
      (tendsto_const_nhds.mul hVa)
  have heq : Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) = 0 := by
    have hzero : Tendsto (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
        atTop (𝓝 0) := by
      simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    simpa using tendsto_nhds_unique hlim hzero
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp heq)).symm

end VerticalContourShift

open scoped BigOperators Classical
namespace FirstPassCubeLabels
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic

def bit (b : Bool) : ℕ := if b then 1 else 0

def conductorExponent (parityBit ε₁ ε₂ : Bool) : ZMod 6 :=
  (bit ε₁ : ZMod 6) - (bit ε₂ : ZMod 6) + 3 * (bit parityBit : ZMod 6)

def crtExponent (side parityBit ε₁ ε₂ : Bool) : ℕ :=
  if conductorExponent parityBit ε₁ ε₂ = 0 then 0 else
    ((1 : ZMod 6) + if side then -conductorExponent parityBit ε₁ ε₂
      else conductorExponent parityBit ε₁ ε₂).val

def dilationExponent (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if parityBit then bit ε₁ + bit ε₂ else 0

def retained (parityBit ε₁ ε₂ : Bool) : Bool := parityBit || (ε₁ && ε₂)

theorem exponent_table (side parityBit ε₁ ε₂ : Bool) :
    (4 * bit (if side then ε₂ else ε₁) + crtExponent side parityBit ε₁ ε₂ +
      dilationExponent parityBit ε₁ ε₂) % 6 = if retained parityBit ε₁ ε₂ then 4 else 0 := by
  cases side <;> cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide

section Rows
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem row_pow (a : O) (m : ℕ) :
    finiteSquarefreeRow P hg S (a ^ m) = finiteSquarefreeRow P hg S a ^ m := by
  simp only [finiteSquarefreeRow, map_pow, Finset.prod_pow]

theorem row_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    finiteSquarefreeRow P hg S (∏ j ∈ B, a j) =
      ∏ j ∈ B, finiteSquarefreeRow P hg S (a j) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [finiteSquarefreeRow]
  | @insert j B hj ih =>
    simp only [Finset.prod_insert hj, finiteSquarefreeRow_mul, ih]

theorem row_sixth (a : O) :
    finiteSquarefreeRow P hg S a ^ 6 = rowCoprimeMask P S a := by
  rw [← row_pow, finiteSquarefreeRow_sixth_power]
  rfl

include hg

theorem mask_mul (a b : O) :
    rowCoprimeMask P S (a * b) = rowCoprimeMask P S a * rowCoprimeMask P S b := by
  simp only [← row_sixth P hg S, finiteSquarefreeRow_mul, mul_pow]

theorem mask_pow (a : O) (m : ℕ) :
    rowCoprimeMask P S (a ^ m) = rowCoprimeMask P S a ^ m := by
  rw [← row_sixth P hg S, row_pow, ← row_sixth P hg S]
  simp only [← pow_mul, Nat.mul_comm]

theorem mask_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    rowCoprimeMask P S (∏ j ∈ B, a j) = ∏ j ∈ B, rowCoprimeMask P S (a j) := by
  rw [← row_sixth P hg S, row_prod, ← Finset.prod_pow]
  simp only [row_sixth]

theorem row_zero_of_mask_zero (a : O) (h : rowCoprimeMask P S a = 0) :
    finiteSquarefreeRow P hg S a = 0 := by
  have hq := row_sixth P hg S a
  rw [h] at hq
  exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hq

theorem row_power_mul_mask_power (a : O) (k m : ℕ) (hk : 0 < k) :
    finiteSquarefreeRow P hg S a ^ k * rowCoprimeMask P S a ^ m =
      finiteSquarefreeRow P hg S a ^ k := by
  by_cases h : ∃ i ∈ S, a ∈ P i
  · have hm : rowCoprimeMask P S a = 0 := by simp [rowCoprimeMask, h]
    rw [row_zero_of_mask_zero P hg S a hm]
    simp [Nat.ne_of_gt hk]
  · simp [rowCoprimeMask, h]

def localFactor (side parityBit ε₁ ε₂ : Bool) (a : O) : ℂ :=
  rowCoprimeMask P S a *
    finiteSquarefreeRow P hg S a ^ (4 * bit (if side then ε₂ else ε₁)) *
    finiteSquarefreeRow P hg S a ^ crtExponent side parityBit ε₁ ε₂ *
    finiteSquarefreeRow P hg S a ^ dilationExponent parityBit ε₁ ε₂

theorem localFactor_eq (side parityBit ε₁ ε₂ : Bool) (a : O) :
    localFactor P hg S side parityBit ε₁ ε₂ a =
      if retained parityBit ε₁ ε₂ then finiteSquarefreeRow P hg S a ^ 4
      else rowCoprimeMask P S a := by
  by_cases h : ∃ i ∈ S, a ∈ P i
  · have hm : rowCoprimeMask P S a = 0 := by simp [rowCoprimeMask, h]
    have hz := row_zero_of_mask_zero P hg S a hm
    simp [localFactor, hm, hz]
  · have hm : rowCoprimeMask P S a = 1 := by simp [rowCoprimeMask, h]
    have h6 : finiteSquarefreeRow P hg S a ^ 6 = 1 := (row_sixth P hg S a).trans hm
    simp only [localFactor, hm, one_mul, ← pow_add]
    rw [pow_eq_pow_mod _ h6, exponent_table]
    split <;> simp

end Rows

def parity (m : ℕ) : Bool := decide (m % 2 = 1)

def evenDouble (m : ℕ) (ε₁ ε₂ : Bool) : Bool := !parity m && ε₁ && ε₂

def b0Exponent (m : ℕ) (ε₁ ε₂ : Bool) : ℕ := m / 2 - bit (evenDouble m ε₁ ε₂)

theorem multiplicity_decomposition (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m) :
    2 * b0Exponent m ε₁ ε₂ + 2 * bit (evenDouble m ε₁ ε₂) + bit (parity m) = m := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp [b0Exponent, evenDouble, parity, bit, h] <;> omega

theorem b0Exponent_pos_of_not_retained (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m)
    (hret : retained (parity m) ε₁ ε₂ = false) : 0 < b0Exponent m ε₁ ε₂ := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp_all [b0Exponent, evenDouble, parity, retained, bit] <;> omega

section Reassembly
variable {ι κ : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem localFactor_eq_b0 (side ε₁ ε₂ : Bool) (a : O) (m : ℕ) (hm : 0 < m) :
    localFactor P hg S side (parity m) ε₁ ε₂ a =
      (finiteSquarefreeRow P hg S (a ^ bit (retained (parity m) ε₁ ε₂))) ^ 4 *
        rowCoprimeMask P S (a ^ b0Exponent m ε₁ ε₂) := by
  rw [localFactor_eq, row_pow, mask_pow P hg S]
  cases hr : retained (parity m) ε₁ ε₂
  · have hpos := b0Exponent_pos_of_not_retained m ε₁ ε₂ hm hr
    simp only [Bool.false_eq_true, ↓reduceIte, bit, Bool.false_eq_true, pow_zero, one_pow,
      one_mul]
    unfold rowCoprimeMask
    split <;> simp [Nat.ne_of_gt hpos]
  · simp only [↓reduceIte, bit, pow_one]
    exact (row_power_mul_mask_power P hg S a 4 _ (by decide)).symm

def primeProduct (p : κ → O) (B : Finset κ) (v : κ → ℕ) : O := ∏ j ∈ B, p j ^ v j

def cubeRadical (p : κ → O) (B : Finset κ) : O := ∏ j ∈ B, p j

def aLabel (p : κ → O) (B : Finset κ) (ε : κ → Bool) : O :=
  primeProduct p B (fun j => bit (ε j))

def crtLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (side : Bool) : O :=
  primeProduct p B (fun j => crtExponent side (parity (v j)) (ε₁ j) (ε₂ j))

def dilationLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => dilationExponent (parity (v j)) (ε₁ j) (ε₂ j))

def jLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => bit (retained (parity (v j)) (ε₁ j) (ε₂ j)))

def j2Label (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => bit (evenDouble (v j) (ε₁ j) (ε₂ j)))

def squarefreeLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ) : O :=
  primeProduct p B (fun j => bit (parity (v j)))

def b0Label (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => b0Exponent (v j) (ε₁ j) (ε₂ j))

theorem first_pass_label_identity (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j) (side : Bool) :
    rowCoprimeMask P S (cubeRadical p B) *
      finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side) *
      finiteSquarefreeRow P hg S (dilationLabel p B v ε₁ ε₂) =
    finiteSquarefreeRow P hg S (jLabel p B v ε₁ ε₂) ^ 4 *
      rowCoprimeMask P S (b0Label p B v ε₁ ε₂) := by
  classical
  simp only [cubeRadical, aLabel, crtLabel, dilationLabel, jLabel, b0Label,
    primeProduct, mask_prod P hg S, row_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [row_pow, row_pow, row_pow]
  convert localFactor_eq_b0 P hg S side (ε₁ j) (ε₂ j) (p j) (v j) (hv j hj) using 1
  cases side <;> simp only [localFactor, Bool.false_eq_true, ↓reduceIte,
    ← _root_.pow_mul, _root_.Nat.mul_comm]

theorem cube_product_decomposition (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j) :
    primeProduct p B v = b0Label p B v ε₁ ε₂ ^ 2 * j2Label p B v ε₁ ε₂ ^ 2 *
      squarefreeLabel p B v := by
  simp only [b0Label, j2Label, squarefreeLabel, primeProduct, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← pow_mul, ← pow_add]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  have h := multiplicity_decomposition (v j) (ε₁ j) (ε₂ j) (hv j hj)
  omega

theorem jLabel_eq_squarefree_mul_j2 (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) :
    jLabel p B v ε₁ ε₂ = squarefreeLabel p B v * j2Label p B v ε₁ ε₂ := by
  simp only [jLabel, squarefreeLabel, j2Label, primeProduct, ← Finset.prod_mul_distrib,
    ← pow_add]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  cases hp : parity (v j) <;> cases ε₁ j <;> cases ε₂ j <;>
    simp [bit, retained, evenDouble, hp]

include hg in

theorem radical_mask_absorbs (p : κ → O) (B : Finset κ) (v : κ → ℕ) :
    rowCoprimeMask P S (cubeRadical p B) * rowCoprimeMask P S (primeProduct p B v) =
      rowCoprimeMask P S (cubeRadical p B) := by
  simp only [cubeRadical, primeProduct, mask_prod P hg S, mask_pow P hg S,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  unfold rowCoprimeMask
  split <;> simp

theorem masked_dual_dilation (p : κ → O) (B : Finset κ) (v : κ → ℕ) (z : O) (c : ℂ) :
    rowCoprimeMask P S (cubeRadical p B) * c * star (finiteSquarefreeRow P hg S z) =
      (rowCoprimeMask P S (cubeRadical p B) * c *
        finiteSquarefreeRow P hg S (primeProduct p B v)) *
      star (finiteSquarefreeRow P hg S (z * primeProduct p B v)) := by
  rw [finiteSquarefreeRow_mul, star_mul]
  calc
    _ = (rowCoprimeMask P S (cubeRadical p B) *
        rowCoprimeMask P S (primeProduct p B v)) * c *
        star (finiteSquarefreeRow P hg S z) := by rw [radical_mask_absorbs P hg S]
    _ = _ := by rw [← finiteSquarefreeRow_self_pair P hg S (primeProduct p B v)]; ring

theorem first_pass_after_dual_dilation
    (p : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (z : O) :
    (rowCoprimeMask P S (cubeRadical p B) *
      finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
      star (finiteSquarefreeRow P hg S z) =
    (finiteSquarefreeRow P hg S (jLabel p B v ε₁ ε₂) ^ 4 *
      rowCoprimeMask P S (b0Label p B v ε₁ ε₂)) *
      star (finiteSquarefreeRow P hg S (z * dilationLabel p B v ε₁ ε₂)) := by
  have hd := masked_dual_dilation P hg S p B
    (fun j => dilationExponent (parity (v j)) (ε₁ j) (ε₂ j)) z
    (finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side))
  change _ = (_ * finiteSquarefreeRow P hg S (dilationLabel p B v ε₁ ε₂)) * _ at hd
  simp only [← mul_assoc] at hd
  rw [first_pass_label_identity P hg S p B v ε₁ ε₂ hv side] at hd
  exact hd

theorem cube_pair_product_decomposition
    (p : κ → O) (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v₁ j + v₂ j) :
    primeProduct p B v₁ * primeProduct p B v₂ =
      b0Label p B (fun j => v₁ j + v₂ j) ε₁ ε₂ ^ 2 *
      j2Label p B (fun j => v₁ j + v₂ j) ε₁ ε₂ ^ 2 *
      squarefreeLabel p B (fun j => v₁ j + v₂ j) := by
  rw [← cube_product_decomposition p B (fun j => v₁ j + v₂ j) ε₁ ε₂ hv]
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

end Reassembly

theorem mobius_column_after_dual_dilation
    {ι κ : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (columns : Finset ι) (C : Finset ι → ℂ)
    (p : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (z : O) :
    (∑ S ∈ columns.powerset, FirstCauchyArithmetic.supportMobius P S * C S *
      ((rowCoprimeMask P S (cubeRadical p B) *
        finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
        finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
        star (finiteSquarefreeRow P hg S z))) =
    FirstCauchyArithmetic.supportConjugateSum P hg columns
      (fun S => C S * finiteSquarefreeRow P hg S (jLabel p B v ε₁ ε₂) ^ 4 *
        rowCoprimeMask P S (b0Label p B v ε₁ ε₂))
      (z * dilationLabel p B v ε₁ ε₂) := by
  unfold FirstCauchyArithmetic.supportConjugateSum
  apply Finset.sum_congr rfl
  intro S hS
  rw [first_pass_after_dual_dilation P hg S p B v ε₁ ε₂ hv side z]
  ring

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open FiniteGaussPhase MixedCrossSeparation ActualEisensteinCoordinates QuadraticGaussRay
open RayFourExpansion

def quadraticSymbol {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) : ℂ :=
  quadraticRow (fun i => Ideal.span {p i}) hg A (∏ i ∈ B, p i)

theorem quadraticSymbol_eq_cross_product {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) :
    quadraticSymbol p hg A B = ∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 3 := by
  simp only [quadraticSymbol, quadraticRow, finiteSquarefreeRow, map_prod,
    ← Finset.prod_pow, crossSymbol]

theorem quadraticSymbol_mul_reverse {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) :
    quadraticSymbol p hg A B * quadraticSymbol p hg B A = quadraticCrossPhase p hg A B := by
  rw [quadraticSymbol_eq_cross_product, quadraticSymbol_eq_cross_product]
  rw [Finset.prod_comm (s := B) (t := A)]
  simp only [quadraticCrossPhase, Finset.prod_mul_distrib]

theorem quadraticSymbol_eq_zero_of_not_disjoint {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (h : ¬ Disjoint A B) :
    quadraticSymbol p hg A B = 0 := by
  obtain ⟨i, hiA, hiB⟩ := Finset.not_disjoint_iff.mp h
  rw [quadraticSymbol_eq_cross_product]
  apply Finset.prod_eq_zero hiA
  apply Finset.prod_eq_zero hiB
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (p i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simp only [crossSymbol, hz, MulChar.map_zero, zero_pow (by decide : 3 ≠ 0)]

theorem quadraticSymbol_sq_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (hd : Disjoint A B) :
    quadraticSymbol p hg A B ^ 2 = 1 := by
  rw [quadraticSymbol_eq_cross_product, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro k hk
  have hik : i ≠ k := by
    intro h
    subst k
    exact Finset.disjoint_left.mp hd hi hk
  rw [← pow_mul]
  simpa only [crossSymbol, show 3 * 2 = 6 by decide, map_pow,
    ite_eq_right (prime_generator_not_mem_other p hcop i k hik)] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)

theorem quadraticSymbol_reciprocity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A B : Finset ι) :
    quadraticSymbol p hg A B =
      quadraticRayPair (residue (∏ i ∈ A, p i)) (residue (∏ i ∈ B, p i)) *
        quadraticSymbol p hg B A := by
  by_cases hd : Disjoint A B
  · have hprod := quadraticSymbol_mul_reverse p hg A B
    rw [quadraticCrossPhase_eq_rayPair p hp hcop hg hc A B hd] at hprod
    have hsq := quadraticSymbol_sq_eq_one p hcop hg B A hd.symm
    calc
      _ = quadraticSymbol p hg A B * (quadraticSymbol p hg B A) ^ 2 := by rw [hsq, mul_one]
      _ = _ := by rw [pow_two, ← mul_assoc, hprod]
  · rw [quadraticSymbol_eq_zero_of_not_disjoint p hg A B hd,
      quadraticSymbol_eq_zero_of_not_disjoint p hg B A (fun h => hd h.symm), mul_zero]

theorem quadraticSymbol_reciprocity_characters {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A B : Finset ι) :
    quadraticSymbol p hg A B =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayCharacter χ (∏ i ∈ A, p i) *
          rayCharacter η (∏ i ∈ B, p i) * quadraticSymbol p hg B A := by
  rw [quadraticSymbol_reciprocity p hp hcop hg hc]
  have hr := quadraticRayPair_character_expansion (∏ i ∈ A, p i) (∏ i ∈ B, p i)
  rw [rayMask_prime_product p hc A, rayMask_prime_product p hc B, one_mul, one_mul] at hr
  rw [hr]
  simp only [Finset.sum_mul]

end QuadraticInitialBound

end

end OAI

end

