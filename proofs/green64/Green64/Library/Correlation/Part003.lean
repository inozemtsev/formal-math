module

public import Green64.Library.Weights.Part021
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Green64.Library.Analysis.Estimates.Part004
public import Green64.Library.Weights.Part011
public import Green64.Library.Analysis.Estimates.Part002
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Correlation / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceActualPhysicalProduct -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1150000

/-- The ORIGINAL source physical angular-time kernel has compact
support in logarithmic u, not merely a uniform time bound. -/
theorem source_actual_physical_kernel_support434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (h : ℝ) (P : ℝ → ℂ) (u t : ℝ)
    (hu : u ∉ Set.Icc (-B) B) :
    sourceActualPhysicalTimeKernel434 chi kappa h P u t = 0 := by
  have hz : chi u = 0 := by
    by_contra hn
    exact hu (hchi (subset_closure hn))
  simp only [sourceActualPhysicalTimeKernel434, sourceCompactCollarSymbol434,
    hz, zero_mul]

/-- Full two-dimensional absolute Bochner integrability of actual
physical u×t source kernel; derives from compact support and j≥2. -/
theorem source_actual_physical_product_integrable434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    Integrable (fun p : ℝ × ℝ =>
      sourceActualPhysicalTimeKernel434 chi kappa h P p.1 p.2)
        (volume.prod volume) := by
  obtain ⟨C,hC,hmajor⟩ :=
    source_actual_physical_time_kernel_majorant434 chi kappa B hB hchi j
  let S : Set ℝ := Set.Icc (-B) B
  let f : ℝ → ℝ := S.indicator (fun _ => C*M)
  let g : ℝ → ℝ := fun t => ((1+h*|t|)^j)⁻¹
  have hf : Integrable f := by
    dsimp [f]
    exact (integrableOn_const (s:=S) (by
      dsimp [S]
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hg : Integrable g :=
    source_real_time_weight_integrable434 h hh j hj
  have hprod : Integrable (fun p : ℝ × ℝ => f p.1 * g p.2)
      (volume.prod volume) := hf.mul_prod hg
  have hcont := source_actual_physical_kernel_joint_continuous434
    chi kappa h P hP
  apply Integrable.mono' hprod hcont.aestronglyMeasurable
  filter_upwards with p
  by_cases hu : p.1 ∈ S
  · have hmajorPoint := hmajor h hh P M hM hBound p.1 p.2
    simpa only [f,g,S,Set.indicator_of_mem hu] using hmajorPoint
  · have hzero := source_actual_physical_kernel_support434
      chi kappa B hchi h P p.1 p.2 hu
    simp only [f, g, Set.indicator_of_notMem hu, zero_mul]
    simp [hzero]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualPhysicalQL1 -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 750000

/-- The actual physical compact log-center collar Q is in L¹ on R.
This is derived from the true full u×t Bochner Fubini, no assumptions on Q. -/
theorem source_actual_physical_Q_integrable434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    Integrable (sourceActualPhysicalQ434 chi kappa h P) := by
  have hprod := source_actual_physical_product_integrable434
    chi kappa B hB hchi j hj h hh P hP M hM hBound
  change Integrable (fun u : ℝ =>
    ∫ t : ℝ, sourceActualPhysicalTimeKernel434 chi kappa h P u t)
  exact hprod.integral_prod_left

/-- No artificial tail in physical logarithmic center:
Q(u) vanishes outside actual supp chi ⊆ [-B,B]. -/
theorem source_actual_physical_Q_support434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (h : ℝ) (P : ℝ → ℂ) (u : ℝ)
    (hu : u ∉ Set.Icc (-B) B) :
    sourceActualPhysicalQ434 chi kappa h P u = 0 := by
  have hzero : (fun t : ℝ =>
      sourceActualPhysicalTimeKernel434 chi kappa h P u t) =
      (fun _ => (0:ℂ)) := by
    funext t
    exact source_actual_physical_kernel_support434
      chi kappa B hchi h P u t hu
  simp only [sourceActualPhysicalQ434, hzero, integral_zero]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualPhysicalModulatedFubini -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 950000

/-- Actual Fourier-u modulation of the original complex physical collar;
source angular t and Fourier cycle s are intentionally separate. -/
noncomputable def sourceActualPhysicalModulatedKernel434
    (chi kappa : 𝓢(ℝ,ℂ)) (h : ℝ) (P : ℝ → ℂ) (s : ℝ)
    (p : ℝ × ℝ) : ℂ :=
  Complex.exp (((-2*Real.pi*(p.1*s):ℝ):ℂ)*Complex.I) *
    sourceActualPhysicalTimeKernel434 chi kappa h P p.1 p.2

/-- The exact source modulated kernel is joint continuous in u,t. -/
theorem source_actual_physical_modulated_continuous434
    (chi kappa : 𝓢(ℝ,ℂ)) (h : ℝ) (P : ℝ → ℂ)
    (hP : Continuous P) (s : ℝ) :
    Continuous (sourceActualPhysicalModulatedKernel434 chi kappa h P s) := by
  have hp : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (((-2*Real.pi*(p.1*s):ℝ):ℂ)*Complex.I)) := by
    fun_prop
  have hK := source_actual_physical_kernel_joint_continuous434
    chi kappa h P hP
  change Continuous (fun p : ℝ × ℝ =>
    Complex.exp (((-2*Real.pi*(p.1*s):ℝ):ℂ)*Complex.I) *
      sourceActualPhysicalTimeKernel434 chi kappa h P p.1 p.2)
  exact hp.mul hK
/-- True complex Bochner absolute integrability on R_u×R_t after the
original exp(-2πisu) cycle Fourier modulation. -/
theorem source_actual_physical_modulated_integrable434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M)
    (s : ℝ) :
    Integrable (sourceActualPhysicalModulatedKernel434 chi kappa h P s)
      (volume.prod volume) := by
  have hOrig : Integrable (fun p : ℝ × ℝ =>
      sourceActualPhysicalTimeKernel434 chi kappa h P p.1 p.2)
      (volume.prod volume) :=
    source_actual_physical_product_integrable434
      chi kappa B hB hchi j hj h hh P hP M hM hBound
  have hMeas : AEStronglyMeasurable
      (sourceActualPhysicalModulatedKernel434 chi kappa h P s)
      (volume.prod volume) :=
    (source_actual_physical_modulated_continuous434
      chi kappa h P hP s).aestronglyMeasurable
  apply Integrable.mono hOrig hMeas
  filter_upwards with p
  change ‖Complex.exp (((-2*Real.pi*(p.1*s):ℝ):ℂ)*Complex.I) *
      sourceActualPhysicalTimeKernel434 chi kappa h P p.1 p.2‖ ≤
    ‖sourceActualPhysicalTimeKernel434 chi kappa h P p.1 p.2‖
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]

/-- Untruncated, original source complex Fubini for Fourier(Q). -/
theorem source_actual_physical_modulated_fubini434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M)
    (s : ℝ) :
    (∫ u : ℝ, ∫ t : ℝ,
      sourceActualPhysicalModulatedKernel434 chi kappa h P s (u,t)) =
    (∫ t : ℝ, ∫ u : ℝ,
      sourceActualPhysicalModulatedKernel434 chi kappa h P s (u,t)) :=
  integral_integral_swap
    (source_actual_physical_modulated_integrable434 chi kappa B hB hchi
      j hj h hh P hP M hM hBound s)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualPhysicalInner -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1050000

/-- Identify the Fourier-u integration of the ORIGINAL physical u,t
kernel at each exact Mellin angular t with the pre-certified Fourier lift.
This is the only place the sign of exp(-iut) is rearranged. -/
theorem source_actual_physical_inner_equals_lift434
    (chi kappa : 𝓢(ℝ,ℂ)) (h s t : ℝ) (P : ℝ → ℂ) :
    (∫ u : ℝ,
      sourceActualPhysicalModulatedKernel434 chi kappa h P s (u,t)) =
      sourceActualCollarLift434 chi kappa h P (s,t) := by
  have hpoint (u : ℝ) :
      sourceActualPhysicalModulatedKernel434 chi kappa h P s (u,t) =
      (Complex.exp (((-2*Real.pi*(u*s):ℝ):ℂ)*Complex.I) *
       Complex.exp (((-(u*t):ℝ):ℂ)*Complex.I) *
       sourceCompactCollarSymbol434 chi kappa h t u) * P t := by
    simp only [sourceActualPhysicalModulatedKernel434,
      sourceActualPhysicalTimeKernel434]
    ring
  calc
    _ = ∫ u : ℝ,
        (Complex.exp (((-2*Real.pi*(u*s):ℝ):ℂ)*Complex.I) *
         Complex.exp (((-(u*t):ℝ):ℂ)*Complex.I) *
         sourceCompactCollarSymbol434 chi kappa h t u) * P t := by
      apply integral_congr_ae
      filter_upwards with u
      exact hpoint u
    _ = (∫ u : ℝ,
        Complex.exp (((-2*Real.pi*(u*s):ℝ):ℂ)*Complex.I) *
        Complex.exp (((-(u*t):ℝ):ℂ)*Complex.I) *
        sourceCompactCollarSymbol434 chi kappa h t u) * P t := by
      rw [integral_mul_const]
    _ = (𝓕 (sourceCompactCollarSymbol434 chi kappa h t))
          (s+t/(2*Real.pi)) * P t := by
      rw [source_original_collar_modulation_shift434 chi kappa h s t]
    _ = sourceActualCollarLift434 chi kappa h P (s,t) := by
      simp only [sourceActualCollarLift434]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualQFourierBridge -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1150000

/-- SOURCE-EXACT physical↔Fourier lift bridge:
the Fourier transform in the physical log-center u of the actual
full-angular-time collar Q_h(u) is IDENTICAL at each cycle frequency s
to the verified operator P(t)*Fourier_u(A_h,t)(s+t/(2π)).
No truncation, source-saving premise, or surrogate endpoint. -/
theorem source_actual_physical_Q_fourier_equals_lift434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M)
    (s : ℝ) :
    (𝓕 (sourceActualPhysicalQ434 chi kappa h P)) s =
      ∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t) := by
  rw [Real.fourier_eq']
  simp only [Real.inner_apply, smul_eq_mul]
  change (∫ u : ℝ,
      Complex.exp (((-2*Real.pi*(u*s):ℝ):ℂ)*Complex.I) *
        sourceActualPhysicalQ434 chi kappa h P u) = _
  calc
    _ = ∫ u : ℝ, ∫ t : ℝ,
        sourceActualPhysicalModulatedKernel434 chi kappa h P s (u,t) := by
      apply integral_congr_ae
      filter_upwards with u
      change Complex.exp (((-2*Real.pi*(u*s):ℝ):ℂ)*Complex.I) *
          sourceActualPhysicalQ434 chi kappa h P u =
        ∫ t : ℝ,
          Complex.exp (((-2*Real.pi*(u*s):ℝ):ℂ)*Complex.I) *
            sourceActualPhysicalTimeKernel434 chi kappa h P u t
      unfold sourceActualPhysicalQ434
      rw [integral_const_mul]
    _ = ∫ t : ℝ, ∫ u : ℝ,
        sourceActualPhysicalModulatedKernel434 chi kappa h P s (u,t) :=
      source_actual_physical_modulated_fubini434 chi kappa B hB hchi
        j hj h hh P hP M hM hBound s
    _ = ∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t) := by
      apply integral_congr_ae
      filter_upwards with t
      exact source_actual_physical_inner_equals_lift434
        chi kappa h s t P
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualPhysicalQBound -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1050000

/-- Actual physical collar is uniformly bounded at each compact log-center.
This proves L² existence, NOT a saving as h→0: the weight integral
may grow as 1/h and must not replace the Fourier-side Schur estimate. -/
theorem source_actual_physical_Q_bound434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ), 0 < h →
      ∀ (P : ℝ → ℂ) (hP : Continuous P)
        (M : ℝ), 0 ≤ M → (∀ t, ‖P t‖ ≤ M) →
      ∀ (u : ℝ), ‖sourceActualPhysicalQ434 chi kappa h P u‖ ≤
        (C*M) * (∫ t : ℝ, ((1+h*|t|)^j)⁻¹) := by
  obtain ⟨C,hC,hmajor⟩ :=
    source_actual_physical_time_kernel_majorant434 chi kappa B hB hchi j
  refine ⟨C,hC,?_⟩
  intro h hh P hP M hM hBound u
  have hTime := source_actual_physical_time_integrable434
    chi kappa B hB hchi j hj h hh P hP M hM hBound u
  have hWeight := (source_real_time_weight_integrable434 h hh j hj).const_mul (C*M)
  have hPoint (t : ℝ) :
      ‖sourceActualPhysicalTimeKernel434 chi kappa h P u t‖ ≤
        (C*M)*((1+h*|t|)^j)⁻¹ :=
    hmajor h hh P M hM hBound u t
  calc
    _ ≤ ∫ t : ℝ, ‖sourceActualPhysicalTimeKernel434 chi kappa h P u t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (C*M)*((1+h*|t|)^j)⁻¹ :=
      integral_mono hTime.norm hWeight hPoint
    _ = (C*M)*(∫ t : ℝ, ((1+h*|t|)^j)⁻¹) := by
      rw [integral_const_mul]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualPhysicalQL2 -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1250000

/-- The original physical Q_h belongs to genuine L² in its compact
logarithmic center variable, derived without using Fourier energy saving. -/
theorem source_actual_physical_Q_sq_integrable434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    Integrable (fun u : ℝ => ‖sourceActualPhysicalQ434 chi kappa h P u‖^2) := by
  obtain ⟨C,hC,hQBound⟩ :=
    source_actual_physical_Q_bound434 chi kappa B hB hchi j hj
  let S : Set ℝ := Set.Icc (-B) B
  let W : ℝ := ∫ t : ℝ, ((1+h*|t|)^j)⁻¹
  let K : ℝ := (C*M)*W
  have hW : 0 ≤ W := integral_nonneg
    (fun t => (source_collar_real_weight_le_one434 h t hh.le j).1)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hC.le hM) hW
  have hQBound' (u : ℝ) :
      ‖sourceActualPhysicalQ434 chi kappa h P u‖ ≤ K :=
    hQBound h hh P hP M hM hBound u
  have hi : Integrable (S.indicator (fun _ : ℝ => K^2)) :=
    (integrableOn_const (s:=S) (by
      dsimp [S]
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hMeas := (source_actual_physical_Q_integrable434
    chi kappa B hB hchi j hj h hh P hP M hM hBound).aestronglyMeasurable
  apply Integrable.mono' hi (hMeas.norm.pow 2)
  filter_upwards with u
  change |‖sourceActualPhysicalQ434 chi kappa h P u‖^2| ≤
    S.indicator (fun _ => K^2) u
  by_cases hu : u ∈ S
  · rw [Set.indicator_of_mem hu, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hQBound' u) 2
  · have hz := source_actual_physical_Q_support434
      chi kappa B hchi h P u hu
    simp only [Set.indicator_of_notMem hu, hz, norm_zero,
      zero_pow (by norm_num : (2:ℕ) ≠ 0), abs_zero, le_refl]

/-- Native Mathlib L² membership for the true original physical Q. -/
theorem source_actual_physical_Q_memLp434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    MemLp (sourceActualPhysicalQ434 chi kappa h P)
      2 (volume : Measure ℝ) := by
  have hL1 := source_actual_physical_Q_integrable434
    chi kappa B hB hchi j hj h hh P hP M hM hBound
  exact (memLp_two_iff_integrable_sq_norm
    hL1.aestronglyMeasurable).mpr
      (source_actual_physical_Q_sq_integrable434
        chi kappa B hB hchi j hj h hh P hP M hM hBound)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualQFourierL1 -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 750000

/-- As well as its full source L² bound, the original Fourier lift is
absolutely L¹ in cycle frequency. Consequence of the certified R²
complex Bochner kernel, NOT a new source input. -/
theorem source_actual_fourier_lift_integrable434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    Integrable (fun s : ℝ =>
      ∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t)) := by
  have hprod := source_actual_collar_lift_integrable434
    chi kappa B hB hchi j hj h hh P hP M hM hBound
  exact hprod.integral_prod_left
/-- The physical Q_h has an honest integrable CLASSICAL Fourier transform;
the whole-real inversion theorem can therefore apply if Q is continuous. -/
theorem source_actual_physical_Q_fourier_integrable434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    Integrable (𝓕 (sourceActualPhysicalQ434 chi kappa h P)) := by
  have hEq : (𝓕 (sourceActualPhysicalQ434 chi kappa h P) : ℝ → ℂ) =
      (fun s : ℝ => ∫ t : ℝ,
        sourceActualCollarLift434 chi kappa h P (s,t)) := by
    funext s
    exact source_actual_physical_Q_fourier_equals_lift434
      chi kappa B hB hchi j hj h hh P hP M hM hBound s
  rw [hEq]
  exact source_actual_fourier_lift_integrable434
    chi kappa B hB hchi j hj h hh P hP M hM hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceActualPhysicalL2Schur -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1800000

/-- True SOURCE PHYSICAL compact-center L² collar operator bound,
not merely a Fourier-side abstract inverse. All integrability and
Plancherel compatibility dependencies are now independently certified. -/
theorem source_actual_physical_Q_L2_schur434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ), 0 < h →
      ∀ (P : ℝ → ℂ) (hP : Continuous P)
        (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M),
        (∫ u : ℝ, ‖sourceActualPhysicalQ434 chi kappa h P u‖^2) ≤
          C^2 * (2*Real.pi) *
            (∫ s : ℝ, collarSchurWeight434 s)^2 *
            (∫ t : ℝ, ((1+h*|t|)^j)⁻¹ * ‖P t‖^2) := by
  obtain ⟨C,hC,hFourier⟩ :=
    source_actual_collar_fourier_L2_schur434 chi kappa B hB hchi j hj
  refine ⟨C,hC,?_⟩
  intro h hh P hP M hM hBound
  let Q : ℝ → ℂ := sourceActualPhysicalQ434 chi kappa h P
  let L : ℝ → ℂ := fun s =>
    ∫ t : ℝ, sourceActualCollarLift434 chi kappa h P (s,t)
  have hL1 : Integrable Q :=
    source_actual_physical_Q_integrable434
      chi kappa B hB hchi j hj h hh P hP M hM hBound
  have hL2 : MemLp Q 2 (volume : Measure ℝ) :=
    source_actual_physical_Q_memLp434
      chi kappa B hB hchi j hj h hh P hP M hM hBound
  have hF : (𝓕 Q : ℝ → ℂ) = L := by
    funext s
    exact source_actual_physical_Q_fourier_equals_lift434
      chi kappa B hB hchi j hj h hh P hP M hM hBound s
  obtain ⟨hFL2,hFBnd⟩ := hFourier h hh P hP M hM hBound
  have hFC : Continuous L :=
    source_actual_lift_operator_continuous434
      chi kappa B hB hchi j hj h hh P hP M hM hBound
  have hFMem : MemLp (𝓕 Q) 2 (volume : Measure ℝ) := by
    rw [hF]
    exact (memLp_two_iff_integrable_sq_norm
      hFC.aestronglyMeasurable).mpr hFL2
  have hPl := source_generic_classical_plancherel434 Q hL1 hL2 hFMem
  calc
    _ = ∫ s : ℝ, ‖(𝓕 Q) s‖^2 := hPl
    _ = ∫ s : ℝ, ‖L s‖^2 := by rw [hF]
    _ ≤ _ := hFBnd
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalMeasurableSections -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 650000

theorem source_physical_section_ae_measurable434
    (chi kappa : 𝓢(ℝ,ℂ)) (h : ℝ)
    (P : ℝ → ℂ) (hP : Continuous P) (u : ℝ) :
    AEStronglyMeasurable
      (sourceActualPhysicalTimeKernel434 chi kappa h P u) := by
  have hc := source_actual_physical_kernel_joint_continuous434 chi kappa h P hP
  exact (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

theorem source_physical_param_continuous434
    (chi kappa : 𝓢(ℝ,ℂ)) (h : ℝ)
    (P : ℝ → ℂ) (hP : Continuous P) (t : ℝ) :
    Continuous (fun u : ℝ =>
      sourceActualPhysicalTimeKernel434 chi kappa h P u t) := by
  have hc := source_actual_physical_kernel_joint_continuous434 chi kappa h P hP
  have ht : Continuous (fun _ : ℝ => t) := continuous_const
  have hpair : Continuous (fun u : ℝ => (u,t)) :=
    continuous_id.prodMk ht
  have hs := hc.comp hpair
  convert hs using 1 <;> ext u <;> rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalDominatedRows -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 750000

theorem source_physical_uniform_dominating_rows434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ t, ‖P t‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ),
      ∀ᵐ t ∂(volume : Measure ℝ),
        ‖sourceActualPhysicalTimeKernel434 chi kappa h P u t‖ ≤
        (C*M)*((1+h*|t|)^j)⁻¹ := by
  obtain ⟨C,hC,hmaj⟩ :=
    source_actual_physical_time_kernel_majorant434 chi kappa B hB hchi j
  refine ⟨C,hC,?_⟩
  intro u
  exact Filter.Eventually.of_forall (hmaj h hh P M hM hBound u)
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalQContinuityTerminal -/

section

open MeasureTheory
open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1300000

/-- REAL source physical Q is continuous everywhere. It is not
merely an L² equivalence class, and no source-saving is required. -/
theorem source_actual_physical_Q_continuous_native434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j)
    (h : ℝ) (hh : 0 < h)
    (P : ℝ → ℂ) (hP : Continuous P)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ t, ‖P t‖ ≤ M) :
    Continuous (sourceActualPhysicalQ434 chi kappa h P) := by
  obtain ⟨C,hC,hdom⟩ :=
    source_physical_uniform_dominating_rows434 chi kappa B hB hchi
      j h hh P M hM hBound
  let F : ℝ → ℝ → ℂ :=
    fun u t => sourceActualPhysicalTimeKernel434 chi kappa h P u t
  let bound : ℝ → ℝ := fun t => (C*M)*((1+h*|t|)^j)⁻¹
  have hb : Integrable bound :=
    (source_real_time_weight_integrable434 h hh j hj).const_mul (C*M)
  have hm (u : ℝ) : AEStronglyMeasurable (F u) :=
    source_physical_section_ae_measurable434 chi kappa h P hP u
  have hd (u : ℝ) :
      ∀ᵐ t ∂(volume : Measure ℝ), ‖F u t‖ ≤ bound t := hdom u
  have hc (t : ℝ) : Continuous (fun u : ℝ => F u t) :=
    source_physical_param_continuous434 chi kappa h P hP t
  have hres := source_generic_dominated_continuity434 F bound hb hm hd hc
  change Continuous (fun u : ℝ =>
    ∫ t : ℝ, sourceActualPhysicalTimeKernel434 chi kappa h P u t)
  exact hres
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalScaleJacobian -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 550000

/-- At v=Y exp u, the original angular real-time inversion has
the EXACT H/(2πv) factor. No H or Y is dropped. -/
theorem source_physical_exact_v_prefactor434
    (H Y u : ℝ) (hY : 0 < Y) :
    H/(2*Real.pi*(Y*Real.exp u)) =
      (H/(2*Real.pi*Y))*Real.exp (-u) := by
  rw [Real.exp_neg]
  have hp : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- The physical collar's two geometric factors combine into exactly
1/Y times the fixed angular/cycle Fourier normalization (2π)^(-2). -/
theorem source_physical_one_over_Y_2pi434
    (H Y : ℝ) (hH : 0 < H) (hY : 0 < Y) :
    (Y/H^2) * (H/(2*Real.pi*Y))^2 =
      (1/Y) * (1/(2*Real.pi)^2) := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
/-- The original physical phase at v=Y exp u splits into the
unchanged Mellin polynomial's common Y-twist and the log-center phase.
This certifies the sign of u*t used in physical/Fourier Q. -/
theorem source_physical_log_phase434
    (Y u t : ℝ) (hY : 0 < Y) :
    Complex.exp (((-t*Real.log (Y*Real.exp u):ℝ):ℂ)*Complex.I) =
      Complex.exp (((-t*Real.log Y:ℝ):ℂ)*Complex.I) *
      Complex.exp (((-(u*t):ℝ):ℂ)*Complex.I) := by
  rw [Real.log_mul hY.ne' (Real.exp_pos u).ne', Real.log_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceResidualConvolution -/

section

/-!
Exact finite source residual R(t) product/collapse. The dyadic supports
and the original alpha/character/marked d coefficients remain explicit.
No abstract L² estimate is asserted for a replacement sequence.
-/

namespace Green64Analytic.CorrelationMellin

noncomputable def sourceResidualProductCoeff
    (M R : Finset ℕ) (a d : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ z ∈ (M.product R).filter (fun z => z.1 * z.2 = n),
    a z.1 * d z.2

theorem source_residual_product_collapse
    (M R : Finset ℕ) (a d : ℕ → ℂ) (t : ℝ)
    (hM : ∀ m ∈ M, 0 < m)
    (hR : ∀ r ∈ R, 0 < r) :
    (∑ m ∈ M, a m * sourcePhase m t) *
       (∑ r ∈ R, d r * sourcePhase r t) =
      ∑ n ∈ (M.product R).image (fun z => z.1 * z.2),
        sourceResidualProductCoeff M R a d n * sourcePhase n t := by
  classical
  let s := M.product R
  let idx : ℕ × ℕ → ℕ := fun z => z.1 * z.2
  have hprod :
      (∑ m ∈ M, a m * sourcePhase m t) *
         (∑ r ∈ R, d r * sourcePhase r t) =
        ∑ z ∈ s, (a z.1 * d z.2) * sourcePhase (idx z) t := by
    calc
      _ = ∑ m ∈ M, ∑ r ∈ R,
          (a m * sourcePhase m t) * (d r * sourcePhase r t) :=
        Finset.sum_mul_sum M R _ _
      _ = ∑ z ∈ s, (a z.1 * d z.2) * sourcePhase (idx z) t := by
        rw [show (∑ z ∈ s, (a z.1*d z.2)*sourcePhase (idx z) t) =
          ∑ m ∈ M, ∑ r ∈ R, (a m*d r)*sourcePhase (m*r) t by
            simpa [s, idx] using
              (Finset.sum_product' M R
                (fun m r => (a m * d r) * sourcePhase (m*r) t))]
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro r hr
        rw [sourcePhase_mul m r (hM m hm) (hR r hr)]
        ring
  have hgroup := collapsed_fiber_sum_eq s idx
    (fun z => (a z.1*d z.2)*sourcePhase (idx z) t)
  calc
    _ = ∑ z ∈ s, (a z.1*d z.2)*sourcePhase (idx z) t := hprod
    _ = ∑ n ∈ s.image idx,
        ∑ z ∈ s.filter (fun z => idx z = n),
          (a z.1*d z.2)*sourcePhase (idx z) t := hgroup.symm
    _ = ∑ n ∈ s.image idx,
        (∑ z ∈ s.filter (fun z => idx z = n), a z.1*d z.2) *
          sourcePhase n t := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro z hz
        rw [(Finset.mem_filter.mp hz).2]
    _ = _ := rfl

/-- Literal source alpha with character and low-frequency twist. -/
noncomputable def sourceAlphaCharacterCoefficient
    (alpha chi : ℕ → ℂ) (sigma0 : ℝ) (m : ℕ) : ℂ :=
  alpha m * chi m * (m : ℂ)⁻¹ * sourcePhase m sigma0

/-- Literal original collapsed marked residual d_{r'} with reciprocal factor. -/
noncomputable def sourceMarkedResidualCoefficient
    (d : ℕ → ℂ) (r : ℕ) : ℂ :=
  d r * (r : ℂ)⁻¹

/-- The *source* alpha/character/residual polynomial product is
exactly the collapsed genuine-frequency polynomial, retaining both
dyadic supports, alpha, character, sigma0, and the marked d coefficients. -/
theorem source_character_residual_collapse
    (M R : Finset ℕ) (alpha chi d : ℕ → ℂ)
    (sigma0 t : ℝ) (hM : ∀ m ∈ M, 0 < m)
    (hR : ∀ r ∈ R, 0 < r) :
    (∑ m ∈ M, alpha m * chi m * (m : ℂ)⁻¹ *
        sourcePhase m (sigma0+t)) *
      (∑ r ∈ R, d r * (r : ℂ)⁻¹ * sourcePhase r t) =
      ∑ n ∈ (M.product R).image (fun z => z.1*z.2),
        sourceResidualProductCoeff M R
          (sourceAlphaCharacterCoefficient alpha chi sigma0)
          (sourceMarkedResidualCoefficient d) n *
          sourcePhase n t := by
  classical
  calc
    _ = (∑ m ∈ M, sourceAlphaCharacterCoefficient alpha chi sigma0 m * sourcePhase m t) *
        (∑ r ∈ R, sourceMarkedResidualCoefficient d r * sourcePhase r t) := by
          congr 1
          · apply Finset.sum_congr rfl
            intro m hm
            rw [sourcePhase_add]
            dsimp [sourceAlphaCharacterCoefficient]
            ring
    _ = _ := source_residual_product_collapse M R
      (sourceAlphaCharacterCoefficient alpha chi sigma0)
      (sourceMarkedResidualCoefficient d) t hM hR
end Green64Analytic.CorrelationMellin

end

/-! ## SourceResidualDivisorFiber -/

section

/-!
A kernel-checked representation-fiber bound for actual source residual
Dirichlet convolutions. An equality mr=n has at most tau(n) ordered
pairs in arbitrary supports M,R, for m,r positive.
-/

namespace Green64Analytic.CorrelationMellin

/-- The exact number of ordered `m*r=n` representations in positive
source dyads is bounded by the genuine natural-number divisor count. -/
theorem source_residual_integer_product_fiber_le_divisors
    (M R : Finset ℕ) (n : ℕ)
    (hM : ∀ m ∈ M, 0 < m) (hR : ∀ r ∈ R, 0 < r) :
    ((M.product R).filter (fun z => z.1*z.2=n)).card ≤ n.divisors.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun z : ℕ × ℕ => z.1)
  · intro z hz
    have hzMR := (Finset.mem_filter.mp hz).1
    have hn := (Finset.mem_filter.mp hz).2
    have hm := (Finset.mem_product.mp hzMR).1
    have hr := (Finset.mem_product.mp hzMR).2
    have hnonzero : n ≠ 0 := by
      have hznonzero : z.1*z.2 ≠ 0 :=
        mul_ne_zero (Nat.ne_of_gt (hM z.1 hm)) (Nat.ne_of_gt (hR z.2 hr))
      simpa only [hn] using hznonzero
    exact Nat.mem_divisors.mpr ⟨⟨z.2, hn.symm⟩, hnonzero⟩
  · intro z hz w hw hfirst
    have hzMR := (Finset.mem_filter.mp hz).1
    have hm := (Finset.mem_product.mp hzMR).1
    have hzEq := (Finset.mem_filter.mp hz).2
    have hwEq := (Finset.mem_filter.mp hw).2
    have hsecond : z.2=w.2 := by
      apply Nat.mul_left_cancel (hM z.1 hm)
      simpa only [hfirst] using hzEq.trans hwEq.symm
    exact Prod.ext hfirst hsecond
end Green64Analytic.CorrelationMellin

end

/-! ## SourceResidualDivisorNorm -/

section

/-! Exact pointwise norm bound for the source alpha-character times
marked-residual convolution. The only assumptions on actual factors
are their reciprocal coefficient bounds; big-mark restrictions remain
inside the original `d` and dyadic supports. -/

namespace Green64Analytic.CorrelationMellin

theorem source_residual_product_coefficient_divisor_bound
    (M R : Finset ℕ) (a d : ℕ → ℂ) (A D : ℝ)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hM : ∀ m ∈ M, 0 < m) (hR : ∀ r ∈ R, 0 < r)
    (ha : ∀ m ∈ M, ‖a m‖ ≤ A/(m:ℝ))
    (hd : ∀ r ∈ R, ‖d r‖ ≤ D/(r:ℝ))
    (n : ℕ) (hn : 0 < n) :
    ‖sourceResidualProductCoeff M R a d n‖ ≤
      (n.divisors.card:ℝ) * (A*D)/(n:ℝ) := by
  classical
  let fiber := (M.product R).filter (fun z => z.1*z.2=n)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hTerm (z : ℕ × ℕ) (hz : z ∈ fiber) :
      ‖a z.1 * d z.2‖ ≤ (A*D)/(n:ℝ) := by
    have hzMR := (Finset.mem_filter.mp hz).1
    have hzProd := (Finset.mem_filter.mp hz).2
    have hm := (Finset.mem_product.mp hzMR).1
    have hr := (Finset.mem_product.mp hzMR).2
    have hmR : (0:ℝ) < z.1 := by exact_mod_cast hM z.1 hm
    have hrR : (0:ℝ) < z.2 := by exact_mod_cast hR z.2 hr
    calc
      ‖a z.1 * d z.2‖ = ‖a z.1‖ * ‖d z.2‖ := norm_mul _ _
      _ ≤ (A/(z.1:ℝ)) * (D/(z.2:ℝ)) :=
        mul_le_mul (ha z.1 hm) (hd z.2 hr)
          (norm_nonneg _) (div_nonneg hA hmR.le)
      _ = (A*D)/(n:ℝ) := by
        have hnprod : (n:ℝ) = (z.1:ℝ)*(z.2:ℝ) := by
          rw [← Nat.cast_mul, hzProd]
        rw [hnprod]
        field_simp <;> ring
  have hCard : (fiber.card:ℝ) ≤ (n.divisors.card:ℝ) := by
    exact_mod_cast source_residual_integer_product_fiber_le_divisors
      M R n hM hR
  calc
    ‖sourceResidualProductCoeff M R a d n‖ ≤
        ∑ z ∈ fiber, ‖a z.1 * d z.2‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _z ∈ fiber, (A*D)/(n:ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      exact hTerm z hz
    _ = (fiber.card:ℝ) * ((A*D)/(n:ℝ)) := by simp
    _ ≤ (n.divisors.card:ℝ) * ((A*D)/(n:ℝ)) :=
      mul_le_mul_of_nonneg_right hCard
        (div_nonneg (mul_nonneg hA hD) hnR.le)
    _ = (n.divisors.card:ℝ) * (A*D)/(n:ℝ) := by ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceResidualActualReciprocalNorm -/

section

/-! Instantiation of the source R(t) convolution norm with the literal
alpha, character, sigma0, and big-mark d coefficients. Character and
mark restrictions remain hypotheses on the same original sequences. -/

namespace Green64Analytic.CorrelationMellin

theorem source_alpha_character_reciprocal_norm
    (alpha chi : ℕ → ℂ) (sigma : ℝ) (m : ℕ) (A : ℝ)
    (hm : 0 < m) (hA : 0 ≤ A)
    (ha : ‖alpha m‖ ≤ A) (hc : ‖chi m‖ ≤ 1) :
    ‖sourceAlphaCharacterCoefficient alpha chi sigma m‖ ≤ A/(m:ℝ) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have heq : ‖sourceAlphaCharacterCoefficient alpha chi sigma m‖ =
      (‖alpha m‖ * ‖chi m‖) / (m:ℝ) := by
    simp [sourceAlphaCharacterCoefficient, norm_mul, norm_inv,
      sourcePhase_norm, div_eq_mul_inv]
  rw [heq]
  apply div_le_div_of_nonneg_right _ hmR.le
  calc
    ‖alpha m‖ * ‖chi m‖ ≤ A*1 :=
      mul_le_mul ha hc (norm_nonneg _) hA
    _ = A := by ring

theorem source_marked_residual_reciprocal_norm
    (d : ℕ → ℂ) (r : ℕ) (D : ℝ)
    (hr : 0 < r) (hd : ‖d r‖ ≤ D) :
    ‖sourceMarkedResidualCoefficient d r‖ ≤ D/(r:ℝ) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  calc
    ‖sourceMarkedResidualCoefficient d r‖ = ‖d r‖ / (r:ℝ) := by
      simp [sourceMarkedResidualCoefficient, norm_mul, norm_inv,
        div_eq_mul_inv]
    _ ≤ D/(r:ℝ) := div_le_div_of_nonneg_right hd hrR.le

/-- The literal two-factor source residual product retains its exact
alpha-character coefficient and its actual remaining marked weight. -/
theorem source_character_residual_coefficient_divisor_bound
    (M R : Finset ℕ) (alpha chi d : ℕ → ℂ)
    (sigma0 : ℝ) (A D : ℝ)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hM : ∀ m ∈ M, 0 < m) (hR : ∀ r ∈ R, 0 < r)
    (ha : ∀ m ∈ M, ‖alpha m‖ ≤ A)
    (hchi : ∀ m ∈ M, ‖chi m‖ ≤ 1)
    (hd : ∀ r ∈ R, ‖d r‖ ≤ D)
    (n : ℕ) (hn : 0 < n) :
    ‖sourceResidualProductCoeff M R
        (sourceAlphaCharacterCoefficient alpha chi sigma0)
        (sourceMarkedResidualCoefficient d) n‖ ≤
      (n.divisors.card:ℝ) * (A*D)/(n:ℝ) := by
  refine source_residual_product_coefficient_divisor_bound
    M R (sourceAlphaCharacterCoefficient alpha chi sigma0)
    (sourceMarkedResidualCoefficient d) A D hA hD hM hR ?_ ?_ n hn
  · intro m hm
    exact source_alpha_character_reciprocal_norm
      alpha chi sigma0 m A (hM m hm) hA (ha m hm) (hchi m hm)
  · intro r hr
    exact source_marked_residual_reciprocal_norm
      d r D (hR r hr) (hd r hr)
end Green64Analytic.CorrelationMellin

end

/-! ## SourceReusedCollapsedMass -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000
open scoped BigOperators
namespace Green64Analytic.Correlation

def ExpectedCollapsedCoefficientMass : Prop :=
∀ (N r : ℕ) (F : Finset ℕ) (S : Finset (Fin (r+1) → ℕ))
 (a : Fin (r+1) → ℕ → ℂ) (A : Fin (r+1) → ℝ) (U : ℝ),
 (∀ i, 0 ≤ A i) → 0 < U → F ⊆ Finset.Icc 1 N →
 (∀ n ∈ F, U ≤ (n:ℝ)) → (∀ v ∈ S, ∀ i, ‖a i (v i)‖ ≤ A i) →
 (∑ n ∈ F, ‖∑ v ∈ S.filter (fun v => ∏ i, v i = n),
     ∏ i, a i (v i) / (v i : ℂ)‖^2) ≤
 (∏ i, A i)^2 / U * (1+Real.log N)^(2^(2*r))

theorem collapsedCoefficientMass : ExpectedCollapsedCoefficientMass :=
by
  have mass : ∀ (N r : ℕ) (F : Finset ℕ) (c : ℕ → ℂ) (A U : ℝ),
 0 ≤ A → 0 < U → F ⊆ Finset.Icc 1 N →
 (∀ n ∈ F, U ≤ (n:ℝ)) →
 (∀ n ∈ F, ‖c n‖ ≤ A * (n.divisors.card : ℝ)^r / n) →
 (∑ n ∈ F, ‖c n‖^2) ≤ A^2/U * (1+Real.log N)^(2^(2*r)) := by
    have moment : ∀ (N k : ℕ), (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)^k / n) ≤ (1+Real.log N)^(2^k) := by
      have moment : ∀ (N k : ℕ), (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)^k / n) ≤ (∑ n ∈ Finset.Icc 1 N, (1 : ℝ)/n)^(2^k) := by
        have point : ∀ (n k : ℕ), (n.divisors.card : ℝ)^(k+1) ≤ ∑ d ∈ n.divisors, (d.divisors.card : ℝ)^k * ((n/d).divisors.card : ℝ)^k := by
          have submul : ∀ (a b : ℕ), (a*b).divisors.card ≤ a.divisors.card * b.divisors.card := by
            intro a b
            classical
            by_cases ha : a = 0
            · simp [ha]
            by_cases hb : b = 0
            · simp [hb]
            have hsub : (a*b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun p => p.1*p.2) := by
              intro d hd
              rcases Nat.dvd_mul.mp (Nat.mem_divisors.mp hd).1 with ⟨u,v,hu,hv,he⟩
              exact Finset.mem_image.mpr ⟨(u,v), Finset.mem_product.mpr
                ⟨Nat.mem_divisors.mpr ⟨hu,ha⟩,Nat.mem_divisors.mpr ⟨hv,hb⟩⟩,he⟩
            exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans_eq (Finset.card_product _ _))
          
          intro n k
          calc
            _ = ∑ d ∈ n.divisors, (n.divisors.card : ℝ)^k := by
              simp only [Finset.sum_const, nsmul_eq_mul, pow_succ]
              ring
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro d hd
              have h := submul d (n/d)
              rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1] at h
              have hc : (n.divisors.card : ℝ) ≤ (d.divisors.card : ℝ)*((n/d).divisors.card : ℝ) := by exact_mod_cast h
              simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ n.divisors.card) hc k
        
        have conv : ∀ (N : ℕ) (f g : ℕ → ℝ), (∀ n, 0 ≤ f n) → (∀ n, 0 ≤ g n) → (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f d * g (n/d)) ≤ (∑ n ∈ Finset.Icc 1 N, f n) * (∑ n ∈ Finset.Icc 1 N, g n) := by
          intro N f g hf hg
          classical
          let S := (Finset.Icc 1 N).sigma (fun n => n.divisors)
          let F : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2,p.1/p.2)
          have hp (p : Σ _ : ℕ, ℕ) (h : p ∈ S) :
              1 ≤ p.1 ∧ p.1 ≤ N ∧ p.2 ∣ p.1 := by
            rcases Finset.mem_sigma.mp h with ⟨h1,h2⟩
            exact ⟨(Finset.mem_Icc.mp h1).1,(Finset.mem_Icc.mp h1).2,(Nat.mem_divisors.mp h2).1⟩
          have he (p : Σ _ : ℕ, ℕ) (h : p ∈ S) : p.2 * (p.1/p.2) = p.1 :=
            Nat.mul_div_cancel' (hp p h).2.2
          have hi : Set.InjOn F (↑S : Set (Σ _ : ℕ, ℕ)) := by
            intro p hp' q hq' heq
            have h1 : p.2 = q.2 := congrArg Prod.fst heq
            have h2 : p.1/p.2 = q.1/q.2 := congrArg Prod.snd heq
            have h0 : p.1 = q.1 := by rw [←he p hp',←he q hq',h2,h1]
            cases p; cases q
            simp_all
          have hs : S.image F ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N := by
            intro p h
            rcases Finset.mem_image.mp h with ⟨q,hq,rfl⟩
            have h := hp q hq
            have hqpos : 0 < q.1 := by omega
            have hdpos : 0 < q.2 := Nat.pos_of_dvd_of_pos h.2.2 hqpos
            have hdivpos : 0 < q.1/q.2 := Nat.div_pos (Nat.le_of_dvd hqpos h.2.2) hdpos
            exact Finset.mem_product.mpr
              ⟨Finset.mem_Icc.mpr ⟨hdpos,(Nat.le_of_dvd hqpos h.2.2).trans h.2.1⟩,
               Finset.mem_Icc.mpr ⟨hdivpos,(Nat.div_le_self _ _).trans h.2.1⟩⟩
          calc
            _ = ∑ p ∈ S, f (F p).1 * g (F p).2 := by
              dsimp [S,F]
              rw [Finset.sum_sigma]
            _ = ∑ p ∈ S.image F, f p.1*g p.2 := by rw [Finset.sum_image hi]
            _ ≤ ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, f p.1*g p.2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => mul_nonneg (hf _) (hg _))
            _ = _ := by rw [Finset.sum_product,Finset.sum_mul_sum]
        
        intro N k
        induction k with
        | zero => simp
        | succ k ih =>
          have hn (n : ℕ) : 0 ≤ (n.divisors.card : ℝ)^k / n := by positivity
          have hH : 0 ≤ ∑ n ∈ Finset.Icc 1 N, (1:ℝ)/n := Finset.sum_nonneg (fun n _ => by positivity)
          calc
            _ ≤ ∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
                (d.divisors.card : ℝ)^k * ((n/d).divisors.card : ℝ)^k) / n := by
              exact Finset.sum_le_sum (fun n _ => div_le_div_of_nonneg_right (point n k) (Nat.cast_nonneg n))
            _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
                ((d.divisors.card : ℝ)^k / d) * (((n/d).divisors.card : ℝ)^k / (n/d : ℕ)) := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro d hd
              rw [div_mul_div_comm]
              congr 1
              exact_mod_cast (Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1).symm
            _ ≤ (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)^k/n) *
                (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)^k/n) := conv N _ _ hn hn
            _ ≤ (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/n)^(2^k) *
                (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/n)^(2^k) := 
              mul_le_mul ih ih (Finset.sum_nonneg (fun n _ => hn n)) (pow_nonneg hH _)
            _ = _ := by rw [←pow_two,←pow_mul,pow_succ]
      
      intro N k
      have hH : (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/n) = (harmonic N : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        simp only [one_div]
      exact (moment N k).trans (pow_le_pow_left₀
        (Finset.sum_nonneg (fun n _ => by positivity)) (by rw [hH]; exact harmonic_le_one_add_log N) _)
    
    intro N r F c A U hA hU hF hu hc
    have hpoint (n : ℕ) (hn : n ∈ F) :
        ‖c n‖^2 ≤ (A^2/U) * ((n.divisors.card : ℝ)^(2*r)/n) := by
      have hnpos : (0:ℝ) < n := lt_of_lt_of_le hU (hu n hn)
      have hs := pow_le_pow_left₀ (norm_nonneg (c n)) (hc n hn) 2
      have hd : (n.divisors.card : ℝ)^(2*r) = ((n.divisors.card : ℝ)^r)^2 := by rw [mul_comm 2 r,pow_mul]
      rw [div_pow,mul_pow,←hd] at hs
      apply hs.trans
      have hinv : 1/(n:ℝ) ≤ 1/U := one_div_le_one_div_of_le hU (hu n hn)
      have hh := mul_le_mul_of_nonneg_left hinv (show 0 ≤ A^2 * (n.divisors.card : ℝ)^(2*r)/(n:ℝ) by positivity)
      convert hh using 1 <;> field_simp <;> ring
    calc
      _ ≤ ∑ n ∈ F, (A^2/U)*((n.divisors.card : ℝ)^(2*r)/n) := Finset.sum_le_sum hpoint
      _ = (A^2/U)*∑ n ∈ F, (n.divisors.card : ℝ)^(2*r)/n := by rw [Finset.mul_sum]
      _ ≤ (A^2/U)*∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ)^(2*r)/n :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hF (fun n _ _ => by positivity)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (moment N (2*r)) (by positivity)
  
  have coeff : ∀ (n r : ℕ) (S : Finset (Fin (r+1) → ℕ)) (a : Fin (r+1) → ℕ → ℂ) (A : Fin (r+1) → ℝ),
 n ≠ 0 → (∀ i, 0 ≤ A i) → (∀ v ∈ S, ∏ i, v i = n) →
 (∀ v ∈ S, ∀ i, ‖a i (v i)‖ ≤ A i) →
 ‖∑ v ∈ S, ∏ i, a i (v i) / (v i : ℂ)‖ ≤
   (∏ i, A i) * (n.divisors.card : ℝ)^r / n := by
    have tupleCount : ∀ (n r : ℕ) (S : Finset (Fin (r+1) → ℕ)), n ≠ 0 → (∀ v ∈ S, ∏ i, v i = n) → S.card ≤ n.divisors.card ^ r := by
      intro n r S hn hprod
      classical
      have hd (v : S) (i : Fin (r+1)) : v.val i ∈ n.divisors := by
        apply Nat.mem_divisors.mpr
        refine ⟨?_,hn⟩
        rw [←hprod v.val v.property]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      let F : S → (Fin r → n.divisors) := fun v i => ⟨v.val i.castSucc, hd v i.castSucc⟩
      have hi : Function.Injective F := by
        intro v w heq
        have he (i : Fin r) : v.val i.castSucc = w.val i.castSucc :=
          congrArg Subtype.val (congrFun heq i)
        have heprod : (∏ i : Fin r, v.val i.castSucc) = (∏ i : Fin r, w.val i.castSucc) :=
          Finset.prod_congr rfl (fun i _ => he i)
        have hv := hprod v.val v.property
        have hw := hprod w.val w.property
        rw [Fin.prod_univ_castSucc] at hv hw
        have hne : (∏ i : Fin r, v.val i.castSucc) ≠ 0 := by
          intro h
          rw [h,zero_mul] at hv
          exact hn hv.symm
        have hl : v.val (Fin.last r) = w.val (Fin.last r) := by
          apply mul_left_cancel₀ hne
          calc
            _ = n := hv
            _ = _ := by rw [heprod]; exact hw.symm
        apply Subtype.ext
        funext i
        exact Fin.lastCases hl (fun j => he j) i
      have h := Fintype.card_le_of_injective F hi
      simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using h
    
    intro n r S a A hn hA hp ha
    have hc : (S.card : ℝ) ≤ (n.divisors.card : ℝ)^r := by exact_mod_cast tupleCount n r S hn hp
    have ht (v) (hv : v ∈ S) :
        ‖∏ i, a i (v i) / (v i : ℂ)‖ ≤ (∏ i, A i) / n := by
      rw [Finset.prod_div_distrib,norm_div,norm_prod]
      have he : (∏ i, (v i : ℂ)) = (n:ℂ) := by exact_mod_cast hp v hv
      rw [he,Complex.norm_natCast]
      exact div_le_div_of_nonneg_right
        (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ha v hv i)) (Nat.cast_nonneg n)
    calc
      _ ≤ ∑ v ∈ S, ‖∏ i, a i (v i) / (v i : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ S, (∏ i, A i)/(n:ℝ) := Finset.sum_le_sum ht
      _ = (S.card : ℝ) * ((∏ i, A i)/n) := by simp
      _ ≤ (n.divisors.card : ℝ)^r * ((∏ i, A i)/n) :=
        mul_le_mul_of_nonneg_right hc (div_nonneg (Finset.prod_nonneg (fun i _ => hA i)) (Nat.cast_nonneg n))
      _ = _ := by ring
  
  intro N r F S a A U hA hU hF hu ha
  apply mass N r F _ (∏ i, A i) U (Finset.prod_nonneg (fun i _ => hA i)) hU hF hu
  intro n hn
  have hn0 : n ≠ 0 := by
    have h := (Finset.mem_Icc.mp (hF hn)).1
    omega
  apply coeff n r _ a A hn0 hA
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v hv i
    exact ha v (Finset.mem_filter.mp hv).1 i


end Green64Analytic.Correlation

end

/-! ## SourceReusedContinuousMeanSquare -/

section

set_option maxHeartbeats 0
set_option maxRecDepth 10000

open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.Correlation

/-- Arbitrary coefficients on positive integer support, uniform in both real endpoints. -/
def ExpectedContinuousMeanSquare : Prop :=
∀ (N : ℕ) (F : Finset ℕ) (c : ℕ → ℂ) (a b : ℝ), F ⊆ Finset.Icc 1 N → a ≤ b →
 (∫ t in Set.Icc a b, ‖∑ n ∈ F, c n * Complex.exp (((t * Real.log (n:ℝ) : ℝ) : ℂ)*Complex.I)‖^2)
 ≤ ((b-a)+16*(N:ℝ)*(1+Real.log N)) * ∑ n ∈ F, ‖c n‖^2

theorem continuousMeanSquare : ExpectedContinuousMeanSquare :=
by
  have meanSquareRange : ∀ (N : ℕ) (c : ℕ → ℂ) (a b : ℝ), a ≤ b →
 (∫ t in a..b, ‖∑ n ∈ Finset.range N, c n * Complex.exp (((t * Real.log ((n:ℝ)+1) : ℝ) : ℂ)*Complex.I)‖^2)
 ≤ ((b-a)+16*(N:ℝ)*(1+Real.log N)) * ∑ n ∈ Finset.range N, ‖c n‖^2 := by
    have meanGram : ∀ (ι : Type) [Fintype ι] (f : ι → ℝ → ℂ) (c : ι → ℂ) (a b C : ℝ),
   a ≤ b → (∀ i, Continuous (f i)) →
   (∀ i, ∑ j, ‖∫ t in a..b, f i t * star (f j t)‖ ≤ C) →
   (∫ t in a..b, ‖∑ i, c i * f i t‖^2) ≤ C * ∑ i, ‖c i‖^2 := by
      have schur :  ∀ (ι : Type) [Fintype ι] (K : ι → ι → ℝ) (a : ι → ℝ) (C : ℝ),
     (∀ i j, 0 ≤ K i j) →
     (∀ i j, K i j = K j i) →
     (∀ i, ∑ j, K i j ≤ C) →
     ∑ i, ∑ j, a i * a j * K i j ≤ C * ∑ i, (a i)^2 := by
        intro ι _ K a C hK hsym hrow
        have hp (i j : ι) :
            a i * a j * K i j ≤ ((a i)^2 * K i j + (a j)^2 * K i j)/2 := by
          nlinarith [mul_nonneg (sq_nonneg (a i - a j)) (hK i j)]
        have hle := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
          Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
        have hswap : (∑ i, ∑ j, (a j)^2 * K i j) = ∑ i, ∑ j, (a i)^2 * K i j := by
          rw [Finset.sum_comm]
          congr 1
          funext i
          apply Finset.sum_congr rfl
          intro j _
          rw [hsym j i]
        have hbound : (∑ i, ∑ j, (a i)^2 * K i j) ≤ C * ∑ i, (a i)^2 := by
          calc
            _ = ∑ i, (a i)^2 * (∑ j, K i j) := by simp only [Finset.mul_sum]
            _ ≤ ∑ i, (a i)^2 * C := Finset.sum_le_sum (fun i _ =>
              mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (a i)))
            _ = C * ∑ i, (a i)^2 := by simp only [Finset.mul_sum, mul_comm]
        simp only [← Finset.sum_div, Finset.sum_add_distrib] at hle
        rw [hswap] at hle
        linarith
      intro ι _ f c a b C hab hf hrow
      classical
      let K : ι → ι → ℝ := fun i j => ‖∫ t in a..b, f i t * star (f j t)‖
      have hKsym (i j : ι) : K i j = K j i := by
        dsimp [K]
        have hid : (fun t => f i t * star (f j t)) =
            (fun t => star (f j t * star (f i t))) := by
          funext t
          simp [mul_comm]
        change ‖∫ t in a..b, (fun t => f i t * star (f j t)) t‖ = _
        rw [hid]
        change ‖∫ t in a..b, (starRingEnd ℂ) (f j t * star (f i t))‖ = _
        rw [intervalIntegral.intervalIntegral_conj]
        exact norm_star _
      have hpoint (t : ℝ) :
          ((‖∑ i, c i * f i t‖^2 : ℝ) : ℂ) =
          ∑ i, ∑ j, (c i * star (c j)) * (f i t * star (f j t)) := by
        rw [Complex.ofReal_pow, ← Complex.mul_conj']
        simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change c i * f i t * (star (c j) * star (f j t)) = _
        ring
      have hc (i j : ι) : Continuous (fun t => (c i * star (c j)) * (f i t * star (f j t))) := by
        fun_prop
      have hint :
          (∫ t in a..b, ((‖∑ i, c i * f i t‖^2 : ℝ) : ℂ)) =
          ∑ i, ∑ j, (c i * star (c j)) * (∫ t in a..b, f i t * star (f j t)) := by
        simp_rw [hpoint]
        rw [intervalIntegral.integral_finsetSum (fun i _ => (by
          apply Continuous.intervalIntegrable
          exact continuous_finset_sum _ (fun j _ => hc i j)))]
        apply Finset.sum_congr rfl
        intro i _
        rw [intervalIntegral.integral_finsetSum (fun j _ => (hc i j).intervalIntegrable a b)]
        simp only [intervalIntegral.integral_const_mul]
      have hnonneg : 0 ≤ ∫ t in a..b, ‖∑ i, c i * f i t‖^2 :=
        intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
      calc
        _ = ‖∫ t in a..b, ((‖∑ i, c i * f i t‖^2 : ℝ) : ℂ)‖ := by
          rw [intervalIntegral.integral_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        _ = ‖∑ i, ∑ j, (c i * star (c j)) * (∫ t in a..b, f i t * star (f j t))‖ := congrArg norm hint
        _ ≤ ∑ i, ∑ j, ‖c i‖ * ‖c j‖ * K i j := by
          calc
            _ ≤ ∑ i, ‖∑ j, (c i * star (c j)) * (∫ t in a..b, f i t * star (f j t))‖ := norm_sum_le _ _
            _ ≤ ∑ i, ∑ j, ‖(c i * star (c j)) * (∫ t in a..b, f i t * star (f j t))‖ :=
              Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
            _ = _ := by simp only [norm_mul, norm_star, K]
        _ ≤ _ := schur ι K (fun i => ‖c i‖) C (fun i j => norm_nonneg _) hKsym hrow
    have phase : ∀ (a b z : ℝ), z ≠ 0 → ‖∫ t in a..b, Complex.exp (((t*z : ℝ) : ℂ)*Complex.I)‖ ≤ 2 / |z| := by
      intro a b z hz
      have hc : (z : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hz) Complex.I_ne_zero
      have hid : (fun t : ℝ => Complex.exp (((t*z : ℝ) : ℂ)*Complex.I)) =
          (fun t : ℝ => Complex.exp (((z : ℂ)*Complex.I)*(t : ℂ))) := by
        funext t
        congr 1
        push_cast
        ring
      rw [hid, integral_exp_mul_complex hc, norm_div]
      have he (t : ℝ) : ‖Complex.exp (((z : ℂ)*Complex.I)*(t : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      calc
        _ ≤ (‖Complex.exp (((z : ℂ)*Complex.I)*(b : ℂ))‖ +
          ‖Complex.exp (((z : ℂ)*Complex.I)*(a : ℂ))‖) / ‖(z : ℂ)*Complex.I‖ :=
          div_le_div_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
        _ = 2 / |z| := by norm_num [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have logOff : ∀ (N i j : ℕ), i < N → j < N → i ≠ j → 2 / |Real.log ((i:ℝ)+1) - Real.log ((j:ℝ)+1)| ≤ 4*(N:ℝ)/(1+|(i:ℝ)-(j:ℝ)|) := by
      have logInv : ∀ (m n N : ℝ), 0 < m → m + 1 ≤ n → n ≤ N → 2 / (Real.log n - Real.log m) ≤ 4*N/(1+n-m) := by
        intro m n N hm hmn hnN
        have hn : 0 < n := by linarith
        have hlt : m < n := by linarith
        have hl : 0 < Real.log n - Real.log m := sub_pos.mpr (Real.log_lt_log hm hlt)
        have h := Real.one_sub_inv_le_log_of_pos (div_pos hn hm)
        rw [Real.log_div (ne_of_gt hn) (ne_of_gt hm), inv_div] at h
        have heq : 1 - m/n = (n-m)/n := by field_simp
        rw [heq] at h
        have hmul : n-m ≤ N*(Real.log n-Real.log m) :=
          ((div_le_iff₀ hn).mp h).trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hnN) (le_of_lt hl)])
        apply (div_le_div_iff₀ hl (by linarith : 0 < 1+n-m)).2
        nlinarith
      intro N i j hi hj hij
      have hpos (k : ℕ) : 0 < (k:ℝ)+1 := by positivity
      rcases lt_or_gt_of_ne hij with h | h
      · have hcast : (i:ℝ) < (j:ℝ) := by exact_mod_cast h
        have hl := Real.log_lt_log (hpos i) (by linarith : (i:ℝ)+1 < (j:ℝ)+1)
        rw [abs_of_neg (sub_neg.mpr hl), abs_of_neg (sub_neg.mpr hcast)]
        have he := logInv ((i:ℝ)+1) ((j:ℝ)+1) N (hpos i)
          (by
            have hh : (i:ℝ)+1 ≤ j := by exact_mod_cast Nat.succ_le_iff.mpr h
            linarith) (by exact_mod_cast Nat.succ_le_iff.mpr hj)
        convert he using 1 <;> congr 1 <;> ring
      · have hcast : (j:ℝ) < (i:ℝ) := by exact_mod_cast h
        have hl := Real.log_lt_log (hpos j) (by linarith : (j:ℝ)+1 < (i:ℝ)+1)
        rw [abs_of_pos (sub_pos.mpr hl), abs_of_pos (sub_pos.mpr hcast)]
        have he := logInv ((j:ℝ)+1) ((i:ℝ)+1) N (hpos j)
          (by
            have hh : (j:ℝ)+1 ≤ i := by exact_mod_cast Nat.succ_le_iff.mpr h
            linarith) (by exact_mod_cast Nat.succ_le_iff.mpr hi)
        convert he using 1 <;> congr 1 <;> ring
    have row : ∀ (N : ℕ) (s : Finset ℕ) (t : ℕ → ℝ) (base : ℝ),
   s ⊆ Finset.range N →
   (∀ j ∈ s, base+(j : ℝ) ≤ t j ∧ t j ≤ base+(j : ℝ)+1) →
   ∀ i ∈ s, ∑ j ∈ s, (1+|t i-t j|)⁻¹ ≤
   4 * ∑ k ∈ Finset.range N, (1+(k : ℝ))⁻¹ := by
      intro N s t base hsub ht i hi
      classical
      let f : ℕ → ℝ := fun k => (1+(k : ℝ))⁻¹
      let sl := s.filter (fun j => j ≤ i)
      let sr := s.filter (fun j => ¬j ≤ i)
      have hiN : i < N := Finset.mem_range.mp (hsub hi)
      have hlmap : sl.image (fun j => i-j) ⊆ Finset.range N := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨j,hj,rfl⟩
        exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.sub_le _ _) hiN)
      have hrmap : sr.image (fun j => j-i) ⊆ Finset.range N := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨j,hj,rfl⟩
        have hjN := Finset.mem_range.mp (hsub (Finset.mem_filter.mp hj).1)
        exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.sub_le _ _) hjN)
      have hli : Set.InjOn (fun j : ℕ => i-j) (↑sl : Set ℕ) := by
        intro j hj k hk heq
        have hjle := (Finset.mem_filter.mp hj).2
        have hkle := (Finset.mem_filter.mp hk).2
        dsimp only at heq
        omega
      have hri : Set.InjOn (fun j : ℕ => j-i) (↑sr : Set ℕ) := by
        intro j hj k hk heq
        have hjle := (Finset.mem_filter.mp hj).2
        have hkle := (Finset.mem_filter.mp hk).2
        dsimp only at heq
        omega
      have hlbound : (∑ j ∈ sl, f (i-j)) ≤ ∑ k ∈ Finset.range N, f k := by
        rw [← Finset.sum_image hli]
        exact Finset.sum_le_sum_of_subset_of_nonneg hlmap (fun k hk h => by dsimp [f]; positivity)
      have hrbound : (∑ j ∈ sr, f (j-i)) ≤ ∑ k ∈ Finset.range N, f k := by
        rw [← Finset.sum_image hri]
        exact Finset.sum_le_sum_of_subset_of_nonneg hrmap (fun k hk h => by dsimp [f]; positivity)
      have hleft : (∑ j ∈ sl, (1+|t i-t j|)⁻¹) ≤ 2*(∑ k ∈ Finset.range N, f k) := by
        calc
          _ ≤ ∑ j ∈ sl, 2*f (i-j) := by
            apply Finset.sum_le_sum
            intro j hj
            have hjm := (Finset.mem_filter.mp hj).1
            have hjle := (Finset.mem_filter.mp hj).2
            have hcast : ((i-j : ℕ) : ℝ) = (i : ℝ)-(j : ℝ) := Nat.cast_sub hjle
            have hd : ((i-j : ℕ) : ℝ) ≤ 1+|t i-t j| := by
              rw [hcast]
              linarith [(ht i hi).1,(ht j hjm).2,le_abs_self (t i-t j)]
            dsimp [f]
            rw [← one_div, ← div_eq_mul_inv]
            apply (div_le_div_iff₀ (by positivity) (by positivity)).2
            nlinarith [abs_nonneg (t i-t j)]
          _ = 2*∑ j ∈ sl, f (i-j) := (Finset.mul_sum _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hlbound (by norm_num)
      have hright : (∑ j ∈ sr, (1+|t i-t j|)⁻¹) ≤ 2*(∑ k ∈ Finset.range N, f k) := by
        calc
          _ ≤ ∑ j ∈ sr, 2*f (j-i) := by
            apply Finset.sum_le_sum
            intro j hj
            have hjm := (Finset.mem_filter.mp hj).1
            have hjle := le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hj).2)
            have hcast : ((j-i : ℕ) : ℝ) = (j : ℝ)-(i : ℝ) := Nat.cast_sub hjle
            have hd : ((j-i : ℕ) : ℝ) ≤ 1+|t i-t j| := by
              rw [hcast]
              linarith [(ht j hjm).1,(ht i hi).2,neg_le_abs (t i-t j)]
            dsimp [f]
            rw [← one_div, ← div_eq_mul_inv]
            apply (div_le_div_iff₀ (by positivity) (by positivity)).2
            nlinarith [abs_nonneg (t i-t j)]
          _ = 2*∑ j ∈ sr, f (j-i) := (Finset.mul_sum _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hrbound (by norm_num)
      have hsplit : (∑ j ∈ sl, (1+|t i-t j|)⁻¹) +
          (∑ j ∈ sr, (1+|t i-t j|)⁻¹) = ∑ j ∈ s, (1+|t i-t j|)⁻¹ :=
        Finset.sum_filter_add_sum_filter_not _ _ _
      change _ ≤ 4 * ∑ k ∈ Finset.range N, f k
      linarith
    have harmonicBound : ∀ N : ℕ, (∑ k ∈ Finset.range N, (1+(k : ℝ))⁻¹) ≤ 1 + Real.log N := by
      intro N
      have h := harmonic_le_one_add_log N
      simpa [harmonic, add_comm] using h
    intro N c a b hab
    classical
    let f : Fin N → ℝ → ℂ := fun i t =>
      Complex.exp (((t*Real.log (((i:ℕ):ℝ)+1) : ℝ) : ℂ)*Complex.I)
    have he (x y : ℝ) :
        Complex.exp ((x:ℂ)*Complex.I) * star (Complex.exp ((y:ℂ)*Complex.I)) =
        Complex.exp (((x-y:ℝ):ℂ)*Complex.I) := by
      change Complex.exp ((x:ℂ)*Complex.I) * (starRingEnd ℂ) (Complex.exp ((y:ℂ)*Complex.I)) = _
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
      ring
    have hker (i j : Fin N) :
        ‖∫ t in a..b, f i t * star (f j t)‖ ≤
        (if i=j then b-a else 0) + 4*(N:ℝ)*(1+|((i:ℕ):ℝ)-((j:ℕ):ℝ)|)⁻¹ := by
      dsimp only [f]
      simp_rw [he, ← mul_sub]
      by_cases hij : i=j
      · subst j
        simp only [sub_self, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
          intervalIntegral.integral_const, if_pos rfl, abs_zero, add_zero, inv_one, mul_one]
        rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)]
        simp only [ite_true]
        linarith [Nat.cast_nonneg (α := ℝ) N]
      · have hij' : (i:ℕ) ≠ (j:ℕ) := fun h => hij (Fin.ext h)
        have hl : Real.log (((i:ℕ):ℝ)+1)-Real.log (((j:ℕ):ℝ)+1) ≠ 0 := by
          intro hh
          have heq := Real.log_injOn_pos (by positivity : 0 < ((i:ℕ):ℝ)+1)
            (by positivity : 0 < ((j:ℕ):ℝ)+1) (sub_eq_zero.mp hh)
          apply hij'
          exact_mod_cast (by linarith : ((i:ℕ):ℝ) = ((j:ℕ):ℝ))
        have h := (phase a b _ hl).trans (logOff N i j i.isLt j.isLt hij')
        simpa only [if_neg hij, zero_add, div_eq_mul_inv] using h
    have hrow (i : Fin N) :
        ∑ j : Fin N, (1+|((i:ℕ):ℝ)-((j:ℕ):ℝ)|)⁻¹ ≤ 4*(1+Real.log N) := by
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (1+|((i:ℕ):ℝ)-(j:ℝ)|)⁻¹) N]
      have hh := row N (Finset.range N) (fun n => (n:ℝ)) 0
        (Finset.Subset.refl _) (by intro j hj; constructor <;> linarith)
        i (Finset.mem_range.mpr i.isLt)
      exact hh.trans (mul_le_mul_of_nonneg_left (harmonicBound N) (by norm_num))
    have h := meanGram (Fin N) f (fun i => c i) a b ((b-a)+16*(N:ℝ)*(1+Real.log N))
      hab (by intro i; dsimp [f]; fun_prop) (by
        intro i
        calc
          _ ≤ ∑ j : Fin N, ((if i=j then b-a else 0) +
              4*(N:ℝ)*(1+|((i:ℕ):ℝ)-((j:ℕ):ℝ)|)⁻¹) :=
            Finset.sum_le_sum (fun j _ => hker i j)
          _ = (b-a)+4*(N:ℝ)*(∑ j : Fin N, (1+|((i:ℕ):ℝ)-((j:ℕ):ℝ)|)⁻¹) := by
            rw [Finset.sum_add_distrib]
            simp [← Finset.mul_sum]
          _ ≤ _ := by
            nlinarith [mul_le_mul_of_nonneg_left (hrow i) (by positivity : 0 ≤ 4*(N:ℝ))])
    have hsum (t : ℝ) :
        (∑ i : Fin N, c i * f i t) =
        ∑ n ∈ Finset.range N, c n * Complex.exp (((t*Real.log ((n:ℝ)+1):ℝ):ℂ)*Complex.I) := by
      exact Fin.sum_univ_eq_sum_range (fun n : ℕ => c n * Complex.exp (((t*Real.log ((n:ℝ)+1):ℝ):ℂ)*Complex.I)) N
    have hnorm : (∑ i : Fin N, ‖c i‖^2) = ∑ n ∈ Finset.range N, ‖c n‖^2 :=
      Fin.sum_univ_eq_sum_range (fun n : ℕ => ‖c n‖^2) N
    simpa only [hsum, hnorm] using h
  have reindex : ∀ (α : Type) [AddCommMonoid α] (N : ℕ) (F : Finset ℕ) (g : ℕ → α),
 F ⊆ Finset.Icc 1 N →
 (∑ n ∈ Finset.range N, if n+1 ∈ F then g (n+1) else 0) = ∑ n ∈ F, g n := by
    intro α _ N F g hF
    classical
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun n _ => n+1)
    · intro n hn
      exact (Finset.mem_filter.mp hn).2
    · intro n hn m hm hnm
      omega
    · intro n hn
      have hb := Finset.mem_Icc.mp (hF hn)
      refine ⟨n-1, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_range.mpr (by omega)
        · simpa only [Nat.sub_add_cancel hb.1] using hn
      · omega
    · intro n hn
      rfl
  intro N F c a b hF hab
  classical
  let g : ℕ → ℂ := fun n => if n+1 ∈ F then c (n+1) else 0
  have hs (t : ℝ) :
      (∑ n ∈ Finset.range N, g n * Complex.exp (((t*Real.log ((n:ℝ)+1):ℝ):ℂ)*Complex.I)) =
      ∑ n ∈ F, c n * Complex.exp (((t*Real.log (n:ℝ):ℝ):ℂ)*Complex.I) := by
    simpa only [g, ite_mul, zero_mul, Nat.cast_add, Nat.cast_one] using
      reindex ℂ N F (fun n => c n * Complex.exp (((t*Real.log (n:ℝ):ℝ):ℂ)*Complex.I)) hF
  have hn : (∑ n ∈ Finset.range N, ‖g n‖^2) = ∑ n ∈ F, ‖c n‖^2 := by
    simpa only [g, apply_ite norm, norm_zero, ite_pow, zero_pow (by norm_num : (2:ℕ)≠0)] using
      reindex ℝ N F (fun n => ‖c n‖^2) hF
  have h := meanSquareRange N g a b hab
  rw [hn] at h
  simp_rw [hs] at h
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact h

end Green64Analytic.Correlation

end

/-! ## SourceActualFourCollapseMeanSquare -/

section

open MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 8000000
namespace Green64Analytic.CorrelationMellin

def sourceFourTuple (z : (ℕ × ℕ) × (ℕ × ℕ)) : Fin 4 → ℕ :=
  ![z.1.1,z.1.2,z.2.1,z.2.2]

theorem sourceFourTuple_injective : Function.Injective sourceFourTuple := by
  intro z w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [sourceFourTuple, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3
  exact Prod.ext (Prod.ext h0 h1) (Prod.ext h2 h3)

theorem sourceFourTuple_prod (z : (ℕ × ℕ) × (ℕ × ℕ)) :
    (∏ i, sourceFourTuple z i) = sourceActualFourDyadProduct z := by
  simp [sourceFourTuple, Fin.prod_univ_succ, sourceActualFourDyadProduct, mul_assoc]

noncomputable def sourceFourCollapseSupport (Z : Finset (Fin 4 → ℕ)) : Finset ℕ :=
  Z.image (fun v => ∏ i, v i)
noncomputable def sourceFourCollapseCoeff
    (Z : Finset (Fin 4 → ℕ)) (coeff : Fin 4 → ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ v ∈ Z.filter (fun v => ∏ i, v i = n),
    ∏ i, coeff i (v i) / (v i : ℂ)
noncomputable def sourceFourCollapseAt
    (Z : Finset (Fin 4 → ℕ)) (coeff : Fin 4 → ℕ → ℂ)
    (cutoff : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ sourceFourCollapseSupport Z,
    (cutoff n * sourceFourCollapseCoeff Z coeff n) * sourcePhase n t

theorem source_four_collapse_sum
    (Z : Finset (Fin 4 → ℕ)) (coeff : Fin 4 → ℕ → ℂ)
    (cutoff : ℕ → ℂ) (t : ℝ) :
    sourceFourCollapseAt Z coeff cutoff t =
      ∑ v ∈ Z, cutoff (∏ i, v i) *
        (∏ i, coeff i (v i) / (v i : ℂ)) * sourcePhase (∏ i, v i) t := by
  classical
  simp only [sourceFourCollapseAt, sourceFourCollapseCoeff, sourceFourCollapseSupport,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_filter, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have hImage : (∏ i, v i) ∈ Z.image (fun u => ∏ i, u i) :=
    Finset.mem_image.mpr ⟨v,hv,rfl⟩
  simp only [Finset.sum_ite_eq]
  rw [if_pos hImage]

noncomputable def sourceFourActualCoeff
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ) :
    Fin 4 → ℕ → ℂ :=
  ![(fun m => alpha m * chi m * sourcePhase m sigma0), bs,
    (fun p => bp p * sourcePhase p sigma1), d]

theorem source_four_actual_collapse_exact
    (small long R : Finset ℕ) (a b : ℕ)
    (cutoff alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 t : ℝ)
    (ha : 1 ≤ a) (hs : ∀ ps ∈ small, 0 < ps)
    (hp : ∀ p ∈ long, 0 < p) (hr : ∀ r ∈ R, 0 < r) :
    sourceFourCollapseAt
      ((sourceActualFourDyadTuples small long R a b).image sourceFourTuple)
      (sourceFourActualCoeff alpha bs bp d chi sigma0 sigma1) cutoff t =
    sourceActualSmoothFourDyadAt small long R a b
      cutoff alpha bs bp d chi sigma0 sigma1 t := by
  classical
  rw [source_four_collapse_sum, Finset.sum_image sourceFourTuple_injective.injOn]
  unfold sourceActualSmoothFourDyadAt
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hzMS,hzPR⟩ := Finset.mem_product.mp hz
  obtain ⟨hm,hps⟩ := Finset.mem_product.mp hzMS
  obtain ⟨hp',hr'⟩ := Finset.mem_product.mp hzPR
  have hmPos : 0 < z.1.1 :=
    lt_of_lt_of_le (by omega : 0 < a) (Finset.mem_Icc.mp hm).1
  have hsPos := hs z.1.2 hps
  have hpPos := hp z.2.1 hp'
  have hrPos := hr z.2.2 hr'
  rw [sourceFourTuple_prod]
  unfold sourceActualFourDyadProduct
  rw [sourcePhase_mul (z.1.1*z.1.2*z.2.1) z.2.2
    (by positivity) hrPos t,
    sourcePhase_mul (z.1.1*z.1.2) z.2.1 (by positivity) hpPos t,
    sourcePhase_mul z.1.1 z.1.2 hmPos hsPos t]
  simp only [sourceFourActualCoeff, sourceFourTuple,
    Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one, sourceActualFourDyadLiteralTerm,
    sourcePhase_add, div_eq_mul_inv]
  ring

/-- Unrestricted centered/translated mean square of the ACTUAL four factors,
including arbitrary bounded product cutoff and every convolution multiplicity.
The fourth-factor divisor moment is fixed order: exponent 64. -/
theorem source_four_collapsed_cutoff_mean_square
    (Z : Finset (Fin 4 → ℕ)) (coeff : Fin 4 → ℕ → ℂ)
    (cutoff : ℕ → ℂ) (A : Fin 4 → ℝ) (eps U t0 t1 : ℝ) (N : ℕ)
    (hA : ∀ i, 0 ≤ A i) (hEps : 0 ≤ eps) (hU : 0 < U)
    (hF : sourceFourCollapseSupport Z ⊆ Finset.Icc 1 N)
    (hLow : ∀ n ∈ sourceFourCollapseSupport Z, U ≤ (n:ℝ))
    (hCoeff : ∀ v ∈ Z, ∀ i, ‖coeff i (v i)‖ ≤ A i)
    (hCut : ∀ n ∈ sourceFourCollapseSupport Z, ‖cutoff n‖ ≤ eps)
    (ht : t0 ≤ t1) :
    (∫ t in Set.Icc t0 t1, ‖sourceFourCollapseAt Z coeff cutoff t‖^2) ≤
      ((t1-t0)+16*(N:ℝ)*(1+Real.log N)) *
        (eps^2*((∏ i, A i)^2/U*(1+Real.log N)^64)) := by
  have hMass := Green64Analytic.Correlation.collapsedCoefficientMass
    N 3 (sourceFourCollapseSupport Z) Z coeff A U
    hA hU hF hLow hCoeff
  have hMass' :
      (∑ n ∈ sourceFourCollapseSupport Z,
        ‖cutoff n * sourceFourCollapseCoeff Z coeff n‖^2) ≤
      eps^2*((∏ i, A i)^2/U*(1+Real.log N)^64) := by
    calc
      _ ≤ ∑ n ∈ sourceFourCollapseSupport Z,
          eps^2*‖sourceFourCollapseCoeff Z coeff n‖^2 := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (norm_nonneg _) hEps).mpr (hCut n hn)) (sq_nonneg _)
      _ = eps^2*(∑ n ∈ sourceFourCollapseSupport Z,
          ‖sourceFourCollapseCoeff Z coeff n‖^2) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hMass (sq_nonneg eps)
  have hMV := Green64Analytic.Correlation.continuousMeanSquare
    N (sourceFourCollapseSupport Z)
    (fun n => cutoff n * sourceFourCollapseCoeff Z coeff n)
    t0 t1 hF ht
  have hLog : 0 ≤ Real.log (N:ℝ) := by
    by_cases hN : N = 0
    · simp [hN]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN)
  have hMult : 0 ≤ (t1-t0)+16*(N:ℝ)*(1+Real.log N) := by positivity
  have hPoly (t : ℝ) :
      sourceFourCollapseAt Z coeff cutoff t =
      ∑ n ∈ sourceFourCollapseSupport Z,
        (cutoff n * sourceFourCollapseCoeff Z coeff n) *
          Complex.exp (((t*Real.log (n:ℝ):ℝ):ℂ)*Complex.I) := by
    unfold sourceFourCollapseAt
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    unfold sourcePhase
    rw [mul_comm]
  simp_rw [← hPoly] at hMV
  exact hMV.trans (mul_le_mul_of_nonneg_left hMass' hMult)
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualSmoothFourDyadMeanSquare -/

section

open MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 8000000
namespace Green64Analytic.CorrelationMellin

/-- Actual dyadic source cutoff mean square, with a fully explicit error
constant and fixed fourth-convolution divisor moment. -/
theorem source_actual_smooth_fourdyad_mean_square
    (small long R : Finset ℕ) (a b M0 P P0 R0 : ℕ)
    (cutoff alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 t0 t1 : ℝ)
    (Am Cs Ap Ar eps : ℝ)
    (ha : 1 ≤ a) (hM0 : 1 ≤ M0) (hP : 1 ≤ P)
    (hP0 : 1 ≤ P0) (hR0 : 1 ≤ R0)
    (hAm : 0 ≤ Am) (hCs : 0 ≤ Cs) (hAp : 0 ≤ Ap)
    (hAr : 0 ≤ Ar) (hEps : 0 ≤ eps)
    (hM : Finset.Icc a b ⊆ Finset.Icc M0 (2*M0))
    (hSmall : small ⊆ Finset.Icc P (2*P))
    (hLong : long ⊆ Finset.Icc P0 (2*P0))
    (hR : R ⊆ Finset.Icc R0 (2*R0))
    (hAlpha : ∀ m ∈ Finset.Icc a b, ‖alpha m‖ ≤ Am)
    (hBs : ∀ ps ∈ small, ‖bs ps‖ ≤ Cs)
    (hBp : ∀ p ∈ long, ‖bp p‖ ≤ Ap)
    (hd : ∀ r ∈ R, ‖d r‖ ≤ Ar)
    (hCut : ∀ w : ℕ, ‖cutoff w‖ ≤ eps)
    (ht : t0 ≤ t1) :
    let U : ℝ := ((M0*P*P0*R0:ℕ):ℝ)
    let N : ℕ := (2*M0)*(2*P)*(2*P0)*(2*R0)
    (∫ t in Set.Icc t0 t1, ‖sourceActualSmoothFourDyadAt
        small long R a b cutoff alpha bs bp d chi sigma0 sigma1 t‖^2) ≤
      ((t1-t0)+16*(N:ℝ)*(1+Real.log N)) *
        (eps^2*((Am*Cs*Ap*Ar)^2/U*(1+Real.log N)^64)) := by
  classical
  let U : ℝ := ((M0*P*P0*R0:ℕ):ℝ)
  let N : ℕ := (2*M0)*(2*P)*(2*P0)*(2*R0)
  let Z := (sourceActualFourDyadTuples small long R a b).image sourceFourTuple
  let coeff := sourceFourActualCoeff alpha bs bp d chi sigma0 sigma1
  let A : Fin 4 → ℝ := ![Am,Cs,Ap,Ar]
  have hU : 0 < U := by dsimp [U]; positivity
  have hA : ∀ i, 0 ≤ A i := by intro i; fin_cases i <;> assumption
  have hCoords (v : Fin 4 → ℕ) (hv : v ∈ Z) :
      v 0 ∈ Finset.Icc a b ∧ v 1 ∈ small ∧ v 2 ∈ long ∧ v 3 ∈ R := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hzMS,hzPR⟩ := Finset.mem_product.mp hz
    obtain ⟨hm,hps⟩ := Finset.mem_product.mp hzMS
    obtain ⟨hp,hr⟩ := Finset.mem_product.mp hzPR
    simpa only [sourceFourTuple, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] using And.intro hm (And.intro hps (And.intro hp hr))
  have hBounds (n : ℕ) (hn : n ∈ sourceFourCollapseSupport Z) :
      M0*P*P0*R0 ≤ n ∧ n ≤ N := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hm,hps,hp,hr⟩ := hCoords v hv
    have hm' := Finset.mem_Icc.mp (hM hm)
    have hps' := Finset.mem_Icc.mp (hSmall hps)
    have hp' := Finset.mem_Icc.mp (hLong hp)
    have hr' := Finset.mem_Icc.mp (hR hr)
    have hProd : (∏ i, v i) = v 0 * v 1 * v 2 * v 3 := by
      simp [Fin.prod_univ_succ, mul_assoc]
    rw [hProd]
    constructor
    · gcongr <;> omega
    · dsimp [N]; gcongr <;> omega
  have hF : sourceFourCollapseSupport Z ⊆ Finset.Icc 1 N := by
    intro n hn
    have hh := hBounds n hn
    apply Finset.mem_Icc.mpr
    exact ⟨Nat.succ_le_iff.mpr (lt_of_lt_of_le
      (by positivity : 0 < M0*P*P0*R0) hh.1),hh.2⟩
  have hLow : ∀ n ∈ sourceFourCollapseSupport Z, U ≤ (n:ℝ) := by
    intro n hn
    dsimp [U]
    exact_mod_cast (hBounds n hn).1
  have hCoeff : ∀ v ∈ Z, ∀ i, ‖coeff i (v i)‖ ≤ A i := by
    intro v hv i
    obtain ⟨hm,hps,hp,hr⟩ := hCoords v hv
    fin_cases i
    · change ‖alpha (v 0) * chi (v 0) * sourcePhase (v 0) sigma0‖ ≤ Am
      simp only [norm_mul,sourcePhase_norm,mul_one]
      calc
        _ ≤ ‖alpha (v 0)‖*1 :=
          mul_le_mul_of_nonneg_left (chi.norm_le_one (v 0 : ZMod q)) (norm_nonneg _)
        _ ≤ Am := by simpa using hAlpha _ hm
    · exact hBs _ hps
    · change ‖bp (v 2) * sourcePhase (v 2) sigma1‖ ≤ Ap
      simpa only [norm_mul, sourcePhase_norm, mul_one] using hBp _ hp
    · exact hd _ hr
  have hsPos : ∀ ps ∈ small, 0 < ps := by
    intro ps hps; have hh := (Finset.mem_Icc.mp (hSmall hps)).1; omega
  have hpPos : ∀ p ∈ long, 0 < p := by
    intro p hp; have hh := (Finset.mem_Icc.mp (hLong hp)).1; omega
  have hrPos : ∀ r ∈ R, 0 < r := by
    intro r hr; have hh := (Finset.mem_Icc.mp (hR hr)).1; omega
  have hMV := source_four_collapsed_cutoff_mean_square
    Z coeff cutoff A eps U t0 t1 N
    hA hEps hU hF hLow hCoeff (fun n hn => hCut n) ht
  have hExact (t : ℝ) :
      sourceFourCollapseAt Z coeff cutoff t =
        sourceActualSmoothFourDyadAt small long R a b
          cutoff alpha bs bp d chi sigma0 sigma1 t :=
    source_four_actual_collapse_exact small long R a b
      cutoff alpha bs bp d chi sigma0 sigma1 t ha hsPos hpPos hrPos
  simp_rw [hExact] at hMV
  simpa only [A,U,N, Fin.prod_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one, mul_assoc] using hMV
end Green64Analytic.CorrelationMellin

end

