module

public import Green64.Library.Sieve.Foundations.Part020
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Green64.Library.Weights.Part111
public import Green64.Library.Sieve.Foundations.Part019
public import Green64.Library.Correlation.Part001
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-!
# Sieve / Foundations / Part021

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistorical3DFourierDerivativeEnvelope -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Explicit source-side finite derivative-integral budget for the
original Parity (4.14) real 3D pulled-back ETA cutoff, for arbitrary
frequency-polynomial order N. The FINITE number of integrals involves
only derivatives 0,...,N of the original source cutoff itself.
It has no hidden Fourier dependence or unverified periodicity. -/
def parityOriginal3DSourceDerivativeIntegralBudget434
    (N : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) : ℝ :=
  (2:ℝ)^N *
    (∑ p ∈ Finset.range 1 ×ˢ Finset.range (N+1),
      ∫ v : EuclideanSpace ℝ (Fin 3),
        ‖v‖^p.1 * ‖iteratedFDeriv ℝ p.2 (f : EuclideanSpace ℝ (Fin 3) → ℂ) v‖)

/-- Entire actual finite derivative-integral budget is nonnegative:
the original R^3 Lebesgue integrands are norms, not signed Fourier
correlations that could cancel. -/
theorem parity_original_3d_source_derivative_integral_budget_nonneg434
    (N : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) :
    0 ≤ parityOriginal3DSourceDerivativeIntegralBudget434 N f := by
  unfold parityOriginal3DSourceDerivativeIntegralBudget434
  apply mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) _)
  apply Finset.sum_nonneg
  intro p hp
  exact integral_nonneg (fun v => mul_nonneg
    (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))

/-- Native original three-dimensional Schwartz Fourier transform has
polynomial frequency-weight order N bounded by a FINITE list of
actual source derivatives, rather than an abstract unspecified
Fourier-tail constant. Constants 2^N and integrability are native
Mathlib and independent of L,k,Z. -/
theorem parity_original_3d_source_derivative_integral_fourier_le434
    (N : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖ξ‖^N * ‖(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ‖ ≤
      parityOriginal3DSourceDerivativeIntegralBudget434 N f := by
  have hF := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (f := (f : EuclideanSpace ℝ (Fin 3) → ℂ))
    (K := ⊤) (N := ⊤) (hf := f.smooth ⊤)
    (h'f := fun k n _ _ => f.integrable_pow_mul_iteratedFDeriv volume k n)
    (k := 0) (n := N) (by simp) (by simp) ξ
  have hCoe : (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ =
      (𝓕 (f : EuclideanSpace ℝ (Fin 3) → ℂ)) ξ := by
    exact congrFun (SchwartzMap.fourier_coe f) ξ
  rw [hCoe]
  simpa only [parityOriginal3DSourceDerivativeIntegralBudget434,
    norm_iteratedFDeriv_zero, pow_zero, one_mul, zero_mul,
    zero_add, Nat.zero_add, Nat.cast_zero, Nat.cast_mul,
    mul_zero, zero_mul, mul_one] using hF

/-- EXACT source Fourier Schwartz seminorm of order (N,0) is bounded
by a FINITE original source derivative integral budget. This is the
precise bridge needed to replace a postulated 3D Fourier moment bound
by the still-open quantitative SOURCE derivative estimate. -/
theorem parity_original_3d_source_fourier_seminorm_le_derivative_integral434
    (N : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) :
    (SchwartzMap.seminorm ℂ N 0)
      (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ≤
    parityOriginal3DSourceDerivativeIntegralBudget434 N f := by
  apply SchwartzMap.seminorm_le_bound ℂ N 0 _
    (parity_original_3d_source_derivative_integral_budget_nonneg434 N f)
  intro ξ
  simpa only [norm_iteratedFDeriv_zero] using
    parity_original_3d_source_derivative_integral_fourier_le434 N f ξ
end Green64Analytic.Parity

end

end

/-! ## OriginalHistorical3DFourierSourceSeminorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The exact 3D Lebesgue geometric constant from native Mathlib
Schwartz integrability, fixed once for all source L,k,U,E,V,Z. -/
def parityOriginal3DSourceGeometricConstant434 : ℝ :=
  (2:ℝ)^((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower) *
    (∫ x : EuclideanSpace ℝ (Fin 3),
      (1+‖x‖)^(-((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℝ)))

/-- The explicit source derivative Fourier envelope expressed in
ONLY ORIGINAL source Schwartz seminorms before the Fourier
transform. The finite derivative budget uses exactly j≤N on the
source pulled-back η_eη_n, with one fixed Euclidean dimension
parameter, not a hidden L-dependent Fourier norm. -/
def parityOriginal3DSourceFiniteSeminormBudget434
    (N : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) : ℝ :=
  (2:ℝ)^N * parityOriginal3DSourceGeometricConstant434 *
    ∑ j ∈ Finset.range (N+1),
      ((SchwartzMap.seminorm ℂ 0 j) f +
       (SchwartzMap.seminorm ℂ
         (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower j) f)

/-- Every source 3D Fréchet derivative integral is explicitly
bounded by TWO Schwartz seminorms of the ORIGINAL physical source
cutoff and ONE fixed geometric constant. -/
theorem parity_original_3d_source_derivative_integral_le_two_seminorms434
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) (j : ℕ) :
    (∫x : EuclideanSpace ℝ (Fin 3),
      ‖iteratedFDeriv ℝ j (f : EuclideanSpace ℝ (Fin 3) → ℂ) x‖) ≤
      parityOriginal3DSourceGeometricConstant434 *
        ((SchwartzMap.seminorm ℂ 0 j) f+
         (SchwartzMap.seminorm ℂ
           (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower j) f) := by
  have h := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ volume f 0 j
  simpa only [parityOriginal3DSourceGeometricConstant434,pow_zero,one_mul,zero_add] using h

/-- The ACTUAL original 3D Fourier derivative L1 bound is controlled
by finitely many Schwartz seminorms OF THE SOURCE CUTOFF itself;
no unproved high-frequency estimate or large sieve is being used.
This is the relevant quantitative decomposition for proving
M_H(L,k,Z) polynomial from moving η_e derivative estimates. -/
theorem parity_original_3d_source_derivative_envelope_le_seminorms434
    (N : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) :
    parityOriginal3DSourceDerivativeIntegralBudget434 N f ≤
      parityOriginal3DSourceFiniteSeminormBudget434 N f := by
  unfold parityOriginal3DSourceDerivativeIntegralBudget434
    parityOriginal3DSourceFiniteSeminormBudget434
  have hSum :
      (∑p∈ Finset.range 1 ×ˢ Finset.range (N+1),
        ∫v : EuclideanSpace ℝ (Fin 3),
          ‖v‖^p.1 * ‖iteratedFDeriv ℝ p.2
            (f : EuclideanSpace ℝ (Fin 3) → ℂ) v‖) ≤
      (∑p∈ Finset.range 1 ×ˢ Finset.range (N+1),
        parityOriginal3DSourceGeometricConstant434 *
          ((SchwartzMap.seminorm ℂ 0 p.2) f+
           (SchwartzMap.seminorm ℂ
              (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower p.2) f)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp0 : p.1=0 := by
      have ha := (Finset.mem_product.mp hp).1
      exact Nat.lt_one_iff.mp (Finset.mem_range.mp ha)
    simpa only [hp0,pow_zero,one_mul] using
      parity_original_3d_source_derivative_integral_le_two_seminorms434 f p.2
  have hSimp :
      (∑p∈ Finset.range 1 ×ˢ Finset.range (N+1),
        parityOriginal3DSourceGeometricConstant434 *
          ((SchwartzMap.seminorm ℂ 0 p.2) f+
           (SchwartzMap.seminorm ℂ
              (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower p.2) f)) =
      parityOriginal3DSourceGeometricConstant434 *
        (∑j∈Finset.range (N+1),
          ((SchwartzMap.seminorm ℂ 0 j) f+
           (SchwartzMap.seminorm ℂ
              (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower j) f)) := by
    simp [Finset.sum_product,Finset.mul_sum]
  have hPower : 0 ≤ (2:ℝ)^N := by positivity
  calc
    (2:ℝ)^N * (∑p∈Finset.range 1 ×ˢ Finset.range (N+1),
      ∫v : EuclideanSpace ℝ (Fin 3),
        ‖v‖^p.1 * ‖iteratedFDeriv ℝ p.2 (f : EuclideanSpace ℝ (Fin 3) → ℂ) v‖) ≤
      (2:ℝ)^N * (∑p∈Finset.range 1 ×ˢ Finset.range (N+1),
        parityOriginal3DSourceGeometricConstant434 *
          ((SchwartzMap.seminorm ℂ 0 p.2) f+
           (SchwartzMap.seminorm ℂ
              (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower p.2) f)) :=
      mul_le_mul_of_nonneg_left hSum hPower
    _ = _ := by rw [hSimp]; ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistorical3DSourceMomentFinite -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Exact fixed geometric R^3 constant has nonnegative sign:
no hidden sign/cancellation in the original 3D Fourier moment. -/
theorem parity_original_3d_source_geometric_constant_nonneg434 :
    0 ≤ parityOriginal3DSourceGeometricConstant434 := by
  unfold parityOriginal3DSourceGeometricConstant434
  apply mul_nonneg
    (pow_nonneg (by norm_num : (0:ℝ)≤2) _)
  exact integral_nonneg (fun x => Real.rpow_nonneg (by positivity) _)

/-- FULL REAL source-based Parity (4.15) Fourier H-moment budget using
ONLY FINITELY MANY derivatives of the input 3D Schwartz kernel,
BEFORE Fourier transformation. This is the exact remaining source
analytic contract for the moving eta_e derivative bound; not a
polynomial growth hypothesis disguised as a Fourier moment estimate. -/
def parityOriginal3DSourceMomentFiniteBudget434
    (H : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) : ℝ :=
  parityOriginal3DSourceGeometricConstant434 *
    (parityOriginal3DSourceFiniteSeminormBudget434 0 f+
     parityOriginal3DSourceFiniteSeminormBudget434
       (H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower) f)

/-- ALL original Euclidean R3 Schwartz cutoff functions have
M_H(f) controlled by an explicit FINITE real SOURCE derivative
seminorm budget. Fixed constants are from Mathlib 3D Lebesgue
geometry; every source cutoff derivative of order ≤H+dim appears
with its mathematically correct polynomial weight. -/
theorem parity_original_real_3d_fourier_moment_le_original_source_finite434
    (H : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) :
    (∫ ξ : EuclideanSpace ℝ (Fin 3),
      ‖ξ‖^H * ‖(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ‖) ≤
    parityOriginal3DSourceMomentFiniteBudget434 H f := by
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin 3)))
  let F := (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
  let P := μ.integrablePower
  let C := parityOriginal3DSourceGeometricConstant434
  have hbase := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ μ F H 0
  have hsource0 := parity_original_3d_source_fourier_seminorm_le_derivative_integral434 0 f
  have hsourceH := parity_original_3d_source_fourier_seminorm_le_derivative_integral434 (H+P) f
  have hseminorm0 := parity_original_3d_source_derivative_envelope_le_seminorms434 0 f
  have hseminormH := parity_original_3d_source_derivative_envelope_le_seminorms434 (H+P) f
  have hsum :
      (SchwartzMap.seminorm ℂ 0 0) F+
        (SchwartzMap.seminorm ℂ (H+P) 0) F ≤
      parityOriginal3DSourceFiniteSeminormBudget434 0 f+
        parityOriginal3DSourceFiniteSeminormBudget434 (H+P) f :=
    add_le_add (hsource0.trans hseminorm0) (hsourceH.trans hseminormH)
  have hC : 0≤C := parity_original_3d_source_geometric_constant_nonneg434
  have hweighted := mul_le_mul_of_nonneg_left hsum hC
  have hnrm :
    (∫ ξ : EuclideanSpace ℝ (Fin 3), ‖ξ‖^H * ‖F ξ‖) ≤
    C * ((SchwartzMap.seminorm ℂ 0 0) F+
      (SchwartzMap.seminorm ℂ (H+P) 0) F) := by
    simpa [μ,P,C,parityOriginal3DSourceGeometricConstant434,
      norm_iteratedFDeriv_zero] using hbase
  exact hnrm.trans hweighted

/-- Specialized ACTUAL historical Parity(4.14) eta_e eta_n cutoff:
its Fourier moment is bounded by finitely many seminorms of the
SOURCE-DEFINED 3D pulledback Schwartz function, without circularly
assuming an unproved source-to-Fourier smallness estimate. -/
theorem parity_original_historical_actual_3d_fourier_moment_source_finite434
    (H : ℕ) (U E V Z : ℝ) (k : ℤ)
    (buf etaE etaN : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b) :
    parityOriginalHistorical3DFourierMoment434 H U E V Z k
      buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport ≤
    parityOriginal3DSourceMomentFiniteBudget434 H
      (parityOriginalHistoricalPulledEuclidean3D434 U E V Z k
        buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) := by
  exact parity_original_real_3d_fourier_moment_le_original_source_finite434 H _
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFixedLogBuffer -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- ORIGINAL Parity §4.5 FIXED smooth logarithmic buffer REALLY EXISTS:
its support is in [-log A,log A], it equals one on the full literal
source dyadic interval [0,log 2], norm≤1, C∞, and it comes with
one uniform actual logarithmic derivative budget K_j, independent of
physical L,k,U,E,V,Z and of target precision. This is constructed
from the existing source-certified fixed eta cutoff, not assumed. -/
theorem parity_original_historical_fixed_log_buffer_exists434 :
    ∃ A : ℝ, 64≤A ∧ ∃ buf : ℝ → ℂ,
      ContDiff ℝ ∞ buf ∧
      (∀ t : ℝ, buf t ≠ 0 → -Real.log A≤t ∧ t≤Real.log A) ∧
      (∀ t ∈ Set.Icc (0:ℝ) (Real.log 2),buf t=1) ∧
      (∀ t : ℝ, ‖buf t‖≤1) ∧
      ∃ K : ℕ → ℝ, (∀ j,0≤K j) ∧
        ∀ L : ℝ, sourceLogDerivativeBudget 0 K L buf := by
  obtain ⟨A,hA,eta,hSmooth,hSupp,hOne,hNorm,hInv,hSuppInv,K,hK,hBudgets⟩ :=
    parity_fixed_rank_cutoff_pair_budget434
  let buf : ℝ → ℂ := fun t => eta (Real.exp t)
  have hApos : 0<A := by linarith
  have hLogInv : Real.log (1/A) = -Real.log A := by
    rw [one_div,Real.log_inv]
  have hSmoothBuf : ContDiff ℝ ∞ buf := hSmooth.comp Real.contDiff_exp
  have hSupportBuf : ∀ t : ℝ, buf t ≠ 0 → -Real.log A≤t ∧ t≤Real.log A := by
    intro t ht
    have hh := hSupp (Real.exp t) ht
    have hl : Real.log (1/A)≤Real.log (Real.exp t) :=
      Real.log_le_log (one_div_pos.mpr hApos) hh.1
    have hu : Real.log (Real.exp t)≤Real.log A :=
      Real.log_le_log (Real.exp_pos t) hh.2
    simpa only [hLogInv,Real.log_exp] using And.intro hl hu
  have hOneBuf : ∀ t ∈ Set.Icc (0:ℝ) (Real.log 2),buf t=1 := by
    intro t ht
    have hExpLo : (1:ℝ) ≤ Real.exp t := by
      calc
        _ = Real.exp 0 := by simp
        _ ≤ Real.exp t := Real.exp_le_exp.mpr ht.1
    have hExpHi : Real.exp t ≤ (2:ℝ) := by
      have hh := Real.exp_le_exp.mpr ht.2
      simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using hh
    have hTwo : (2:ℝ)≤64*Real.exp 2+1 := by
      have hExp : (1:ℝ)≤Real.exp 2 := by
        have hh : Real.exp (0:ℝ)≤Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
        simpa using hh
      nlinarith
    exact hOne (Real.exp t) ⟨by linarith [hExpLo],hExpHi.trans hTwo⟩
  have hNormBuf : ∀ t : ℝ, ‖buf t‖≤1 := fun t => hNorm (Real.exp t)
  refine ⟨A,hA,buf,hSmoothBuf,hSupportBuf,hOneBuf,hNormBuf,K,hK,?_⟩
  intro L
  exact (hBudgets L).1
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUnbufferedFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 17500000

/-- On ORIGINAL true dyadic source m,m'∈[U,2U], z∈[Z,2Z],
all three fixed smooth log buffers are identically one. Hence the
TRUE original eta_e(e/E)*eta_n(n/V) physical source is EXACTLY the
FULL 3D Fourier inversion of its source-derived Schwartz kernel,
WITHOUT leftover artificial buffer factors. The 2π normalization
and all physical Q/P/B509 gates are preserved. This is NOT a bound
on the multiplier moments or final TypeII. -/
theorem parity_original_historical_true_source_unbuffered_3d_fourier434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (U E V Z : ℝ) (hU : 0 < U) (hE : 0 < E)
    (hV : 0 < V) (hZ : 0 < Z)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)≤2*U)
    (hzLo : Z≤(parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ))
    (hzHi : (parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ)≤2*Z)
    (buf etaE etaN : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN)
    (hBufSupport : ∀ t : ℝ, buf t ≠ 0 → a ≤ t ∧ t ≤ b)
    (hBufOne : ∀ t ∈ Set.Icc (0:ℝ) (Real.log 2),buf t=1) :
    etaE ((e:ℝ)/E)*etaN ((n:ℝ)/V) =
      ∫ ξ : EuclideanSpace ℝ (Fin 3),
        (Complex.exp (((2*Real.pi*(ξ 0)*Real.log ((m:ℝ)/U):ℝ):ℂ)*Complex.I) *
         Complex.exp (((2*Real.pi*(ξ 1)*Real.log ((mp:ℝ)/U):ℝ):ℂ)*Complex.I) *
         Complex.exp (((2*Real.pi*(ξ 2)*Real.log
           ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ)/Z):ℝ):ℂ)*Complex.I)) *
        (𝓕 (parityOriginalHistoricalPulledEuclidean3D434
          U E V Z (parityOriginalHistoricalOffdiagK434 e m mp)
          buf etaE etaN a b hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) :
          𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ := by
  let z := parityOriginalHistoricalCanonicalZ434 e m mp n
  have hBox := parity_original_historical_log_three_coordinate_box434
    U Z m mp z hU hZ hmLo hmHi hmpLo hmpHi hzLo hzHi
  have hb0 := hBufOne (Real.log ((m:ℝ)/U)) ⟨hBox.1,hBox.2.1⟩
  have hb1 := hBufOne (Real.log ((mp:ℝ)/U)) ⟨hBox.2.2.1,hBox.2.2.2.1⟩
  have hb2 := hBufOne (Real.log ((z:ℝ)/Z)) ⟨hBox.2.2.2.2.1,hBox.2.2.2.2.2⟩
  have hSource := parity_original_historical_source_eta_real_3d_fourier_integral434
    d L band slot δ Y e m mp n he hneq hValid
    U E V Z hU hE hV hZ buf etaE etaN a b
    hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport
  rw [hb0,hb1,hb2] at hSource
  simpa only [one_mul] using hSource
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalReal3DFourierExists -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- UNCONDITIONAL smooth-auxiliary existence and real 3D Fourier
separation for the TRUE original supported Parity (4.14) eta_e*eta_n
source weight. The fixed compact dyadic buffer is CONSTRUCTED from
native source cutoffs, not postulated, and is independent of every
source e,n,m,m',k and Fourier frequency. On actual m,m',z dyads it
is exactly one, so no artificial multiplicative factor survives.
The original h=-2 source Q/P gates and 2π Fourier convention remain.

This theorem proves REAL exact Fourier inversion, not uniform moment
budget or the final complete character-correlation sum (4.17). -/
theorem parity_original_historical_true_source_3d_fourier_exists434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (U E V Z : ℝ) (hU : 0 < U) (hE : 0 < E)
    (hV : 0 < V) (hZ : 0 < Z)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)≤2*U)
    (hzLo : Z≤(parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ))
    (hzHi : (parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ)≤2*Z)
    (etaE etaN : ℝ → ℂ)
    (hEtaESmooth : ContDiff ℝ ∞ etaE)
    (hEtaNSmooth : ContDiff ℝ ∞ etaN) :
    ∃ (A : ℝ) (buf : ℝ → ℂ)
      (hBufSmooth : ContDiff ℝ ∞ buf)
      (hBufSupport : ∀ t : ℝ, buf t ≠ 0 →
        -Real.log A≤t ∧ t≤Real.log A),
      64≤A ∧
      etaE ((e:ℝ)/E)*etaN ((n:ℝ)/V) =
        ∫ ξ : EuclideanSpace ℝ (Fin 3),
          (Complex.exp (((2*Real.pi*(ξ 0)*Real.log ((m:ℝ)/U):ℝ):ℂ)*Complex.I) *
           Complex.exp (((2*Real.pi*(ξ 1)*Real.log ((mp:ℝ)/U):ℝ):ℂ)*Complex.I) *
           Complex.exp (((2*Real.pi*(ξ 2)*Real.log
             ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ)/Z):ℝ):ℂ)*Complex.I)) *
          (𝓕 (parityOriginalHistoricalPulledEuclidean3D434
            U E V Z (parityOriginalHistoricalOffdiagK434 e m mp)
            buf etaE etaN (-Real.log A) (Real.log A)
            hBufSmooth hEtaESmooth hEtaNSmooth hBufSupport) :
            𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ := by
  obtain ⟨A,hA,buf,hBSmooth,hBSupp,hBOne,hBNorm,K,hK,hBudgets⟩ :=
    parity_original_historical_fixed_log_buffer_exists434
  refine ⟨A,buf,hBSmooth,hBSupp,hA,?_⟩
  exact parity_original_historical_true_source_unbuffered_3d_fourier434
    d L band slot δ Y e m mp n he hneq hValid
    U E V Z hU hE hV hZ hmLo hmHi hmpLo hmpHi hzLo hzHi
    buf etaE etaN (-Real.log A) (Real.log A)
    hBSmooth hEtaESmooth hEtaNSmooth hBSupp hBOne
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFourier3DFrequency -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- In genuine Euclidean R^3, every individual original Fourier
coordinate has absolute value at most the ambient Euclidean norm.
No coordinatewise sup norm is substituted for the real Schwartz
Fourier convention. -/
theorem parity_original_real_3d_fourier_coordinate_le_norm434
    (ξ : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    |ξ i| ≤ ‖ξ‖ := by
  simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le ξ i)

/-- The manuscript uses e^(i ξ log m); Mathlib's genuine Fourier
transform uses 2πξ. The actual frequency budget pays exactly ONE
fixed power of L for 2π (since π<4 and L≥8). This is a source-
faithful frequency normalization for Parity (4.17), not forgetting 2π. -/
theorem parity_original_real_3d_fourier_frequency_budget434
    (L Cf : ℝ) (hL : 8≤L)
    (ξ : EuclideanSpace ℝ (Fin 3))
    (hξ : ‖ξ‖ ≤ L^Cf) (i : Fin 3) :
    |2*Real.pi*(ξ i)| ≤ L^(Cf+1) := by
  have hLp : 0<L := by linarith
  have hPi : 0≤2*Real.pi := by positivity
  have h2Pi : 2*Real.pi ≤ L := by
    have hp := Real.pi_le_four
    linarith
  have hξi : |ξ i| ≤ L^Cf :=
    (parity_original_real_3d_fourier_coordinate_le_norm434 ξ i).trans hξ
  have hProd : (2*Real.pi)*|ξ i| ≤ L*(L^Cf) := by
    exact mul_le_mul h2Pi hξi (abs_nonneg _) (by positivity)
  have hpow : L*(L^Cf)=L^(Cf+1) := by
    rw [Real.rpow_add hLp, Real.rpow_one]
    ring
  calc
    _ = (2*Real.pi)*|ξ i| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),
        abs_of_nonneg Real.pi_pos.le]
    _ ≤ L*(L^Cf) := hProd
    _ = L^(Cf+1) := hpow

/-- Simultaneously verifies the frequency range needed for each of
the THREE genuine original m,m',z Fourier phases in the native signed
Parity (4.17) theorem, on the actual Euclidean 3D frequency ball. -/
theorem parity_original_real_3d_all_parity417_frequency_budgets434
    (L Cf : ℝ) (hL : 8≤L)
    (ξ : EuclideanSpace ℝ (Fin 3)) (hξ : ‖ξ‖≤L^Cf) :
    |2*Real.pi*(ξ 0)|≤L^(Cf+1) ∧
    |2*Real.pi*(ξ 1)|≤L^(Cf+1) ∧
    |2*Real.pi*(ξ 2)|≤L^(Cf+1) :=
  ⟨parity_original_real_3d_fourier_frequency_budget434 L Cf hL ξ hξ 0,
   parity_original_real_3d_fourier_frequency_budget434 L Cf hL ξ hξ 1,
   parity_original_real_3d_fourier_frequency_budget434 L Cf hL ξ hξ 2⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPullbackCoeffBudget -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- A genuine nonzero historical integer k has |k|>=1 in the real
normalizations of both Parity (4.14) pulledback arguments. In particular
there is no hidden k^-1 singularity on actual source k!=0 fibres. -/
theorem parity_original_nonzero_integer_k_abs_ge_one434
    (k : ℤ) (hk : k≠0) : (1:ℝ) ≤ |(k:ℝ)| := by
  have hnat : 1≤k.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hk)
  have hnatR : (1:ℝ)≤(k.natAbs:ℝ) := by exact_mod_cast hnat
  have heq : (k.natAbs:ℝ)=|(k:ℝ)| := by
    have ht := congrArg (fun x : ℤ => (x : ℝ)) (Int.natCast_natAbs k)
    simpa only [Int.cast_natCast, Int.cast_abs] using ht
  rwa [heq] at hnatR

/-- EXACT h=-2 ORIGINAL Parity (4.14) coefficient U/(kE) has
absolute value <= L^K0 when E=U L^-K0, k!=0. This applies for
positive and negative k with NO error or ignored phase. -/
theorem parity_original_historical_eta_e_parameter_polylog434
    (L U E K0 : ℝ) (k : ℤ)
    (hL : 0<L) (hU : 0<U) (hE : E=U*L^(-K0)) (hk : k≠0) :
    |U/((k:ℝ)*E)| ≤ L^K0 := by
  have hkpos : (0:ℝ) < |(k:ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have hkone := parity_original_nonzero_integer_k_abs_ge_one434 k hk
  have hkreal : (k:ℝ)≠0 := by exact_mod_cast hk
  have hKpow : 0<L^K0 := Real.rpow_pos_of_pos hL _
  have hEq : U/((k:ℝ)*E)=L^K0/(k:ℝ) := by
    rw [hE,Real.rpow_neg hL.le]
    field_simp [hkreal,hU.ne',hKpow.ne']
  rw [hEq,abs_div,abs_of_pos hKpow]
  apply (div_le_iff₀ hkpos).mpr
  calc
    _ = (1:ℝ)*L^K0 := by ring
    _ ≤ |(k:ℝ)| *L^K0 :=
      mul_le_mul_of_nonneg_right hkone hKpow.le
    _ = L^K0*|(k:ℝ)| := by ring

/-- Parity's second 3D pulledback coefficient Z/(kUV) is polynomial
in L on the REAL ORIGINAL source physical dyads when UV>=exp L and
Z<=4exp L L^(K0+88). No k or Z loss is hidden in an unspecified
constant: its exact bound is 4 L^(K0+88). -/
theorem parity_original_historical_eta_n_parameter_polylog434
    (L U V Z K0 : ℝ) (k : ℤ)
    (hL : 0<L) (hU : 0<U) (hV : 0<V) (hk : k≠0)
    (hUV : Real.exp L≤U*V)
    (hZpos : 0≤Z) (hZ : Z≤4*Real.exp L*L^(K0+88)) :
    |Z/((k:ℝ)*U*V)| ≤ 4*L^(K0+88) := by
  have hkpos : (0:ℝ) < |(k:ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have hkone := parity_original_nonzero_integer_k_abs_ge_one434 k hk
  have hp := Real.rpow_pos_of_pos hL (K0+88)
  have hUVpos : 0<U*V := mul_pos hU hV
  have hdenpos : (0:ℝ) < |(k:ℝ)| *U*V := by positivity
  have hden : Real.exp L ≤ |(k:ℝ)| *U*V := by
    calc
      _ ≤ U*V := hUV
      _ = (1:ℝ)*(U*V) := by ring
      _ ≤ |(k:ℝ)| *(U*V) := mul_le_mul_of_nonneg_right hkone hUVpos.le
      _ = |(k:ℝ)| *U*V := by ring
  rw [abs_div,abs_mul,abs_mul,abs_of_nonneg hZpos,
    abs_of_pos hU,abs_of_pos hV]
  apply (div_le_iff₀ hdenpos).mpr
  calc
    _ ≤ 4*Real.exp L*L^(K0+88) := hZ
    _ = (4*L^(K0+88))*Real.exp L := by ring
    _ ≤ (4*L^(K0+88))*(|(k:ℝ)| *U*V) := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ = (4*L^(K0+88))*(|(k:ℝ)| *U*V) := rfl

/-- The third original 4.14 coefficient 2/(UV) is uniformly <=1
on source physical dyads UV>=exp L, L>=8. It is nonnegative. -/
theorem parity_original_historical_eta_n_shift_parameter_le_one434
    (L U V : ℝ) (hL : 8≤L) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) :
    0≤2/(U*V) ∧ 2/(U*V)≤1 := by
  have hUVpos : 0<U*V := mul_pos hU hV
  have hExpLo : (2:ℝ)≤Real.exp L := by
    have hh := Real.add_one_le_exp L
    linarith
  constructor
  · exact div_nonneg (by norm_num) hUVpos.le
  · apply (div_le_iff₀ hUVpos).mpr
    linarith
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualDyadicZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The genuine original Parity (4.15) binary dyadic scale attached to
physical z. The scale is defined by the real ORIGINAL integer z,
not an independently chosen Z cutoff. -/
def parityOriginalHistoricalActualZDyadicScale434 (z : ℕ) : ℕ :=
  2 ^ (Nat.log 2 z)

/-- Actual physical z>0 belongs to its EXACT source dyadic interval
Z<=z<2Z with Z=2^floor(log2 z). The original cofactor m',n and
physical Ppart are untouched, and z=0 is treated separately. -/
theorem parity_original_historical_actual_z_in_own_dyad434
    (z : ℕ) (hz : 0<z) :
    0<parityOriginalHistoricalActualZDyadicScale434 z ∧
    parityOriginalHistoricalActualZDyadicScale434 z ≤ z ∧
    z < 2*parityOriginalHistoricalActualZDyadicScale434 z := by
  unfold parityOriginalHistoricalActualZDyadicScale434
  have hpos : 0<2^(Nat.log 2 z) := pow_pos (by omega) _
  have hlo : 2^(Nat.log 2 z)≤z :=
    Nat.pow_log_le_self 2 hz.ne'
  have hhi := Nat.lt_pow_succ_log_self (by omega : 1<2) z
  refine ⟨hpos,hlo,?_⟩
  simpa only [pow_succ,mul_comm] using hhi

/-- Finite physical source z-carrier grouped exactly into its real
binary dyadic Z images. This partitions all REAL original complex
signed z contributions with exact source multiplicities, no imaginary
extra Z pieces, and no Fourier derivative bounds assumed. -/
theorem parity_original_historical_actual_dyadic_z_finite_reindex434
    (S : Finset ℕ) (W : ℕ → ℂ) :
    (∑ z∈S,W z) =
      ∑ Z∈S.image parityOriginalHistoricalActualZDyadicScale434,
        ∑ z∈S.filter (fun z => parityOriginalHistoricalActualZDyadicScale434 z=Z),W z := by
  classical
  let g : ℕ → ℕ := parityOriginalHistoricalActualZDyadicScale434
  have h := Finset.sum_image' (s:=S) (g:=g)
    (f:=fun Z => ∑z∈S.filter (fun z=>g z=Z),W z)
    W (by intro z hz; rfl)
  simpa only [g] using h.symm

/-- The exact actual historical physical signed z-support, grouped by
its SOURCE binary dyadic Z, not by the whole interval [1,X]. -/
def parityOriginalHistoricalActualPhysicalDyadicZSupport434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp : ℕ) (J : Finset ℕ) : Finset ℕ :=
  (parityOriginalHistoricalPhysicalValidZSupport434
    d L band slot δ Y e m mp J).image
      parityOriginalHistoricalActualZDyadicScale434

/-- The exact original z-fibre inside one ORIGINAL physically
attained dyadic Z. This is a subcarrier of the true Q/P/B509 source. -/
def parityOriginalHistoricalActualPhysicalZDyadicFibre434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp : ℕ) (J : Finset ℕ) (Z : ℕ) : Finset ℕ :=
  (parityOriginalHistoricalPhysicalValidZSupport434 d L band slot δ Y e m mp J).filter
    (fun z => parityOriginalHistoricalActualZDyadicScale434 z=Z)

/-- True original physical signed SOURCE k,z at fixed e,m,m' is
EXACTLY its source Z-dyadic partition, with the same signed H_0,
original b629 alpha/star alpha and n-fibre. Nothing is averaged,
replaced by a positive majorant, or duplicated. -/
theorem parity_original_historical_physical_z_dyadic_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m mp : ℕ) (J : Finset ℕ) :
    (∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
        d L band slot δ Y e m mp J,
      ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
        (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
        parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp) =
    ∑ Z∈parityOriginalHistoricalActualPhysicalDyadicZSupport434
        d L band slot δ Y e m mp J,
      ∑ z∈parityOriginalHistoricalActualPhysicalZDyadicFibre434
        d L band slot δ Y e m mp J Z,
        ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
          (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp := by
  unfold parityOriginalHistoricalActualPhysicalDyadicZSupport434
    parityOriginalHistoricalActualPhysicalZDyadicFibre434
  exact parity_original_historical_actual_dyadic_z_finite_reindex434
    (parityOriginalHistoricalPhysicalValidZSupport434 d L band slot δ Y e m mp J)
    (fun z => ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
      (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualZ417Range -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17500000

/-- The REAL original physical h=-2 z lies in its source binary
Z-scale and this scale is in the precise polynomial Parity (4.17)
Z envelope as soon as the original e/E dyad gives
 exp L*L^K0/2 <= z <= 4exp L*L^(K0+88).
The exponent CZ=K0+90 is not a free assumption inserted by a
correlation theorem: it is paid explicitly from the source physical
scale, with all constants 2,4 and 2^j retained. -/
theorem parity_original_historical_actual_z_dyadic_parity417_envelope434
    (L K0 : ℝ) (z : ℕ)
    (hL : 8≤L) (hK0 : 0≤K0) (hz : 0<z)
    (hLow : (Real.exp L/2)*L^K0≤(z:ℝ))
    (hHi : (z:ℝ)≤4*Real.exp L*L^(K0+88)) :
    Real.exp L*L^(-(K0+90)) ≤
      (parityOriginalHistoricalActualZDyadicScale434 z:ℝ) ∧
    (parityOriginalHistoricalActualZDyadicScale434 z:ℝ) ≤
      Real.exp L*L^(K0+90) := by
  have hLp : 0<L := by linarith
  have hLone : 1≤L := by linarith
  have hX : 0<Real.exp L := Real.exp_pos L
  have hKpos : 0<L^K0 := Real.rpow_pos_of_pos hLp _
  have hExpHiPos : 0<L^(K0+88) := Real.rpow_pos_of_pos hLp _
  obtain ⟨hZpos,hZlo,hZhi⟩ := parity_original_historical_actual_z_in_own_dyad434 z hz
  have hZRpos : (0:ℝ)<(parityOriginalHistoricalActualZDyadicScale434 z:ℝ) := by
    exact_mod_cast hZpos
  have hZRlo : (parityOriginalHistoricalActualZDyadicScale434 z:ℝ)≤(z:ℝ) := by
    exact_mod_cast hZlo
  have hZRhi : (z:ℝ)<2*(parityOriginalHistoricalActualZDyadicScale434 z:ℝ) := by
    exact_mod_cast hZhi
  have hZlower : (Real.exp L/4)*L^K0≤
      (parityOriginalHistoricalActualZDyadicScale434 z:ℝ) := by
    have hh := hLow.trans_lt hZRhi
    nlinarith [mul_pos hX hKpos]
  have hZupper : (parityOriginalHistoricalActualZDyadicScale434 z:ℝ)≤
      4*Real.exp L*L^(K0+88) := hZRlo.trans hHi
  have hPowK0 : 1≤L^K0 := Real.one_le_rpow hLone hK0
  have hL2 : (4:ℝ)≤L^2 := by nlinarith
  have h90 : 4≤L^(K0+90) := by
    have hExp : (2:ℝ)≤K0+90 := by linarith
    have hm := Real.rpow_le_rpow_of_exponent_le hLone hExp
    have h2 : L^(2:ℝ)=L^2 := Real.rpow_natCast L 2
    exact hL2.trans (h2 ▸ hm)
  have hPow90pos : 0<L^(K0+90) := Real.rpow_pos_of_pos hLp _
  have hInv : L^(-(K0+90))≤(1/4:ℝ) := by
    rw [Real.rpow_neg hLp.le]
    have hh := (inv_le_inv₀ hPow90pos (by norm_num : (0:ℝ)<4)).mpr h90
    simpa only [one_div] using hh
  have hLowBound : L^(-(K0+90))≤(1/4:ℝ)*L^K0 := by
    calc
      _ ≤ (1/4:ℝ) := hInv
      _ = (1/4:ℝ)*1 := by ring
      _ ≤ (1/4:ℝ)*L^K0 :=
        mul_le_mul_of_nonneg_left hPowK0 (by norm_num)
  have hPowInc : L^(K0+90)=L^(K0+88)*L^2 := by
    have heq : K0+90=(K0+88)+(2:ℝ) := by ring
    rw [heq,Real.rpow_add hLp]
    exact congrArg (fun r : ℝ => L^(K0+88)*r) (Real.rpow_natCast L 2)
  constructor
  · calc
      _ ≤ Real.exp L*((1/4:ℝ)*L^K0) :=
        mul_le_mul_of_nonneg_left hLowBound hX.le
      _ = (Real.exp L/4)*L^K0 := by ring
      _ ≤ _ := hZlower
  · calc
      _ ≤ 4*Real.exp L*L^(K0+88) := hZupper
      _ = Real.exp L*(4*L^(K0+88)) := by ring
      _ ≤ Real.exp L*(L^2*L^(K0+88)) := by
        apply mul_le_mul_of_nonneg_left _ hX.le
        exact mul_le_mul_of_nonneg_right hL2 hExpHiPos.le
      _ = Real.exp L*L^(K0+90) := by rw [hPowInc];ring

/-- The actual original Q/P h=-2 cofactor-supported z in the
historical active e-window, with U*V>=exp L, gives precisely the
required source-derived Parity (4.17) real Z envelope for its OWN
binary dyadic scale. No independently imposed beta/4 or Z condition
and no unsupported floor-division z cases appear. -/
theorem parity_original_historical_supported_z_actual_parity417_Z_envelope434
    (d : ℕ) (L U V E K0 : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (J : Finset ℕ) (e m mp z : ℕ)
    (hL : 8≤L) (hK0 : 0≤K0)
    (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hE : E=U*L^(-K0))
    (hWin : parityOriginalHistoricalEWindow434 L E e)
    (he : Odd e) (hneq : m≠mp)
    (hmLo : U≤(m:ℝ)) (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)<2*U)
    (hnLo : ∀ n∈J,V≤(n:ℝ))
    (hz : z∈parityOriginalHistoricalPhysicalValidZSupport434
      d L band slot δ ⌊2*Real.exp L⌋₊ e m mp J) :
    Real.exp L*L^(-(K0+90))≤
      (parityOriginalHistoricalActualZDyadicScale434 z:ℝ) ∧
    (parityOriginalHistoricalActualZDyadicScale434 z:ℝ)≤
      Real.exp L*L^(K0+90) := by
  have hZ := parity_original_historical_physical_supported_z_source_dyadic434
    d L U V E K0 band slot δ J e m mp z
    (by linarith : 4≤L) hU hV hUV hE hWin he hneq
    hmLo hmpLo hmpHi hnLo hz
  have hZpos := parity_original_historical_physical_supported_z_and_shift_pos434
    d L band slot δ ⌊2*Real.exp L⌋₊ e m mp J z he hneq hz
  exact parity_original_historical_actual_z_dyadic_parity417_envelope434
    L K0 z hL hK0 hZpos.2.1 hZ.1 hZ.2
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalDyadicFubini -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17500000

/-- The exact genuine dyadic Z SUPPORT across all actual ORIGINAL
cofactors m' for a fixed source e,m,k, with no manufactured full
range of powers-of-two or independent physical v assumption. -/
def parityOriginalHistoricalActualPhysicalDyadicZUnion434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) : Finset ℕ :=
  (parityOriginalHistoricalKPrimeFibre434 e m K k).biUnion (fun mp =>
    parityOriginalHistoricalActualPhysicalDyadicZSupport434
      d L band slot δ Y e m mp J)

/-- Every physical Z retains EXACTLY its supporting m' fibre.
The absence of a particular Z for an m' contributes ZERO rather
than some fictitious complex source coefficient. -/
def parityOriginalHistoricalActualPhysicalDyadicMFibre434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ) : Finset ℕ :=
  (parityOriginalHistoricalKPrimeFibre434 e m K k).filter (fun mp =>
    Z∈parityOriginalHistoricalActualPhysicalDyadicZSupport434
      d L band slot δ Y e m mp J)

/-- Exact finite cofactor/dyadic Z interchange with arbitrary
cofactor-dependent physical Z carriers. No double-counting in the
union across m', and no factor #k, #Z, or #m' is introduced. -/
theorem parity_original_historical_physical_dyadic_fubini434
    (M : Finset ℕ) (S : ℕ → Finset ℕ) (W : ℕ → ℕ → ℂ) :
    (∑ mp∈M,∑Z∈S mp,W mp Z) =
    ∑ Z∈M.biUnion S,
      ∑ mp∈M.filter (fun mp => Z∈S mp),W mp Z := by
  classical
  have hExtend (mp : ℕ) (hmp : mp∈M) :
      (∑ Z∈S mp,W mp Z) =
      ∑ Z∈M.biUnion S,if Z∈S mp then W mp Z else 0 := by
    have hsub : S mp ⊆ M.biUnion S := by
      intro Z hZ
      exact Finset.mem_biUnion.mpr ⟨mp,hmp,hZ⟩
    calc
      _ = ∑ Z∈(M.biUnion S).filter (fun Z => Z∈S mp),W mp Z := by
        congr 1
        ext Z
        simp only [Finset.mem_filter]
        constructor
        · intro hZ;exact ⟨hsub hZ,hZ⟩
        · exact And.right
      _ = _ := by rw [Finset.sum_filter]
  calc
    _ = ∑mp∈M,∑Z∈M.biUnion S,if Z∈S mp then W mp Z else 0 := by
      apply Finset.sum_congr rfl
      intro mp hmp
      exact hExtend mp hmp
    _ = ∑Z∈M.biUnion S,∑mp∈M,if Z∈S mp then W mp Z else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Z hZ
      rw [Finset.sum_filter]

/-- For the TRUE signed original finite character cofactor expression,
introduce and move its REAL dyadic Z outside the whole m' sum.
Every original physical n/z collision and Q/P support is retained.
This is a literal Parity(4.15) reindex, before Fourier or correlation
bounds; unlike a claimed TypeII saving it is an exact complex sum. -/
theorem parity_original_historical_character_cofactor_dyadic_fubini434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y e m : ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    (∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
      χ (mp : ZMod (2*k.natAbs)) *
      (∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
        d L band slot δ Y e m mp J,
        ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
          (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp)) =
    ∑ Z∈parityOriginalHistoricalActualPhysicalDyadicZUnion434
        d L band slot δ Y e m K J k,
      ∑ mp∈parityOriginalHistoricalActualPhysicalDyadicMFibre434
        d L band slot δ Y e m K J k Z,
        χ (mp : ZMod (2*k.natAbs)) *
        (∑ z∈parityOriginalHistoricalActualPhysicalZDyadicFibre434
          d L band slot δ Y e m mp J Z,
          ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
            (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
            parityOriginalHistoricalOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e n m mp) := by
  let M := parityOriginalHistoricalKPrimeFibre434 e m K k
  let S : ℕ → Finset ℕ := fun mp =>
    parityOriginalHistoricalActualPhysicalDyadicZSupport434
      d L band slot δ Y e m mp J
  let W : ℕ → ℕ → ℂ := fun mp Z =>
    χ (mp : ZMod (2*k.natAbs)) *
      (∑z∈parityOriginalHistoricalActualPhysicalZDyadicFibre434
        d L band slot δ Y e m mp J Z,
        ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
          (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp)
  have hOne (mp : ℕ) (hmp : mp∈M) :
      χ (mp : ZMod (2*k.natAbs)) *
      (∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
        d L band slot δ Y e m mp J,
        ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
          (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp) =
      ∑Z∈S mp,W mp Z := by
    rw [parity_original_historical_physical_z_dyadic_exact434]
    rw [Finset.mul_sum]
  calc
    _ = ∑mp∈M,∑Z∈S mp,W mp Z := by
      apply Finset.sum_congr rfl
      intro mp hmp
      exact hOne mp hmp
    _ = ∑Z∈M.biUnion S,
          ∑mp∈M.filter (fun mp => Z∈S mp),W mp Z :=
        parity_original_historical_physical_dyadic_fubini434 M S W
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalWeightedCauchy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17500000

/-- GENUINE original Parity(4.10) positive weighted Cauchy physical
square, on only the HISTORICALLY ACTIVE selected-Q e-window, with the
real smoothing weight η_e(e/E)η_n(n/V) (abstract w until the source
smooth majorant construction is inserted). No assumptions about
signed offdiagonal cancellation are introduced. -/
def parityOriginalHistoricalWeightedActiveCauchySquare434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℝ :=
  ∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑ n ∈ J, w e n *
      ‖∑m∈K,α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2

/-- The mathematically correct location of η_e,η_n in Parity (4.10):
first take the ACTUAL signed source Cauchy norm square, then enlarge
its real NONNEGATIVE physical square by any true smooth weight w≥1.
There is NO false monotonicity of the complex offdiagonal terms;
that offdiagonal is expanded only AFTER the positive majorant. -/
theorem parity_original_historical_signed_weighted_active_Cauchy434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ e ∈ parityOriginalHistoricalCauchyActiveESupport434
         d L E band slot δ, ∀ n ∈ J, 1 ≤ w e n) :
    ‖parityOriginalHistoricalCauchyAtDelta434 d L E band slot δ ξ rho
      K J α β signed Y‖^2 ≤
    (∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
      ∑n∈J,‖parityOriginalHistoricalWindowAE434
        d L E band slot δ ξ rho e*β n‖^2) *
      parityOriginalHistoricalWeightedActiveCauchySquare434
        d L E band slot δ ξ rho K J α signed Y w := by
  have hOld := parity_original_historical_signed_active_e_n_cauchy434
    d L E band slot δ ξ rho K J α β signed Y
  have hSquare : parityOriginalHistoricalActiveCauchySquare434
      d L E band slot δ ξ rho K J α signed Y ≤
      parityOriginalHistoricalWeightedActiveCauchySquare434
        d L E band slot δ ξ rho K J α signed Y w := by
    unfold parityOriginalHistoricalActiveCauchySquare434
      parityOriginalHistoricalWeightedActiveCauchySquare434
    apply Finset.sum_le_sum
    intro e he
    apply Finset.sum_le_sum
    intro n hn
    have hpos : 0≤‖∑m∈K,α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2 := sq_nonneg _
    calc
      _ = 1 * _ := by ring
      _ ≤ w e n * _ := mul_le_mul_of_nonneg_right (hw e he n hn) hpos
  have hCoef : 0 ≤
      (∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
      ∑n∈J,‖parityOriginalHistoricalWindowAE434
        d L E band slot δ ξ rho e*β n‖^2) := by
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro n hn
    exact sq_nonneg _
  exact hOld.trans (mul_le_mul_of_nonneg_left hSquare hCoef)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalWeightedGram -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- The true Parity (4.10) smooth-weighted diagonal, restricted to the
ORIGINAL selected-Q active e-window. This is a NONNEGATIVE real
quadratic sum, not a signed offdiagonal term. -/
def parityOriginalHistoricalWeightedActiveDiagonal434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℝ :=
  ∑ e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑ n∈J,w e n *
      ∑ m∈K,‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2

/-- Exact ORIGINAL smooth-weighted complex signed Parity (4.13)
OFFDIAGONAL, with η_e(e/E)η_n(n/V) outside the genuine m,m' pair.
Critically it is NOT assumed nonnegative, bounded by the raw
unweighted offdiagonal, or equal to the ungated physical source. -/
def parityOriginalHistoricalWeightedActiveOffdiag434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℂ :=
  ∑ e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑ n∈J,((w e n:ℝ):ℂ) *
      (∑ m∈K,∑ mp∈K.erase m,
        (α m*parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m) *
        star (α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n mp))

/-- TRUE original Parity(4.10) weighted Gram identity. The smooth
majorant weights are introduced on the positive Cauchy square BEFORE
splitting into m=m' diagonal and m≠m' complex offdiagonal.
Every source h=-2 signed H0 coefficient is kept exact, even for
weights >1. This prevents invalid signed-offdiagonal monotonicity. -/
theorem parity_original_historical_weighted_active_square_diag_offdiag434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) :
    ((parityOriginalHistoricalWeightedActiveCauchySquare434
      d L E band slot δ ξ rho K J α signed Y w:ℝ):ℂ) =
    ((parityOriginalHistoricalWeightedActiveDiagonal434
      d L E band slot δ ξ rho K J α signed Y w:ℝ):ℂ) +
      parityOriginalHistoricalWeightedActiveOffdiag434
        d L E band slot δ ξ rho K J α signed Y w := by
  let Q := parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ
  let F : ℕ → ℕ → ℕ → ℂ := fun e n m =>
    α m*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m
  have hOne (e n : ℕ) :
      ((‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
      ((∑m∈K,‖F e n m‖^2:ℝ):ℂ) +
        ∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp) :=
    parity_original_historical_actual_e_n_square_diag_offdiag434
      d L band slot δ ξ rho K α signed Y e n
  unfold parityOriginalHistoricalWeightedActiveCauchySquare434
    parityOriginalHistoricalWeightedActiveDiagonal434
    parityOriginalHistoricalWeightedActiveOffdiag434
  change ((∑e∈Q,∑n∈J,w e n*‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
    ((∑e∈Q,∑n∈J,w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) +
      (∑e∈Q,∑n∈J,((w e n:ℝ):ℂ)*
        (∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp)))
  have hCastL : ((∑e∈Q,∑n∈J,w e n*‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
      ∑e∈Q,∑n∈J,((w e n*‖∑m∈K,F e n m‖^2:ℝ):ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Complex.ofReal_sum]
  have hCastD : ((∑e∈Q,∑n∈J,w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) =
      ∑e∈Q,∑n∈J,((w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Complex.ofReal_sum]
  rw [hCastL,hCastD]
  calc
    _ = ∑e∈Q,∑n∈J,
      (((w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) +
        ((w e n:ℝ):ℂ)*(∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp))) := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      calc
        ((w e n*‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
          ((w e n:ℝ):ℂ)*((‖∑m∈K,F e n m‖^2:ℝ):ℂ) := by push_cast; rfl
        _ = ((w e n:ℝ):ℂ) *
          (((∑m∈K,‖F e n m‖^2:ℝ):ℂ) +
            (∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp))) := by
              rw [hOne e n]
        _ = (((w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) +
          ((w e n:ℝ):ℂ)*(∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp))) := by
            push_cast
            ring
    _ = _ := by simp_rw [Finset.sum_add_distrib]

/-- The exact weighted original diagonal is NONNEGATIVE whenever
η_e η_n are nonnegative on their original active e,n support; no
unproved smooth Fourier-tail estimate enters. -/
theorem parity_original_historical_weighted_active_diagonal_nonneg434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ)
    (hw : ∀e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
       ∀n∈J,0≤w e n) :
    0≤parityOriginalHistoricalWeightedActiveDiagonal434
      d L E band slot δ ξ rho K J α signed Y w := by
  unfold parityOriginalHistoricalWeightedActiveDiagonal434
  apply Finset.sum_nonneg
  intro e he
  apply Finset.sum_nonneg
  intro n hn
  apply mul_nonneg (hw e he n hn)
  apply Finset.sum_nonneg
  intro m hm
  exact sq_nonneg _
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalWeightedPhysicalKZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- The true original Parity (4.10)-(4.13) weighted signed physical
complex offdiagonal after original e,n smoothing has been introduced
on the POSITIVE Cauchy square and m,m' GRAM expanded. For arbitrary
signed real weights w(e,n), the original selected e window, k!=0,
canonical physical z, and all true Q/P H0 gates and n fibre weights
are kept exactly. -/
def parityOriginalHistoricalWeightedActivePhysicalKZ434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℂ :=
  ∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
          ∑z∈parityOriginalHistoricalPhysicalValidZSupport434
            d L band slot δ Y e m mp J,
            ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
              (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
              ((w e n:ℝ):ℂ) *
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp

/-- Nonnegative structural SOURCE weight is NEVER used to bound the
complex signed offdiagonal. Instead, this exact source identity
eliminates physically unsupported n using the already proven zero
criterion, preserving the FULL complex weighted signed amplitude. -/
theorem parity_original_historical_weighted_N_source_filter_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m mp : ℕ) (w : ℕ → ℂ) (J : Finset ℕ) :
    (∑n∈J,w n*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
       d L band slot δ ξ rho α signed Y e n m mp) =
    ∑n∈J.filter
      (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
      w n*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hv : parityOriginalHistoricalPhysicalValidN434
    d L band slot δ Y e m mp n
  · simp only [if_pos hv]
  · have hh := parity_original_historical_offdiag_zero_without_physical_N434
      d L band slot δ ξ rho α signed Y e m mp n hv
    simp [hv,hh]

/-- The source-signed weighted original n -> z image reindex, with
every actual e,n smooth weight STILL INSIDE the unique n fibre.
It does not incorrectly pull eta_n(n/V) outside the source z sum. -/
theorem parity_original_historical_weighted_z_source_filter_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m mp : ℕ) (w : ℕ → ℂ) (J : Finset ℕ) :
    (∑z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
      ∑n∈parityOriginalHistoricalCanonicalZNFibre434 e m mp J z,
        w n*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp) =
    ∑z∈parityOriginalHistoricalPhysicalValidZSupport434
        d L band slot δ Y e m mp J,
      ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
        (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
        w n*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp := by
  classical
  let NF : ℕ → Finset ℕ :=
    parityOriginalHistoricalCanonicalZNFibre434 e m mp J
  let V : ℕ → Prop :=
    parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp
  have hOne (z : ℕ) :
    (∑n∈NF z,w n*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
       d L band slot δ ξ rho α signed Y e n m mp) =
    ∑n∈(NF z).filter V,
      w n*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp :=
    parity_original_historical_weighted_N_source_filter_exact434
      d L band slot δ ξ rho α signed Y e m mp w (NF z)
  calc
    _ = ∑z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
        ∑n∈(NF z).filter V,
          w n*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hOne z
    _ = ∑z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
        if ((NF z).filter V).Nonempty then
          (∑n∈(NF z).filter V,
            w n*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e n m mp) else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hv : ((NF z).filter V).Nonempty
      · simp only [if_pos hv]
      · have hempty : (NF z).filter V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hv
        simp [hv,hempty]
    _ = _ := by
      unfold parityOriginalHistoricalPhysicalValidZSupport434
      rw [Finset.sum_filter]

/-- The actual original smooth-weighted Cauchy signed offdiagonal
can be reindexed to the full NONZERO canonical k and the TRUE
physical z support without changing the e,n weight, H0 parity,
original b629 alpha, or any Fourier phase. No character orthogonality
is needed at this purely exact arithmetic step. -/
theorem parity_original_historical_weighted_offdiag_k_z_exact434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ)
    (hOdd : ∀ e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
      Odd e) :
    parityOriginalHistoricalWeightedActiveOffdiag434
      d L E band slot δ ξ rho K J α signed Y w =
    parityOriginalHistoricalWeightedActivePhysicalKZ434
      d L E band slot δ ξ rho K J α signed Y w := by
  let Q := parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ
  let F : ℕ → ℕ → ℕ → ℕ → ℂ := fun e n m mp =>
    ((w e n:ℝ):ℂ) *
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp
  have hPoint (e n m mp : ℕ) :
      ((w e n:ℝ):ℂ) *
      ((α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m) *
       star (α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n mp)) = F e n m mp := by
    exact congrArg (fun t : ℂ => ((w e n:ℝ):ℂ)*t)
      (parity_original_historical_actual_ENM_pair_eq_gated_source434
        d L band slot δ ξ rho α signed Y e n m mp)
  have hZero (e n m : ℕ) (he : e∈Q) :
      (∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K 0,F e n m mp)=0 := by
    apply Finset.sum_eq_zero
    intro mp hmp
    have hp := Finset.mem_filter.mp hmp
    have hz := parity_original_historical_actual_zero_k_physical_source_vanishes434
      d L band slot δ ξ rho K α signed Y e n m mp
      (hOdd e he) hp.1 hp.2
    dsimp [F]
    rw [hz,mul_zero]
  unfold parityOriginalHistoricalWeightedActiveOffdiag434
    parityOriginalHistoricalWeightedActivePhysicalKZ434
  simp_rw [Finset.mul_sum]
  change (∑e∈Q,∑n∈J,∑m∈K,∑mp∈K.erase m,
      ((w e n:ℝ):ℂ)*
      ((α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m)*
       star (α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n mp))) = _
  calc
    _ = ∑e∈Q,∑n∈J,∑m∈K,∑mp∈K.erase m,F e n m mp := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro mp hmp
      exact hPoint e n m mp
    _ = ∑e∈Q,∑n∈J,∑m∈K,
        ∑k∈parityOriginalHistoricalKSupport434 e m K,
          ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,F e n m mp := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      exact parity_original_historical_cofactor_sum_eq_k_fibres434 e m K (F e n m)
    _ = ∑e∈Q,∑n∈J,∑m∈K,
        ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
          ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,F e n m mp := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      let S := parityOriginalHistoricalKSupport434 e m K
      let H : ℤ → ℂ := fun k =>
        ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,F e n m mp
      change (∑k∈S,H k)=(∑k∈S.filter (·≠0),H k)
      calc
        _ = ∑k∈S,if k≠0 then H k else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases h : k=0
          · subst k
            simpa only [if_neg (by decide : ¬ ((0:ℤ) ≠ 0))] using (hZero e n m he)
          · simp [h]
        _ = _ := by rw [Finset.sum_filter]
    _ = ∑e∈Q,∑m∈K,
        ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
          ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
            ∑z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
              ∑n∈parityOriginalHistoricalCanonicalZNFibre434 e m mp J z,
              F e n m mp :=
      parity_original_historical_k_then_z_source_reindex434 Q K J F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro mp hmp
      exact parity_original_historical_weighted_z_source_filter_exact434
        d L band slot δ ξ rho α signed Y e m mp
        (fun n => ((w e n:ℝ):ℂ)) J
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalWeightedMask -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- EXACT character orthogonality inserted into one complete original
physical z fibre with the actual b629 fine-cell α_m,α_m'. On the
unrestricted original formal k,z image the mask need not hold. Here
e,m,m',z and canonical k are source-filtered and the two endpoint
physical Q/P carriers are really inhabited. The entire original
smooth eta_e(e/E)*eta_n(n/V) weight remains at the UNIQUE physical n,
not outside the source z support. If either fine alpha is
zero, the entire SOURCE fibre is identically zero and stays zero.
No ℓ1 bound is applied until AFTER this identity. -/
theorem parity_eventually_original_weighted_supported_z_fine_character_mask_insert434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E rho : ℝ) (K J : Finset ℕ) (signed prime : Bool)
        (lFine uFine e m mp z : ℕ) (w : ℕ → ℕ → ℝ),
      0<U → E=U*L^(-K0) →
      U≤(m:ℝ) → (m:ℝ)<2*U →
      U≤(mp:ℝ) → (mp:ℝ)<2*U →
      e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ →
      m∈K → mp∈K.erase m →
      z∈parityOriginalHistoricalPhysicalValidZSupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m mp J →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let k := parityOriginalHistoricalOffdiagK434 e m mp
      let W := ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
        (parityOriginalHistoricalPhysicalValidN434
          (sourceOriginalLiteralDepth 20 L) L band slot δ
          ⌊2*Real.exp L⌋₊ e m mp),
        ((w e n:ℝ):ℂ) * parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho alpha signed
          ⌊2*Real.exp L⌋₊ e n m mp
      W = ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
        (parityShiftTwoMaskCoefficient434 k.natAbs chi *
          chi (mp : ZMod (2*k.natAbs)) *
          star (chi (m : ZMod (2*k.natAbs)))) * W := by
  filter_upwards [parity_eventually_original_historical_supported_fine_mask_at_z434
    S beta gamma K0 hS hbeta hgamma] with L h
  refine ⟨h.1,?_⟩
  intro band slot δ ξ U E rho K J signed prime lFine uFine
    e m mp z w hU hScale hmLo hmHi hmpLo hmpHi he hm hmp hz
    hl hFineLow
  dsimp only
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  let W : ℂ := ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
    (parityOriginalHistoricalPhysicalValidN434
      (sourceOriginalLiteralDepth 20 L) L band slot δ
      ⌊2*Real.exp L⌋₊ e m mp),
    ((w e n:ℝ):ℂ) * parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho alpha signed
      ⌊2*Real.exp L⌋₊ e n m mp
  change W = ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
    (parityShiftTwoMaskCoefficient434 k.natAbs chi *
      chi (mp : ZMod (2*k.natAbs)) *
      star (chi (m : ZMod (2*k.natAbs)))) * W
  by_cases ham : alpha m=0
  · have hW : W=0 := by
      dsimp [W]
      apply Finset.sum_eq_zero
      intro n hn
      unfold parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      simp only [ham,zero_mul,mul_zero,Finset.sum_const_zero]
    rw [hW]
    simp
  by_cases hamp : alpha mp=0
  · have hW : W=0 := by
      dsimp [W]
      apply Finset.sum_eq_zero
      intro n hn
      unfold parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      simp only [hamp,zero_mul,mul_zero,star_zero,Finset.sum_const_zero]
    rw [hW]
    simp
  have hActual := h.2 band slot δ U E K J e m mp z
    hU hScale hmLo hmHi hmpLo hmpHi he hm hmp hz
    prime lFine uFine hl hFineLow ham hamp
  dsimp only at hActual
  have hMask := hActual.2.2.2.1
  exact parity_original_exact_mask_insert_complex434 k m mp W hMask
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalWeightedFullMask -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- True original Parity(4.10) smooth-weighted signed m≠m' physical
Cauchy offdiagonal with SOURCE-selected historical e-window and
exact character orthogonality (2.6) inserted before any character
l1 majorant. Real w(e,n)=eta_e(e/E)*eta_n(n/V) remains INSIDE the
true supported n fibre. No hypothetical cancellation estimate. -/
def parityOriginalHistoricalWeightedActiveMaskedKZ434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℂ :=
  ∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
          ∑z∈parityOriginalHistoricalPhysicalValidZSupport434
            d L band slot δ Y e m mp J,
            ∑chi : DirichletCharacter ℂ (2*k.natAbs),
              (parityShiftTwoMaskCoefficient434 k.natAbs chi *
                chi (mp : ZMod (2*k.natAbs)) *
                star (chi (m : ZMod (2*k.natAbs)))) *
              (∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
                (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
                ((w e n:ℝ):ℂ)*
                parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                  d L band slot δ ξ rho α signed Y e n m mp)

/-- Entire literal original Parity(4.10) historical SMOOTH-weighted
signed physical Cauchy offdiagonal equals exact original Parity(2.6)
character-masked k,z source, under the REAL b629 nonzero/unit
conditions. The proof applies character orthogonality only AFTER
the positive Cauchy majorant and full Gram expansion.
At no point is a signed offdiagonal replaced by its unweighted value. -/
theorem parity_eventually_original_historical_weighted_fine_offdiag_masked434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop,4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E rho : ℝ) (K J : Finset ℕ) (prime signed : Bool)
        (lFine uFine : ℕ) (w : ℕ → ℕ → ℝ),
      0<U → E=U*L^(-K0) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      parityOriginalHistoricalWeightedActiveOffdiag434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w =
      parityOriginalHistoricalWeightedActiveMaskedKZ434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w := by
  filter_upwards [parity_eventually_original_cartesian_selected_e_odd_unit434,
    parity_eventually_original_weighted_supported_z_fine_character_mask_insert434
      S beta gamma K0 hS hbeta hgamma] with L hOdd hMask
  refine ⟨hMask.1,?_⟩
  intro band slot δ ξ U E rho K J prime signed lFine uFine w
    hU hScale hDyad hl hFineLow
  dsimp only
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  have hQ : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
      (sourceOriginalLiteralDepth 20 L) L E band slot δ,Odd e := by
    intro e he
    exact (hOdd.2 band slot δ e (Finset.mem_filter.mp he).1).1
  rw [parity_original_historical_weighted_offdiag_k_z_exact434
    (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho K J
    alpha signed ⌊2*Real.exp L⌋₊ w hQ]
  unfold parityOriginalHistoricalWeightedActivePhysicalKZ434
    parityOriginalHistoricalWeightedActiveMaskedKZ434
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro mp hmp
  apply Finset.sum_congr rfl
  intro z hz
  have hmpMem : mp∈K.erase m := (Finset.mem_filter.mp hmp).1
  have hkCanon : parityOriginalHistoricalOffdiagK434 e m mp=k :=
    (Finset.mem_filter.mp hmp).2
  have hmD := hDyad m hm
  have hmpD := hDyad mp (Finset.mem_erase.mp hmpMem).2
  have hPoint := hMask.2 band slot δ ξ U E rho K J signed prime
    lFine uFine e m mp z w hU hScale hmD.1 hmD.2 hmpD.1 hmpD.2
    he hm hmpMem hz hl hFineLow
  dsimp only at hPoint
  rw [hkCanon] at hPoint
  exact hPoint
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalWeightedCharacterOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- True source Parity (4.13)--(4.16) with each ORIGINAL CHARACTER
OUTSIDE m', z and n for the full active e-window and canonical k.
The coefficient `c_chi*conj(chi(m))` remains separate from m' and
original b629 fine alpha; chi(m') remains inside the true cofactor
sum. This is the required position before original (4.17).
No Fourier ℓ1 bound or analytic cancellation is smuggled in. -/
def parityOriginalHistoricalWeightedActiveCharacterOuter434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℂ :=
  ∑ e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑ m∈K,
      ∑ k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          (parityShiftTwoMaskCoefficient434 k.natAbs chi *
            star (chi (m : ZMod (2*k.natAbs)))) *
          (∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
            chi (mp : ZMod (2*k.natAbs)) *
              (∑ z∈parityOriginalHistoricalPhysicalValidZSupport434
                d L band slot δ Y e m mp J,
                ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
                  (parityOriginalHistoricalPhysicalValidN434
                    d L band slot δ Y e m mp),
                  ((w e n:ℝ):ℂ) * parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                    d L band slot δ ξ rho α signed Y e n m mp))

/-- Source-faithful original signed after-mask finite Fubini. In
particular the Dirichlet character is NOT applied to the unsigned
odd-parity projector and no character count is paid before using the
source-proven (2.6) ℓ1 mask bound. -/
theorem parity_original_historical_weighted_masked_k_z_eq_character_outer434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) :
    parityOriginalHistoricalWeightedActiveMaskedKZ434
      d L E band slot δ ξ rho K J α signed Y w =
    parityOriginalHistoricalWeightedActiveCharacterOuter434
      d L E band slot δ ξ rho K J α signed Y w := by
  unfold parityOriginalHistoricalWeightedActiveMaskedKZ434
    parityOriginalHistoricalWeightedActiveCharacterOuter434
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  let M := parityOriginalHistoricalKPrimeFibre434 e m K k
  let Q : Finset (DirichletCharacter ℂ (2*k.natAbs)) := Finset.univ
  let Z : ℕ → Finset ℕ := fun mp =>
    parityOriginalHistoricalPhysicalValidZSupport434
      d L band slot δ Y e m mp J
  let c : DirichletCharacter ℂ (2*k.natAbs) → ℂ := fun chi =>
    parityShiftTwoMaskCoefficient434 k.natAbs chi *
      star (chi (m : ZMod (2*k.natAbs)))
  let f : DirichletCharacter ℂ (2*k.natAbs) → ℕ → ℂ :=
    fun chi mp => chi (mp : ZMod (2*k.natAbs))
  let Wfz : ℕ → ℕ → ℂ := fun mp z =>
    ∑ n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
      (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
      ((w e n:ℝ):ℂ) * parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp
  change (∑mp∈M,∑z∈Z mp,∑chi∈Q,
    (parityShiftTwoMaskCoefficient434 k.natAbs chi *
      chi (mp : ZMod (2*k.natAbs)) *
      star (chi (m : ZMod (2*k.natAbs)))) * Wfz mp z) =
    ∑chi∈Q,c chi*(∑mp∈M,f chi mp*(∑z∈Z mp,Wfz mp z))
  calc
    _ = ∑mp∈M,∑z∈Z mp,∑chi∈Q,(c chi*f chi mp)*Wfz mp z := by
      apply Finset.sum_congr rfl
      intro mp hmp
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro chi hchi
      dsimp [c,f]
      ring
    _ = _ := parity_original_character_outer_finite_fubini434 M Q Z c f Wfz

/-- Actual original r20 signed fine-cell Cauchy offdiagonal is
exactly its historical k,z character-outer expression, retaining
original m' and physical u/u', e*vStar Q/P supports and chi modulus
2|k|. Orthogonality has been used BEFORE any ℓ1 estimate. -/
theorem parity_eventually_original_historical_weighted_fine_offdiag_eq_character_outer434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E rho : ℝ) (K J : Finset ℕ)
        (prime signed : Bool) (lFine uFine : ℕ) (w : ℕ → ℕ → ℝ),
      0<U → E=U*L^(-K0) →
      (∀ m∈K, U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      parityOriginalHistoricalWeightedActiveOffdiag434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w =
      parityOriginalHistoricalWeightedActiveCharacterOuter434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w := by
  filter_upwards [parity_eventually_original_historical_weighted_fine_offdiag_masked434
    S beta gamma K0 hS hbeta hgamma] with L h
  refine ⟨h.1,?_⟩
  intro band slot δ ξ U E rho K J prime signed lFine uFine w
    hU hScale hDyad hl hFineLow
  dsimp only
  rw [h.2 band slot δ ξ U E rho K J prime signed lFine uFine w
    hU hScale hDyad hl hFineLow]
  exact parity_original_historical_weighted_masked_k_z_eq_character_outer434
    (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho K J
    (restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine))
    signed ⌊2*Real.exp L⌋₊ w
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalWeightedDyadicCharacter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The authentic Parity(4.15) dyadic Z move in the PHYSICALLY
SMOOTH-WEIGHTED original χ-cofactor sum: the original η_eη_n
weight stays at each canonical n, the character at its real m',
and every possible Z is an actually attained binary dyad from a
true two-ended Q/P source. No positive unweighted offdiagonal
substitution is made. -/
theorem parity_original_historical_weighted_character_dyadic_cofactor_fubini434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y e m : ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (w : ℕ → ℕ → ℝ) :
    (∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
      χ (mp : ZMod (2*k.natAbs)) *
      (∑z∈parityOriginalHistoricalPhysicalValidZSupport434
        d L band slot δ Y e m mp J,
        ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
          (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
          ((w e n:ℝ):ℂ)*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp)) =
    ∑Z∈parityOriginalHistoricalActualPhysicalDyadicZUnion434
        d L band slot δ Y e m K J k,
      ∑mp∈parityOriginalHistoricalActualPhysicalDyadicMFibre434
        d L band slot δ Y e m K J k Z,
        χ (mp : ZMod (2*k.natAbs)) *
        (∑z∈parityOriginalHistoricalActualPhysicalZDyadicFibre434
          d L band slot δ Y e m mp J Z,
          ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
            (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
            ((w e n:ℝ):ℂ)*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e n m mp) := by
  let M := parityOriginalHistoricalKPrimeFibre434 e m K k
  let S : ℕ → Finset ℕ := fun mp =>
    parityOriginalHistoricalActualPhysicalDyadicZSupport434
      d L band slot δ Y e m mp J
  let W : ℕ → ℕ → ℂ := fun mp Z =>
    χ (mp : ZMod (2*k.natAbs)) *
    (∑z∈parityOriginalHistoricalActualPhysicalZDyadicFibre434
      d L band slot δ Y e m mp J Z,
      ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
        (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
        ((w e n:ℝ):ℂ)*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp)
  have hOne (mp : ℕ) (hmp : mp∈M) :
      χ (mp : ZMod (2*k.natAbs)) *
      (∑z∈parityOriginalHistoricalPhysicalValidZSupport434
        d L band slot δ Y e m mp J,
        ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
          (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
          ((w e n:ℝ):ℂ)*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp) =
      ∑Z∈S mp,W mp Z := by
    rw [parity_original_historical_actual_dyadic_z_finite_reindex434]
    rw [Finset.mul_sum]
    rfl
  calc
    _ = ∑mp∈M,∑Z∈S mp,W mp Z := by
      apply Finset.sum_congr rfl
      intro mp hmp
      exact hOne mp hmp
    _ = ∑Z∈M.biUnion S,∑mp∈M.filter (fun mp => Z∈S mp),W mp Z :=
      parity_original_historical_physical_dyadic_fubini434 M S W
    _ = _ := rfl

/-- Historical original Parity (4.13)-(4.17) after exact source
SMOOTH-weighted positive Cauchy and true CHARACTER orthogonality,
now the dyadic Z is OUTSIDE m',z,n and INSIDE each genuine k,chi.
This is the precise preceding algebraic form for applying actual
per-character correlation Parity (4.17) after Fourier separation. -/
def parityOriginalHistoricalWeightedActiveCharacterDyadicOuter434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℂ :=
  ∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑chi : DirichletCharacter ℂ (2*k.natAbs),
          (parityShiftTwoMaskCoefficient434 k.natAbs chi *
            star (chi (m : ZMod (2*k.natAbs)))) *
          (∑Z∈parityOriginalHistoricalActualPhysicalDyadicZUnion434
            d L band slot δ Y e m K J k,
            ∑mp∈parityOriginalHistoricalActualPhysicalDyadicMFibre434
              d L band slot δ Y e m K J k Z,
              chi (mp : ZMod (2*k.natAbs)) *
                (∑z∈parityOriginalHistoricalActualPhysicalZDyadicFibre434
                  d L band slot δ Y e m mp J Z,
                  ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
                    (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
                    ((w e n:ℝ):ℂ)*
                    parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                      d L band slot δ ξ rho α signed Y e n m mp))

/-- Exact original weighted and signed character-outer-to-dyadic
reindex. No guessed Z support is inserted and NO future Parity(4.17)
smallness theorem is used as an axiom; the identity is finite
Fubini with all original complex factors preserved. -/
theorem parity_original_historical_weighted_character_outer_eq_dyadic434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) :
    parityOriginalHistoricalWeightedActiveCharacterOuter434
      d L E band slot δ ξ rho K J α signed Y w =
    parityOriginalHistoricalWeightedActiveCharacterDyadicOuter434
      d L E band slot δ ξ rho K J α signed Y w := by
  unfold parityOriginalHistoricalWeightedActiveCharacterOuter434
    parityOriginalHistoricalWeightedActiveCharacterDyadicOuter434
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro chi hchi
  rw [parity_original_historical_weighted_character_dyadic_cofactor_fubini434]

/-- TRUE original Parity(4.10) smooth-weighted signed Cauchy full
m≠m' offdiagonal equals the exact historically dyadically grouped
per-character k/Z physical source, once the ACTUAL fine-alpha
nonzero/unit support hypotheses are established. The original
weights remain inside the singleton n(z) fibre, not outside z. -/
theorem parity_eventually_original_historical_weighted_fine_offdiag_character_dyadic434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop,4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E rho : ℝ) (K J : Finset ℕ) (prime signed : Bool)
        (lFine uFine : ℕ) (w : ℕ → ℕ → ℝ),
      0<U → E=U*L^(-K0) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      parityOriginalHistoricalWeightedActiveOffdiag434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w =
      parityOriginalHistoricalWeightedActiveCharacterDyadicOuter434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w := by
  filter_upwards [parity_eventually_original_historical_weighted_fine_offdiag_eq_character_outer434
    S beta gamma K0 hS hbeta hgamma] with L h
  refine ⟨h.1,?_⟩
  intro band slot δ ξ U E rho K J prime signed lFine uFine w
    hU hScale hDyad hl hFineLow
  dsimp only
  rw [h.2 band slot δ ξ U E rho K J prime signed lFine uFine w
    hU hScale hDyad hl hFineLow]
  exact parity_original_historical_weighted_character_outer_eq_dyadic434
    (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho K J
    (restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine))
    signed ⌊2*Real.exp L⌋₊ w
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualEtaMajorants -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Construct the ACTUAL smooth Parity (4.10) e/E majorant at the
historical lower e-window parameter a=L^-88. Its exact closed core
is [a,1], its support lies in (a/2,2), and all derivatives exist.
Unlike a fixed positive-away-from-zero bump, this radius genuinely
shrinks with a and hence carries the crucial L-dependent derivatives. -/
def parityOriginalHistoricalEtaEBump434
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) : ContDiffBump (1+a/4) :=
  ⟨1-3*a/4,1-a/4,by linarith,by linarith⟩

/-- Actual original Parity eta_e(e/E) real-valued nonnegative smooth
majorant, constructed from the source-varying a=L^-88. -/
def parityOriginalHistoricalActualEtaE434
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) (x : ℝ) : ℂ :=
  ((parityOriginalHistoricalEtaEBump434 a ha ha1 x : ℝ):ℂ)

/-- Construct the ORIGINAL eta_n(n/V) dyadic bump, supported in
(1/2,3), identically 1 on [1,2], with fixed radii 3/4,5/4.
Its constants do not depend on L,k or the original n dyad. -/
def parityOriginalHistoricalEtaNBump434 : ContDiffBump (7/4:ℝ) :=
  ⟨3/4,5/4,by norm_num,by norm_num⟩

def parityOriginalHistoricalActualEtaN434 (x : ℝ) : ℂ :=
  ((parityOriginalHistoricalEtaNBump434 x : ℝ):ℂ)

/-- Source-compatible eta_e is smooth for every physical a∈(0,1]. -/
theorem parity_original_historical_actual_eta_e_smooth434
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) :
    ContDiff ℝ ∞ (parityOriginalHistoricalActualEtaE434 a ha ha1) :=
  Complex.ofRealCLM.contDiff.comp
    (parityOriginalHistoricalEtaEBump434 a ha ha1).contDiff

/-- Source-compatible eta_n is a genuinely constructed C∞ cutoff. -/
theorem parity_original_historical_actual_eta_n_smooth434 :
    ContDiff ℝ ∞ parityOriginalHistoricalActualEtaN434 :=
  Complex.ofRealCLM.contDiff.comp parityOriginalHistoricalEtaNBump434.contDiff

/-- The original historical e-smoothing cutoff equals EXACTLY one
on the entire active e/E interval [L^-88,1]. In particular there
is no artificial extra multiplicity or loss in the weighted
positive Cauchy square at source-supported selected e. -/
theorem parity_original_historical_actual_eta_e_one_on_window434
    (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (x : ℝ) (hx : x∈Set.Icc a 1) :
    parityOriginalHistoricalActualEtaE434 a ha ha1 x = 1 := by
  let b := parityOriginalHistoricalEtaEBump434 a ha ha1
  have hdist : |x-(1+a/4)|≤1-3*a/4 := by
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  have hb : b x=1 := b.one_of_mem_closedBall (by
    change |x-(1+a/4)|≤1-3*a/4
    exact hdist)
  simpa only [parityOriginalHistoricalActualEtaE434,b,hb,Complex.ofReal_one]

/-- The original historical n/V dyadic majorant is exactly one
on [1,2], not just a formally assumed smooth multiplier. -/
theorem parity_original_historical_actual_eta_n_one_on_window434
    (x : ℝ) (hx : x∈Set.Icc 1 2) :
    parityOriginalHistoricalActualEtaN434 x=1 := by
  let b := parityOriginalHistoricalEtaNBump434
  have hdist : |x-(7/4:ℝ)|≤3/4 := by
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  have hb : b x=1 := b.one_of_mem_closedBall (by
    change |x-(7/4:ℝ)|≤3/4
    exact hdist)
  simpa only [parityOriginalHistoricalActualEtaN434,b,hb,Complex.ofReal_one]

/-- Exact original eta_e support is INSIDE (a/2,2), including the
historical source lower buffer; no fictitious fixed positive lower
support when a=L^-88 tends to zero. -/
theorem parity_original_historical_actual_eta_e_support434
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) (x : ℝ)
    (hx : parityOriginalHistoricalActualEtaE434 a ha ha1 x≠0) :
    a/2<x ∧ x<2 := by
  let b := parityOriginalHistoricalEtaEBump434 a ha ha1
  have hne : b x≠0 := by
    intro hb
    exact hx (by simp only [parityOriginalHistoricalActualEtaE434,b,hb,Complex.ofReal_zero])
  have hball : x∈Metric.ball (1+a/4) b.rOut := by
    rw [←b.support_eq]
    exact hne
  have habs : |x-(1+a/4)|<1-a/4 := by
    have hh : |x-(1+a/4)| < b.rOut := by
      simpa only [Metric.mem_ball,Real.dist_eq] using hball
    exact hh
  constructor <;> linarith [(abs_lt.mp habs).1,(abs_lt.mp habs).2]

/-- True original eta_n support is INSIDE (1/2,3). -/
theorem parity_original_historical_actual_eta_n_support434
    (x : ℝ) (hx : parityOriginalHistoricalActualEtaN434 x≠0) :
    1/2<x ∧ x<3 := by
  let b := parityOriginalHistoricalEtaNBump434
  have hne : b x≠0 := by
    intro hb
    exact hx (by simp only [parityOriginalHistoricalActualEtaN434,b,hb,Complex.ofReal_zero])
  have hball : x∈Metric.ball (7/4:ℝ) b.rOut := by
    rw [←b.support_eq]
    exact hne
  have habs : |x-(7/4:ℝ)|<5/4 := by
    have hh : |x-(7/4:ℝ)| < b.rOut := by
      simpa only [Metric.mem_ball,Real.dist_eq] using hball
    exact hh
  constructor <;> linarith [(abs_lt.mp habs).1,(abs_lt.mp habs).2]

/-- Real source majorants are nonnegative and bounded by ONE at
every real x. This is the actual smooth Parity (4.10) cutoff with
no hidden signed weight. -/
theorem parity_original_historical_actual_eta_e_nonneg_le_one434
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) (x : ℝ) :
    0≤(parityOriginalHistoricalActualEtaE434 a ha ha1 x).re ∧
    (parityOriginalHistoricalActualEtaE434 a ha ha1 x).re≤1 := by
  unfold parityOriginalHistoricalActualEtaE434
  simpa only [Complex.ofReal_re] using
    ⟨(parityOriginalHistoricalEtaEBump434 a ha ha1).nonneg,
     (parityOriginalHistoricalEtaEBump434 a ha ha1).le_one⟩

theorem parity_original_historical_actual_eta_n_nonneg_le_one434
    (x : ℝ) :
    0≤(parityOriginalHistoricalActualEtaN434 x).re ∧
    (parityOriginalHistoricalActualEtaN434 x).re≤1 := by
  unfold parityOriginalHistoricalActualEtaN434
  simpa only [Complex.ofReal_re] using
    ⟨parityOriginalHistoricalEtaNBump434.nonneg,
     parityOriginalHistoricalEtaNBump434.le_one⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualWeightedCauchy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- The literal original historical small-e smoothing parameter
a=L^-88 is positive and <=1 for every L>=8. Its dependence on L
must NOT be replaced by a fixed positive lower support bound. -/
theorem parity_original_historical_real_e_eta_parameter434
    (L : ℝ) (hL : 8≤L) :
    0<L^(-88:ℝ) ∧ L^(-88:ℝ)≤1 := by
  have hLp : 0<L := by linarith
  have hL1 : 1≤L := by linarith
  refine ⟨Real.rpow_pos_of_pos hLp _,?_⟩
  have hh := Real.rpow_le_rpow_of_exponent_le hL1
    (by norm_num : (-88:ℝ)≤0)
  simpa only [Real.rpow_zero] using hh

/-- ORIGINAL eta_e for the ACTUAL source moving L^-88 active window,
constructed with precise L-dependent bump radii and real-valued C∞. -/
def parityOriginalHistoricalActualEtaEAtL434 (L : ℝ) (hL : 8≤L) : ℝ → ℂ :=
  parityOriginalHistoricalActualEtaE434 (L^(-88:ℝ))
    (parity_original_historical_real_e_eta_parameter434 L hL).1
    (parity_original_historical_real_e_eta_parameter434 L hL).2

/-- The exact real nonnegative original smoothing weight in Parity(4.10)
for any selected e,n, with η_e at moving L^-88 and fixed η_n. -/
def parityOriginalHistoricalActualEtaWeight434
    (L E V : ℝ) (hL : 8≤L) (e n : ℕ) : ℝ :=
  (parityOriginalHistoricalActualEtaEAtL434 L hL ((e:ℝ)/E)).re *
  (parityOriginalHistoricalActualEtaN434 ((n:ℝ)/V)).re

/-- The actual original eta_e is EXACTLY one for any selected e in
the historical E L^-88 <= e <= E window. Not a near-zero approximation. -/
theorem parity_original_historical_eta_e_at_source_e_one434
    (L E : ℝ) (hL : 8≤L) (hE : 0<E) (e : ℕ)
    (hwin : parityOriginalHistoricalEWindow434 L E e) :
    parityOriginalHistoricalActualEtaEAtL434 L hL ((e:ℝ)/E)=1 := by
  let a := L^(-88:ℝ)
  have ha := parity_original_historical_real_e_eta_parameter434 L hL
  have hlo : a≤(e:ℝ)/E := (le_div_iff₀ hE).mpr (by
    change a*E≤(e:ℝ)
    calc
      _ = E*a := by ring
      _ ≤ (e:ℝ) := hwin.1)
  have hhi : (e:ℝ)/E≤1 := (div_le_iff₀ hE).mpr (by
    simpa only [one_mul] using hwin.2)
  exact parity_original_historical_actual_eta_e_one_on_window434
    a ha.1 ha.2 ((e:ℝ)/E) ⟨hlo,hhi⟩

/-- The actual original eta_n equals one on the literal n∈[V,2V]
dyad and has independent smooth support [1/2,3]. -/
theorem parity_original_historical_eta_n_at_source_n_one434
    (V : ℝ) (hV : 0<V) (n : ℕ)
    (hnLo : V≤(n:ℝ)) (hnHi : (n:ℝ)≤2*V) :
    parityOriginalHistoricalActualEtaN434 ((n:ℝ)/V)=1 := by
  have h1 : (1:ℝ)≤(n:ℝ)/V :=
    (le_div_iff₀ hV).mpr (by simpa only [one_mul] using hnLo)
  have h2 : (n:ℝ)/V≤2 :=
    (div_le_iff₀ hV).mpr (by simpa only [mul_comm] using hnHi)
  exact parity_original_historical_actual_eta_n_one_on_window434
    ((n:ℝ)/V) ⟨h1,h2⟩

/-- On the SOURCE-supported original selected e-window and n dyad,
the genuinely constructed smooth majorant weight is exactly ONE.
This licenses multiplying the positive physical Cauchy square by
eta_e*eta_n before expanding, without silently modifying signed
complex offdiagonal terms. -/
theorem parity_original_historical_actual_eta_weight_one_on_source434
    (L E V : ℝ) (hL : 8≤L) (hE : 0<E) (hV : 0<V)
    (e n : ℕ) (hwin : parityOriginalHistoricalEWindow434 L E e)
    (hnLo : V≤(n:ℝ)) (hnHi : (n:ℝ)≤2*V) :
    parityOriginalHistoricalActualEtaWeight434 L E V hL e n=1 := by
  unfold parityOriginalHistoricalActualEtaWeight434
  rw [parity_original_historical_eta_e_at_source_e_one434 L E hL hE e hwin,
    parity_original_historical_eta_n_at_source_n_one434 V hV n hnLo hnHi]
  norm_num

/-- Native original smooth-weighted h=-2 Parity(4.10) Cauchy majorant
WITHOUT an abstract assumed eta_e/eta_n: the genuine smooth source
cutoffs are built above, the moving e support is exact, and the
natural n-dyad support implies eta_n=1. The positive square is
weighted BEFORE any signed character-offdiagonal decomposition. -/
theorem parity_original_historical_actual_smooth_weighted_Cauchy434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L) (hE : 0<E) (hV : 0<V)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (hnRange : ∀ n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) :
    ‖parityOriginalHistoricalCauchyAtDelta434 d L E band slot δ ξ rho
      K J α β signed Y‖^2 ≤
    (∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
      ∑n∈J,‖parityOriginalHistoricalWindowAE434
        d L E band slot δ ξ rho e*β n‖^2) *
      parityOriginalHistoricalWeightedActiveCauchySquare434
        d L E band slot δ ξ rho K J α signed Y
        (parityOriginalHistoricalActualEtaWeight434 L E V hL) := by
  apply parity_original_historical_signed_weighted_active_Cauchy434
    d L E band slot δ ξ rho K J α β signed Y
    (parityOriginalHistoricalActualEtaWeight434 L E V hL)
  intro e he n hn
  have hWin := (Finset.mem_filter.mp he).2
  have hnd := hnRange n hn
  rw [parity_original_historical_actual_eta_weight_one_on_source434
    L E V hL hE hV e n hWin hnd.1 hnd.2]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualSmoothCharacterJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18500000

/-- COMPLETE TRUE source Parity(4.10)->(4.13) smooth-weighted Cauchy
AND the exact signed complex character/dyadic-k-Z physical reduction
for both signed ε branches, with genuinely CONSTRUCTED η_e and η_n,
not abstract majorant hypotheses. Its selected-Q e-window includes
the moving L^-88 support, both original physical Q/P gates and all
b629 fine alpha, true h=-2 k and z=m'v, original conjugations,
character modulus 2|k| and physical double source n-fibre.

This proves the complete SOURCE-to-character/dyadic algebra before
(4.17); it does NOT prove uniform Fourier-moment polynomial decay,
the final Parity (4.17) full signed kernel identification, Type II(4.2),
or Green64.green_64. -/
theorem parity_eventually_original_actual_smooth_weighted_cauchy_to_character_Z434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U V E rho : ℝ) (K J : Finset ℕ)
        (prime signed : Bool) (lFine uFine : ℕ) (β : ℕ → ℂ),
      0<U → 0<V → E=U*L^(-K0) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let w := parityOriginalHistoricalActualEtaWeight434 L E V
        hLw
      let Ns := parityOriginalHistoricalWeightedActiveCauchySquare434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w
      let D := parityOriginalHistoricalWeightedActiveDiagonal434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w
      let OD := parityOriginalHistoricalWeightedActiveCharacterDyadicOuter434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha signed ⌊2*Real.exp L⌋₊ w
      (‖parityOriginalHistoricalCauchyAtDelta434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
          K J alpha β signed ⌊2*Real.exp L⌋₊‖^2 ≤
        (∑e∈parityOriginalHistoricalCauchyActiveESupport434
            (sourceOriginalLiteralDepth 20 L) L E band slot δ,
          ∑n∈J,‖parityOriginalHistoricalWindowAE434
            (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*β n‖^2)*Ns)
       ∧ ((Ns:ℝ):ℂ)=((D:ℝ):ℂ)+OD := by
  filter_upwards [parity_eventually_original_historical_weighted_fine_offdiag_character_dyadic434
    S beta gamma K0 hS hbeta hgamma,
    eventually_ge_atTop (8:ℝ)] with L hOff hL8
  refine ⟨hL8,?_⟩
  intro hLw band slot δ ξ U V E rho K J prime signed lFine uFine β
    hU hV hScale hDyad hNrange hl hFineLow
  dsimp only
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let w := parityOriginalHistoricalActualEtaWeight434 L E V hLw
  have hLp : 0<L := by linarith
  have hEpos : 0<E := by
    rw [hScale]
    exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  have hCauchy := parity_original_historical_actual_smooth_weighted_Cauchy434
    (sourceOriginalLiteralDepth 20 L) L E V hLw hEpos hV
    band slot δ ξ rho K J alpha β signed ⌊2*Real.exp L⌋₊ hNrange
  have hGram := parity_original_historical_weighted_active_square_diag_offdiag434
    (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
    K J alpha signed ⌊2*Real.exp L⌋₊ w
  have hOD := hOff.2 band slot δ ξ U E rho K J prime signed
    lFine uFine w hU hScale hDyad hl hFineLow
  rw [hOD] at hGram
  exact ⟨hCauchy,hGram⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFixedRatioBump -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- LOCAL source smooth unit bump at every dyadic physical ordinary
e-scale c>0, with FIXED outer/inner ratio 3/2. In particular the
underlying Mathlib `someContDiffBumpBase` is evaluated at the SAME
parameter 3/2 for every c, unlike the shrinking source eta_e bump
whose rOut/rIn tends to 1 as L→∞. This avoids a moving bump BASE
profile in eventual derivative estimates. -/
def parityOriginalHistoricalFixedRatioDyadicBump434
    (c : ℝ) (hc : 0<c) : ContDiffBump c :=
  ⟨c/3,c/2,by positivity,by linarith⟩

/-- All local dyadic source bumps use the exact SAME fixed parameter
rOut/rIn=3/2. The signed physical p-2 and Q group are unaffected. -/
theorem parity_original_historical_fixed_ratio_dyadic_bump_ratio434
    (c : ℝ) (hc : 0<c) :
    (parityOriginalHistoricalFixedRatioDyadicBump434 c hc).rOut /
      (parityOriginalHistoricalFixedRatioDyadicBump434 c hc).rIn = (3/2:ℝ) := by
  change (c/2)/(c/3)=(3/2:ℝ)
  field_simp

/-- Each fixed-ratio dyadic source bump is C∞. -/
theorem parity_original_historical_fixed_ratio_dyadic_bump_smooth434
    (c : ℝ) (hc : 0<c) :
    ContDiff ℝ ∞ (fun x : ℝ =>
      ((parityOriginalHistoricalFixedRatioDyadicBump434 c hc x : ℝ):ℂ)) :=
  Complex.ofRealCLM.contDiff.comp
    (parityOriginalHistoricalFixedRatioDyadicBump434 c hc).contDiff

/-- On [2c/3,4c/3], this source dyadic bump equals 1 pointwise.
The plateau for c and 2c touches exactly at 4c/3, so a dyadic
family with these bumps can cover the entire moving e-window. -/
theorem parity_original_historical_fixed_ratio_dyadic_bump_one434
    (c : ℝ) (hc : 0<c) (x : ℝ)
    (hx : (2/3:ℝ)*c≤x ∧ x≤(4/3:ℝ)*c) :
    (parityOriginalHistoricalFixedRatioDyadicBump434 c hc x : ℝ)=1 := by
  let b := parityOriginalHistoricalFixedRatioDyadicBump434 c hc
  have hdist : |x-c|≤ c/3 := by
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  have hball : x∈Metric.closedBall c b.rIn := by
    change |x-c|≤ c/3
    exact hdist
  exact b.one_of_mem_closedBall hball

/-- Exact positive support of a dyadic source bump: it is contained
in (c/2,3c/2), and at EVERY physical c≥a its lower edge respects
the historical original e-window auxiliary bound a/2. -/
theorem parity_original_historical_fixed_ratio_dyadic_bump_support434
    (c : ℝ) (hc : 0<c) (x : ℝ)
    (hx : (parityOriginalHistoricalFixedRatioDyadicBump434 c hc x : ℝ) ≠ 0) :
    c/2<x ∧ x<(3/2:ℝ)*c := by
  let b := parityOriginalHistoricalFixedRatioDyadicBump434 c hc
  have hball : x∈Metric.ball c b.rOut := by
    rw [←b.support_eq]
    exact hx
  have hdist : |x-c|<c/2 := by
    have hh : |x-c| < b.rOut := by
      simpa only [Metric.mem_ball,Real.dist_eq] using hball
    exact hh
  constructor <;> linarith [(abs_lt.mp hdist).1,(abs_lt.mp hdist).2]

/-- The fixed ratio family is uniformly nonnegative and ≤1; it is
an actual source positive majorant after eventual finite dyadic sum. -/
theorem parity_original_historical_fixed_ratio_dyadic_bump_nonneg_le_one434
    (c : ℝ) (hc : 0<c) (x : ℝ) :
    0≤(parityOriginalHistoricalFixedRatioDyadicBump434 c hc x : ℝ) ∧
    (parityOriginalHistoricalFixedRatioDyadicBump434 c hc x : ℝ)≤1 :=
  ⟨(parityOriginalHistoricalFixedRatioDyadicBump434 c hc).nonneg,
   (parityOriginalHistoricalFixedRatioDyadicBump434 c hc).le_one⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFixedRatioRescale -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- This is the genuine ORIGINAL source local dyadic bump reference
at unit physical ordinary-e scale c=1. Its source inner/outer radii
are fixed 1/3,1/2, independent of original L and moving a=L^-88. -/
def parityOriginalFixedRatioDyadicReference434 : ContDiffBump (1:ℝ) :=
  parityOriginalHistoricalFixedRatioDyadicBump434 1 (by norm_num)

/-- Critical quantitative repair for the source e-majorant: all
bump profiles in the scaled dyadic family are EXACT rescalings of
ONE fixed reference bump at c=1. This is stronger than arbitrary
C∞ at changing near-touching radii; its derivatives have controlled
powers c^-j from the native chain rule. -/
theorem parity_original_historical_fixed_ratio_dyadic_bump_rescale434
    (c : ℝ) (hc : 0<c) (x : ℝ) :
    (parityOriginalHistoricalFixedRatioDyadicBump434 c hc x : ℝ) =
      (parityOriginalFixedRatioDyadicReference434 (x/c) : ℝ) := by
  rw [ContDiffBump.apply,ContDiffBump.apply]
  have hR := parity_original_historical_fixed_ratio_dyadic_bump_ratio434 c hc
  have hR1 : parityOriginalFixedRatioDyadicReference434.rOut /
      parityOriginalFixedRatioDyadicReference434.rIn = (3/2:ℝ) := by
    change ((1:ℝ)/2)/((1:ℝ)/3) = (3/2:ℝ)
    norm_num
  rw [hR,hR1]
  congr 1
  simp only [smul_eq_mul]
  change (c/3)⁻¹ * (x-c) = ((1:ℝ)/3)⁻¹ * (x/c-1)
  field_simp [hc.ne']

/-- ONE fixed real source smooth compact reference profile is an
ACTUAL Schwartz map, thus possesses all finite uniform derivative
seminorm constants before any physical L,k,Z or precision. -/
def parityOriginalFixedRatioDyadicReferenceSchwartz434 : 𝓢(ℝ,ℝ) :=
  parityOriginalFixedRatioDyadicReference434.hasCompactSupport.toSchwartzMap
    parityOriginalFixedRatioDyadicReference434.contDiff

/-- The reference Schwartz map evaluates to the SAME true Mathlib
fixed-ratio physical dyadic bump; no abstract surrogate cutoff. -/
theorem parity_original_historical_reference_schwartz_apply434 (x : ℝ) :
    parityOriginalFixedRatioDyadicReferenceSchwartz434 x =
      (parityOriginalFixedRatioDyadicReference434 x : ℝ) := rfl

/-- The physical source local bump derivative is the reference
fixed-profile derivative rescaled by c^-j, EXACTLY, for arbitrary
j and any physical x. No moving rOut/rIn base profile remains. -/
theorem parity_original_historical_fixed_ratio_dyadic_derivative_rescale434
    (c : ℝ) (hc : 0<c) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y : ℝ =>
      (parityOriginalHistoricalFixedRatioDyadicBump434 c hc y : ℝ)) x =
    (c⁻¹)^j *
      iteratedDeriv j (fun y : ℝ => (parityOriginalFixedRatioDyadicReference434 y : ℝ))
        (x/c) := by
  have hfun : (fun y : ℝ =>
       (parityOriginalHistoricalFixedRatioDyadicBump434 c hc y : ℝ)) =
       (fun y : ℝ => (parityOriginalFixedRatioDyadicReference434 (c⁻¹*y) : ℝ)) := by
    funext y
    simpa only [inv_mul_eq_div] using
      parity_original_historical_fixed_ratio_dyadic_bump_rescale434 c hc y
  rw [hfun]
  have hDiff : ContDiff ℝ j (fun y : ℝ =>
      (parityOriginalFixedRatioDyadicReference434 y : ℝ)) :=
    parityOriginalFixedRatioDyadicReference434.contDiff
  have h := iteratedDeriv_comp_const_mul hDiff (c⁻¹)
  rw [h]
  simp only [inv_mul_eq_div]

/-- UNIFORM source local dyadic-e cutoff C∞ derivative bound,
with the fixed Schwartz reference seminorm chosen ONCE before L,
and exact scaling c^-j. This is an actual quantitative polynomial
rate for each bump of dyadic radius c, not an assumed bound for the
full original η_e sum; the finite family assembly is separate. -/
theorem parity_original_historical_fixed_ratio_dyadic_derivative_norm_le434
    (c : ℝ) (hc : 0<c) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (fun y : ℝ =>
       (parityOriginalHistoricalFixedRatioDyadicBump434 c hc y : ℝ)) x‖ ≤
    (c⁻¹)^j *
      ((SchwartzMap.seminorm ℝ 0 j)
        parityOriginalFixedRatioDyadicReferenceSchwartz434) := by
  rw [parity_original_historical_fixed_ratio_dyadic_derivative_rescale434 c hc j x]
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hc.le) _)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_nonneg.mpr hc.le) _)
  have hh := SchwartzMap.le_seminorm' ℝ 0 j
    parityOriginalFixedRatioDyadicReferenceSchwartz434 (x/c)
  have hfun : (fun y : ℝ => (parityOriginalFixedRatioDyadicReference434 y : ℝ)) =
      (parityOriginalFixedRatioDyadicReferenceSchwartz434 : ℝ → ℝ) := by
    funext y
    rfl
  rw [hfun]
  simpa only [pow_zero,one_mul] using hh
end Green64Analytic.Parity

end

end

