module

public import Green64.Library.Sieve.Foundations.Part022
public import Green64.Library.Sieve.Foundations.Part021
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Green64.Library.Sieve.Foundations.Part020

@[expose] public section

/-!
# Sieve / Foundations / Part023

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalFourierFiniteFubini -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- The exact original 3D Fourier character exponential at a SOURCE
logarithmic point t, with native Mathlib's 2π normalization. -/
def parityOriginal3DPhysicalLogFourierPhase434
    (ξ t : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (((2*Real.pi*⟪ξ,t⟫:ℝ):ℂ)*Complex.I)

/-- Fourier phase has unit norm at every real source logarithmic
point and every real frequency, without a complex conjugation swap. -/
theorem parity_original_3d_physical_log_fourier_phase_norm434
    (ξ t : EuclideanSpace ℝ (Fin 3)) :
    ‖parityOriginal3DPhysicalLogFourierPhase434 ξ t‖=1 := by
  unfold parityOriginal3DPhysicalLogFourierPhase434
  exact Complex.norm_exp_ofReal_mul_I _

/-- A finite REAL original logarithmic physical source signal.
The weights W may be the signed b629 alpha, intrinsic H0, parity,
Dirichlet character, original k and physical n-fibre coefficients.
No positivity, factorization, or artificial shift is assumed. -/
def parityOriginal3DPhysicalFiniteSignal434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ)
    (t : ι → EuclideanSpace ℝ (Fin 3))
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) : ℂ :=
  ∑ i∈S,W i*f (t i)

/-- The source Fourier side is ONE frequency integral with the
ORIGINAL finite physical signed source W inside the twisted
per-character correlation sum, NOT an integral for every event with
separately chosen source Fourier kernel. -/
def parityOriginal3DPhysicalFiniteTwistedSource434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ)
    (t : ι → EuclideanSpace ℝ (Fin 3))
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
    (ξ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ *
    ∑i∈S,W i*parityOriginal3DPhysicalLogFourierPhase434 ξ (t i)

/-- Exact source 3D Fourier inversion of a SINGLE genuinely weighted
physical term. The same source Fourier kernel is used for all terms;
it may be the ACTUAL Parity(4.14) eta_e*eta_n pullback constructed in
preceding modules. No separate k,Z Fourier coefficient is invented. -/
theorem parity_original_3d_physical_source_one_fourier_inverse434
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
    (t : EuclideanSpace ℝ (Fin 3)) (W : ℂ) :
    W*f t = ∫ξ : EuclideanSpace ℝ (Fin 3),
      W*parityOriginal3DPhysicalLogFourierPhase434 ξ t *
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ := by
  have hInv : f t = ∫ξ : EuclideanSpace ℝ (Fin 3),
      parityOriginal3DPhysicalLogFourierPhase434 ξ t *
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ := by
    have hh : (𝓕⁻ (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))) t = f t := by
      rw [FourierTransform.fourierInv_fourier_eq]
    rw [←hh,SchwartzMap.fourierInv_coe,Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [smul_eq_mul,parityOriginal3DPhysicalLogFourierPhase434]
  rw [hInv,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  ring

/-- Each original real-3D physical Fourier character summand is
integrable against the genuine Schwartz Fourier kernel. There is no
unstated assumption about its norm or a spurious number of chars. -/
theorem parity_original_3d_physical_weighted_phase_integrable434
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
    (t : EuclideanSpace ℝ (Fin 3)) (W : ℂ) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin 3) =>
      W*parityOriginal3DPhysicalLogFourierPhase434 ξ t *
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ) := by
  let F : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ) := 𝓕 f
  have hF : Integrable (fun ξ : EuclideanSpace ℝ (Fin 3) => F ξ) := F.integrable
  have hC : Continuous (fun ξ : EuclideanSpace ℝ (Fin 3) =>
      W*parityOriginal3DPhysicalLogFourierPhase434 ξ t*F ξ) := by
    dsimp [parityOriginal3DPhysicalLogFourierPhase434]
    fun_prop
  have hBase : Integrable (fun ξ : EuclideanSpace ℝ (Fin 3) => (W:ℂ)*F ξ) :=
    hF.const_mul W
  apply hBase.mono hC.aestronglyMeasurable
  filter_upwards [] with ξ
  simpa only [norm_mul,parity_original_3d_physical_log_fourier_phase_norm434,mul_one] using (le_refl (‖W‖ * ‖F ξ‖))

/-- TRUE finite-source character and Fourier interchange:
all physical signed weights W can be brought UNDER the SAME
three-dimensional Fourier integral, with exact 2π logarithmic
phases, independent of term count, k, Z, or a conjectural TypeII
saving. For the original source W includes m',z,n physical Q/P
supports and chi; f is the actual eta_e/n Schwartz cutoff. -/
theorem parity_original_3d_physical_finite_source_fourier_fubini434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ)
    (t : ι → EuclideanSpace ℝ (Fin 3))
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) :
    parityOriginal3DPhysicalFiniteSignal434 S W t f =
    ∫ ξ : EuclideanSpace ℝ (Fin 3),
      parityOriginal3DPhysicalFiniteTwistedSource434 S W t f ξ := by
  let F : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ) := 𝓕 f
  let g : ι → EuclideanSpace ℝ (Fin 3) → ℂ := fun i ξ =>
      W i*parityOriginal3DPhysicalLogFourierPhase434 ξ (t i)*F ξ
  have hi : ∀i∈S,Integrable (g i) := by
    intro i hi
    exact parity_original_3d_physical_weighted_phase_integrable434 f (t i) (W i)
  unfold parityOriginal3DPhysicalFiniteSignal434
    parityOriginal3DPhysicalFiniteTwistedSource434
  calc
    (∑i∈S,W i*f (t i)) = ∑i∈S,∫ ξ : EuclideanSpace ℝ (Fin 3),g i ξ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact parity_original_3d_physical_source_one_fourier_inverse434 f (t i) (W i)
    _ = ∫ξ : EuclideanSpace ℝ (Fin 3),∑i∈S,g i ξ :=
      (integral_finset_sum S hi).symm
    _ = ∫ξ : EuclideanSpace ℝ (Fin 3),F ξ *
        ∑i∈S,W i*parityOriginal3DPhysicalLogFourierPhase434 ξ (t i) := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      dsimp [g]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hii
      ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFiniteFourierTrunc -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- ACTUAL physical source finite e,m',z,n/character coefficient
mass: the original signed coefficient is never replaced by a
nonexistent counting bound; every physical term retains its norm
inside a literal finite l1 mass. -/
def parityOriginal3DPhysicalFiniteCoefficientMass434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ) : ℝ :=
  ∑i∈S, ‖W i‖

/-- Source finite ℓ1 coefficient mass is nonnegative exactly,
without claiming a bound on its physical size or character count. -/
theorem parity_original_3d_physical_finite_coefficient_mass_nonneg434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ) :
    0≤parityOriginal3DPhysicalFiniteCoefficientMass434 S W := by
  unfold parityOriginal3DPhysicalFiniteCoefficientMass434
  exact Finset.sum_nonneg (fun i hi => norm_nonneg _)

/-- The same TRUE source Schwartz Fourier 3D kernel can be
interchanged with any finite physical source sum on the bounded
frequency ball. This is a Bochner Fubini identity, not the false
assertion that the signed source has positive coefficients. -/
theorem parity_original_3d_physical_source_finite_fourier_ball_fubini434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ)
    (t : ι → EuclideanSpace ℝ (Fin 3))
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
    (T : ℝ) :
    (∫ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 S W t f ξ) =
    ∑i∈S, (∫ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
      W i*parityOriginal3DPhysicalLogFourierPhase434 ξ (t i) *
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ) := by
  let B : Set (EuclideanSpace ℝ (Fin 3)) := {ξ | ‖ξ‖≤T}
  let F : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ) := 𝓕 f
  let g : ι → EuclideanSpace ℝ (Fin 3) → ℂ := fun i ξ =>
    W i*parityOriginal3DPhysicalLogFourierPhase434 ξ (t i)*F ξ
  have hIntegrable : ∀ i∈S, Integrable (g i) (volume.restrict B) := by
    intro i hi
    exact (parity_original_3d_physical_weighted_phase_integrable434
      f (t i) (W i)).integrableOn
  unfold parityOriginal3DPhysicalFiniteTwistedSource434
  have hEq (ξ : EuclideanSpace ℝ (Fin 3)) :
    F ξ * (∑i∈S,W i*parityOriginal3DPhysicalLogFourierPhase434 ξ (t i)) =
      ∑i∈S,g i ξ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [g]
    ring
  calc
    _ = ∫ξ in B, ∑i∈S,g i ξ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      exact hEq ξ
    _ = ∑i∈S,∫ξ in B,g i ξ := integral_finset_sum S hIntegrable

/-- Exact finite source weighted Fourier cancellation identity:
subtract the low-frequency 3D integral BEFORE taking abs values,
and the remainder is the original finite sum of each signed source
term's truncation remainder. No artificial #characters or #z loss. -/
theorem parity_original_3d_physical_finite_truncation_error_identity434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ)
    (t : ι → EuclideanSpace ℝ (Fin 3))
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) (T : ℝ) :
    parityOriginal3DPhysicalFiniteSignal434 S W t f -
      (∫ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 S W t f ξ) =
    ∑i∈S,W i *
      (f (t i)-
        ∫ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
          parityOriginal3DPhysicalLogFourierPhase434 ξ (t i)*
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ) := by
  rw [parity_original_3d_physical_source_finite_fourier_ball_fubini434]
  unfold parityOriginal3DPhysicalFiniteSignal434
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hInt :
      (∫ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
        W i*parityOriginal3DPhysicalLogFourierPhase434 ξ (t i)*
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ) =
      W i*(∫ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
        parityOriginal3DPhysicalLogFourierPhase434 ξ (t i)*
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ) := by
    simp_rw [mul_assoc]
    exact integral_const_mul (W i) _
  rw [hInt]
  ring

/-- ***SOURCE FINITE 3D FOURIER TRUNCATION***.
For the truly constructed historical eta_e,L with proved all-order
L-polynomial real/complex derivatives and the true fixed eta_n,
ANY finite family of original physical signed character cofactor
weights W has its exact source sum approximated by ONE genuinely
3D frequency-ball Fourier integral, with residual bounded by

   (sum_i ||W_i||) * B_H(source 3D f)/T^H.

This is the precise finite-summation/tail interaction needed by Parity
(4.15); the source `sum ||W||` and complete uniform 3D derivative
bound B_H << L^C must still be established separately before the
full summed original Type II claim. -/
theorem parity_original_historical_actual_dyadic_finite_3d_truncation434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ)
    (t : ι → EuclideanSpace ℝ (Fin 3))
    (H : ℕ) (L : ℝ) (hL : 8≤L)
    (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ x : ℝ, buf x≠0 → a≤x ∧ x≤b)
    (T : ℝ) (hT : 0<T) :
    ‖parityOriginal3DPhysicalFiniteSignal434 S W t
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport) -
      (∫ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 S W t
          (parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hL U E V Z k buf a b hBufSmooth hBufSupport) ξ)‖ ≤
    parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
      (parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport) / T^H) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hBufSmooth hBufSupport
  let c := parityOriginal3DSourceMomentFiniteBudget434 H f / T^H
  have hPoint (i : ι) :
    ‖W i*(f (t i) -
      ∫ ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
        parityOriginal3DPhysicalLogFourierPhase434 ξ (t i)*
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ)‖ ≤ ‖W i‖*c := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (parity_original_historical_actual_dyadic_eta_3d_truncation434
        H L hL U E V Z k buf a b hBufSmooth hBufSupport (t i) T hT)
      (norm_nonneg _)
  rw [parity_original_3d_physical_finite_truncation_error_identity434]
  calc
    ‖∑i∈S,W i*(f (t i)-
      ∫ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
        parityOriginal3DPhysicalLogFourierPhase434 ξ (t i)*
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ)‖ ≤
      ∑i∈S,‖W i*(f (t i)-
      ∫ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
        parityOriginal3DPhysicalLogFourierPhase434 ξ (t i)*
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ)‖ := norm_sum_le _ _
    _ ≤ ∑i∈S,‖W i‖*c := Finset.sum_le_sum (fun i hi => hPoint i)
    _ = parityOriginal3DPhysicalFiniteCoefficientMass434 S W * c := by
      unfold parityOriginal3DPhysicalFiniteCoefficientMass434
      rw [Finset.sum_mul]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLogBuffer3DFDeriv -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The original fixed logarithmic buffer supported in [-log A,log A]
is an ACTUAL compactly supported complex-valued function, not an
assumed Fourier multiplier or an L-dependent buffer. -/
theorem parity_original_historical_fixed_log_buffer_compact434
    (A : ℝ) (buf : ℝ → ℂ)
    (hBufSupport : ∀t : ℝ, buf t≠0 → -Real.log A≤t ∧ t≤Real.log A) :
    HasCompactSupport buf := by
  have hSub : Function.support buf ⊆ Set.Icc (-Real.log A) (Real.log A) := by
    intro t ht
    exact hBufSupport t ht
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal hSub isClosed_Icc)

/-- ONE ACTUAL fixed Schwartz buffer with exactly the original
source [0,log2] plateau, not a new smooth regularizer. -/
def parityOriginalHistoricalFixedLogBufferSchwartz434
    (A : ℝ) (buf : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀t : ℝ, buf t≠0 → -Real.log A≤t ∧ t≤Real.log A) :
    𝓢(ℝ,ℂ) :=
  (parity_original_historical_fixed_log_buffer_compact434 A buf hSupp).toSchwartzMap hSmooth

/-- Fixed no-L derivative envelope for the ACTUAL original smooth
one-dimensional logarithmic buffer. -/
def parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434
    (A : ℝ) (buf : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀t : ℝ, buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (J : ℕ) : ℝ :=
  ∑j∈Finset.range (J+1),
    (SchwartzMap.seminorm ℂ 0 j)
      (parityOriginalHistoricalFixedLogBufferSchwartz434 A buf hSmooth hSupp)

/-- Each original fixed log-buffer i-th scalar Fréchet derivative
is bounded by the same exact fixed profile budget at every real
argument, uniformly for all orders i≤J. -/
theorem parity_original_historical_fixed_log_buffer_fderiv_envelope434
    (A : ℝ) (buf : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀t : ℝ, buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (J i : ℕ) (hi : i≤J) (x : ℝ) :
    ‖iteratedFDeriv ℝ i buf x‖ ≤
      parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434
        A buf hSmooth hSupp J := by
  have hfun : buf = (parityOriginalHistoricalFixedLogBufferSchwartz434 A buf hSmooth hSupp : ℝ→ℂ) := by
    funext y
    rfl
  let hS := parityOriginalHistoricalFixedLogBufferSchwartz434 A buf hSmooth hSupp
  have hder : ‖iteratedFDeriv ℝ i buf x‖ =
      ‖iteratedFDeriv ℝ i (hS : ℝ→ℂ) x‖ := by
    rw [hfun]
  rw [hder,norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hAt := SchwartzMap.le_seminorm' ℂ 0 i hS x
  calc
    _ ≤ (SchwartzMap.seminorm ℂ 0 i) hS := by
      simpa only [pow_zero,one_mul] using hAt
    _ ≤ parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434 A buf hSmooth hSupp J := by
      unfold parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434
      apply Finset.single_le_sum ?_ (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      intro j hj
      exact apply_nonneg _ _

/-- The actual fixed original buffer in ANY real Euclidean three-D
logarithmic coordinate has all-order j derivative norm bounded by
j! times a fixed reference Schwartz constant, independent of
L,k,Z and original e/m prime parameters. -/
theorem parity_original_historical_fixed_log_buffer_3d_fderiv_le434
    (A : ℝ) (buf : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀t : ℝ, buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (i : Fin 3) (J : ℕ)
    (t : EuclideanSpace ℝ (Fin 3)) :
    ‖iteratedFDeriv ℝ J
      (fun x : EuclideanSpace ℝ (Fin 3) => buf (x i)) t‖ ≤
      (J.factorial:ℝ)*
        parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434
          A buf hSmooth hSupp J := by
  let f : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => x i
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_apply ℝ ℝ i).comp
      (EuclideanSpace.equiv (Fin 3) ℝ).contDiff
  have hD : ∀ (j : ℕ), 1≤j → j≤J →
      ‖iteratedFDeriv ℝ j f t‖ ≤ (1:ℝ)^j := by
    intro j hj hJ
    simpa only [one_pow] using
      (parity_original_euclidean_linear_coord_derivatives_le_one434 i j hj t)
  have hC : ∀ (j : ℕ),j≤J →
      ‖iteratedFDeriv ℝ j buf (f t)‖ ≤
        parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434 A buf hSmooth hSupp J := by
    intro j hj
    exact parity_original_historical_fixed_log_buffer_fderiv_envelope434
      A buf hSmooth hSupp J j hj (f t)
  have h := norm_iteratedFDeriv_comp_le hSmooth hf (by simp) t hC hD
  simpa only [Function.comp_def,one_pow,mul_one] using h
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFiveFactorDerivative -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The exact dimension-FIVE finite product Leibniz combinatorial
coefficient (independent of all historical source parameters).
Each underlying derivative is real Euclidean dimension THREE;
five factors are original buffers (3), eta_e and eta_n. -/
def parityOriginal3DFiveFactorDerivativeCombinatorial434 (J : ℕ) : ℝ :=
  ∑ p∈(Finset.univ : Finset (Fin 5)).sym J,
    ((p : Multiset (Fin 5)).countPerms : ℝ)

/-- Nonnegative true finite-dimensional combinatorial factor. -/
theorem parity_original_3d_five_factor_combinatorial_nonneg434 (J : ℕ) :
    0≤parityOriginal3DFiveFactorDerivativeCombinatorial434 J := by
  unfold parityOriginal3DFiveFactorDerivativeCombinatorial434
  apply Finset.sum_nonneg
  intro p hp
  exact Nat.cast_nonneg _

/-- EXACT native multivariate 5-factor Leibniz inequality, with
all orders r≤J and ONE common pointwise bound B for each original
buffer/eta factor: ∥D^J ∏_{i=0}^4 f_i∥ ≤ Comb_J B^5.
Nothing is asserted about the size of B or the SOURCE parameters;
this theorem isolates the native product combinatorics so the
individually proved Parity polynomial derivatives can be substituted. -/
theorem parity_original_3d_five_factor_derivative_le434
    (f : Fin 5 → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hf : ∀i,ContDiff ℝ ∞ (f i))
    (J : ℕ) (t : EuclideanSpace ℝ (Fin 3))
    (B : ℝ) (hB : 0≤B)
    (hEach : ∀ (i : Fin 5) (r : ℕ),r≤J →
       ‖iteratedFDeriv ℝ r (f i) t‖≤B) :
    ‖iteratedFDeriv ℝ J
      (fun x : EuclideanSpace ℝ (Fin 3) => ∏i : Fin 5,f i x) t‖ ≤
      parityOriginal3DFiveFactorDerivativeCombinatorial434 J * B^5 := by
  let S : Finset (Fin 5) := Finset.univ
  have hBase := norm_iteratedFDeriv_prod_le (u:=S) (f:=f)
    (N:=∞) (by intro i hi; exact hf i) (by simp : (J:ℕ∞ω)≤∞)
    (x:=t)
  have hPoint (p : Sym (Fin 5) J) :
      ((p : Multiset (Fin 5)).countPerms : ℝ) *
        (∏ i∈S,‖iteratedFDeriv ℝ (Multiset.count i (p : Multiset (Fin 5)))
          (f i) t‖) ≤
      ((p : Multiset (Fin 5)).countPerms : ℝ) * B^5 := by
    have hProd : (∏ i∈S,‖iteratedFDeriv ℝ (Multiset.count i (p : Multiset (Fin 5)))
          (f i) t‖) ≤ B^5 := by
      calc
        _ ≤ ∏_i∈S,B := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact norm_nonneg _
          intro i hi
          have hCount : Multiset.count i (p : Multiset (Fin 5))≤J := by
            have hh := Multiset.count_le_card i (p : Multiset (Fin 5))
            simpa only [Sym.card_coe] using hh
          exact hEach i _ hCount
        _ = B^5 := by
          rw [Finset.prod_const]
          have hh : S.card=5 := by dsimp [S]; simp
          rw [hh]
    exact mul_le_mul_of_nonneg_left hProd (Nat.cast_nonneg _)
  change ‖iteratedFDeriv ℝ J (fun x => ∏i∈S,f i x) t‖ ≤ _
  calc
    _ ≤ ∑p∈S.sym J,
        ((p : Multiset (Fin 5)).countPerms : ℝ) *
        (∏ i∈S,‖iteratedFDeriv ℝ (Multiset.count i (p : Multiset (Fin 5)))
          (f i) t‖) := hBase
    _ ≤ ∑p∈S.sym J,((p : Multiset (Fin 5)).countPerms : ℝ)*B^5 :=
      Finset.sum_le_sum (fun p hp => hPoint p)
    _ = parityOriginal3DFiveFactorDerivativeCombinatorial434 J * B^5 := by
      unfold parityOriginal3DFiveFactorDerivativeCombinatorial434
      exact (Finset.sum_mul _ _ _).symm
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFiveFactorFixedBudget -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Exact fixed, L-INDEPENDENT source coefficient budget for five
actual original 3D Parity factors: fixed log buffer (three copies),
finite-dyadic eta_e and fixed eta_n, at all derivatives up to J.
The single j-th term is j! times the ACTUAL fixed Schwartz reference
seminorm envelopes, not a guessed analytic constant. -/
def parityOriginalHistoricalFiveFactorFixedBudget434
    (A : ℝ) (buf : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀t : ℝ, buf t ≠ 0 → -Real.log A≤t ∧ t≤Real.log A)
    (J : ℕ) : ℝ :=
  1 + ∑r∈Finset.range (J+1), (r.factorial:ℝ)*(
      parityOriginalEtaEDerivativeFixedEnvelope434 r +
      parityOriginalEtaNDerivativeFixedEnvelope434 r +
      parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434 A buf hSmooth hSupp r)

/-- Three ACTUAL source seminorm envelopes are each nonnegative. -/
theorem parity_original_historical_five_factor_fixed_envelopes_nonneg434
    (A : ℝ) (buf : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀t : ℝ, buf t ≠ 0 → -Real.log A≤t ∧ t≤Real.log A)
    (r : ℕ) :
    0≤parityOriginalEtaEDerivativeFixedEnvelope434 r ∧
    0≤parityOriginalEtaNDerivativeFixedEnvelope434 r ∧
    0≤parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434 A buf hSmooth hSupp r := by
  refine ⟨?_,?_,?_⟩
  · unfold parityOriginalEtaEDerivativeFixedEnvelope434
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (by norm_num) (apply_nonneg _ _)
  · unfold parityOriginalEtaNDerivativeFixedEnvelope434
    exact Finset.sum_nonneg (fun i hi=>apply_nonneg _ _)
  · unfold parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434
    exact Finset.sum_nonneg (fun i hi=>apply_nonneg _ _)

/-- The true fixed reference envelope M_J is ≥1. It depends only on
one fixed source logarithmic cutoff and J, not on L,k,Z,χ or rho. -/
theorem parity_original_historical_five_factor_fixed_budget_ge_one434
    (A : ℝ) (buf : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀t : ℝ, buf t ≠ 0 → -Real.log A≤t ∧ t≤Real.log A)
    (J : ℕ) :
    1≤parityOriginalHistoricalFiveFactorFixedBudget434 A buf hSmooth hSupp J := by
  unfold parityOriginalHistoricalFiveFactorFixedBudget434
  have hnonneg : 0≤∑r∈Finset.range (J+1),(r.factorial:ℝ)*(
      parityOriginalEtaEDerivativeFixedEnvelope434 r+
      parityOriginalEtaNDerivativeFixedEnvelope434 r+
      parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434 A buf hSmooth hSupp r) := by
    apply Finset.sum_nonneg
    intro r hr
    obtain ⟨he,hn,hb⟩ := parity_original_historical_five_factor_fixed_envelopes_nonneg434
      A buf hSmooth hSupp r
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  linarith

/-- Each individual SOURCE derivative coefficient for either eta_e,
eta_n or fixed buffer (multiplied by its own r!) costs at most the
SAME explicitly constructed M_J for all 0≤ r≤J. -/
theorem parity_original_historical_five_factor_individual_constant_le434
    (A : ℝ) (buf : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀t : ℝ, buf t ≠ 0 → -Real.log A≤t ∧ t≤Real.log A)
    (J r : ℕ) (hr : r≤J) :
    (r.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 r ≤
      parityOriginalHistoricalFiveFactorFixedBudget434 A buf hSmooth hSupp J ∧
    (r.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 r ≤
      parityOriginalHistoricalFiveFactorFixedBudget434 A buf hSmooth hSupp J ∧
    (r.factorial:ℝ)*parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434
      A buf hSmooth hSupp r ≤
      parityOriginalHistoricalFiveFactorFixedBudget434 A buf hSmooth hSupp J := by
  let e := parityOriginalEtaEDerivativeFixedEnvelope434 r
  let n := parityOriginalEtaNDerivativeFixedEnvelope434 r
  let b := parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434 A buf hSmooth hSupp r
  let s : ℕ → ℝ := fun i => (i.factorial:ℝ)*(
    parityOriginalEtaEDerivativeFixedEnvelope434 i+
    parityOriginalEtaNDerivativeFixedEnvelope434 i+
    parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434 A buf hSmooth hSupp i)
  let R := ∑i∈Finset.range (J+1),s i
  have hNonneg : ∀ (i : ℕ), i ∈ Finset.range (J+1) → (0:ℝ) ≤ s i := by
    intro i hi
    obtain ⟨he,hn,hb⟩ := parity_original_historical_five_factor_fixed_envelopes_nonneg434
      A buf hSmooth hSupp i
    exact mul_nonneg (Nat.cast_nonneg _) (by positivity)
  have hSingle : s r ≤ R :=
    Finset.single_le_sum hNonneg (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  obtain ⟨he,hn,hb⟩ := parity_original_historical_five_factor_fixed_envelopes_nonneg434
    A buf hSmooth hSupp r
  change (r.factorial:ℝ)*e≤1+R ∧ (r.factorial:ℝ)*n≤1+R ∧
    (r.factorial:ℝ)*b≤1+R
  have hR : 0≤R := Finset.sum_nonneg hNonneg
  have hCoeff : 0≤(r.factorial:ℝ) := Nat.cast_nonneg _
  dsimp [s,e,n,b] at hSingle ⊢
  constructor
  · nlinarith [hSingle]
  constructor <;> nlinarith [hSingle]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualFiveFactors -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Literal FIVE factors of the ACTUAL original Parity (4.14)
real Euclidean 3D source cutoff: three fixed real-log buffers,
constructed moving η_e,L of its exact e(t)/E pullback and fixed
η_n of its exact h=-2 n(t)/V pullback.
All five factors share the SAME source logarithmic coordinate t.
No arbitrary Schwartz surrogate or Fourier tail weight. -/
def parityOriginalHistoricalActualFive3DFactors434
    (L U E V Z : ℝ) (hL : 8≤L) (k : ℤ)
    (buf : ℝ → ℂ) : Fin 5 → EuclideanSpace ℝ (Fin 3) → ℂ :=
  ![(fun t => buf (t 0)),
    (fun t => buf (t 1)),
    (fun t => buf (t 2)),
    (fun t => parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL
      (parityOriginalHistoricalEtaELogArg434 U E k
        (EuclideanSpace.equiv (Fin 3) ℝ t))),
    (fun t => parityOriginalHistoricalActualEtaN434
      (parityOriginalHistoricalEtaNLogArg434 U V Z k
        (EuclideanSpace.equiv (Fin 3) ℝ t)))]

/-- This is a FACTORIZATION of the actual source η_eη_n buffered
Euclidean 3D cutoff; all source h=-2 nonlinear arguments and buffers
are unchanged. -/
theorem parity_original_historical_actual_five_product_eq_schwartz434
    (L U E V Z : ℝ) (hL : 8≤L) (k : ℤ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x : ℝ, buf x≠0 → a≤x ∧ x≤b)
    (t : EuclideanSpace ℝ (Fin 3)) :
    (∏ i : Fin 5,
      parityOriginalHistoricalActualFive3DFactors434 L U E V Z hL k buf i t) =
    parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hBufSmooth hBufSupport t := by
  change (∏ i : Fin 5,
      parityOriginalHistoricalActualFive3DFactors434 L U E V Z hL k buf i t) =
    parityOriginalHistoricalPulledBuffered3D434 U E V Z k buf
      (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL)
      parityOriginalHistoricalActualEtaN434
      (EuclideanSpace.equiv (Fin 3) ℝ t)
  rw [Fin.prod_univ_five]
  change buf (t 0) * buf (t 1) * buf (t 2) *
      parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL
        (parityOriginalHistoricalEtaELogArg434 U E k
          (EuclideanSpace.equiv (Fin 3) ℝ t)) *
      parityOriginalHistoricalActualEtaN434
        (parityOriginalHistoricalEtaNLogArg434 U V Z k
          (EuclideanSpace.equiv (Fin 3) ℝ t)) =
    buf (t 0) * buf (t 1) * buf (t 2) *
      (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL
        (parityOriginalHistoricalEtaELogArg434 U E k
          (EuclideanSpace.equiv (Fin 3) ℝ t)) *
       parityOriginalHistoricalActualEtaN434
        (parityOriginalHistoricalEtaNLogArg434 U V Z k
          (EuclideanSpace.equiv (Fin 3) ℝ t)))
  ring

/-- Each of the FIVE actual original source 3D cutoff factors is
C∞, with its REAL source nonlinear log arguments. This property
requires only SOURCE smooth η_e,L/η_n and three fixed buffers. -/
theorem parity_original_historical_actual_five_factors_smooth434
    (L U E V Z : ℝ) (hL : 8≤L) (k : ℤ)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf) :
    ∀ i : Fin 5,
      ContDiff ℝ ∞ (parityOriginalHistoricalActualFive3DFactors434
        L U E V Z hL k buf i) := by
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun t : EuclideanSpace ℝ (Fin 3) => buf (t 0))
    fun_prop
  · change ContDiff ℝ ∞ (fun t : EuclideanSpace ℝ (Fin 3) => buf (t 1))
    fun_prop
  · change ContDiff ℝ ∞ (fun t : EuclideanSpace ℝ (Fin 3) => buf (t 2))
    fun_prop
  · change ContDiff ℝ ∞ (fun t : EuclideanSpace ℝ (Fin 3) =>
      parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL
        (parityOriginalHistoricalEtaELogArg434 U E k
          (EuclideanSpace.equiv (Fin 3) ℝ t)))
    exact (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL).comp
      ((parity_original_historical_eta_e_log_arg_smooth434 U E k).comp
        (EuclideanSpace.equiv (Fin 3) ℝ).contDiff)
  · change ContDiff ℝ ∞ (fun t : EuclideanSpace ℝ (Fin 3) =>
      parityOriginalHistoricalActualEtaN434
        (parityOriginalHistoricalEtaNLogArg434 U V Z k
          (EuclideanSpace.equiv (Fin 3) ℝ t)))
    exact parity_original_historical_actual_eta_n_smooth434.comp
      ((parity_original_historical_eta_n_log_arg_smooth434 U V Z k).comp
        (EuclideanSpace.equiv (Fin 3) ℝ).contDiff)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFiveFactorLargeThreshold -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Monotonic original Parity (4.14) e-window source derivative
threshold 2 A r! ≤ 2 A J! for all r≤J. -/
theorem parity_original_eta_e_threshold_mono434
    (A : ℝ) (hA : 0≤A) (J r : ℕ) (hr : r≤J)
    (L : ℝ) (hLarge : 2*A*(J.factorial:ℝ)≤L) :
    2*A*(r.factorial:ℝ)≤L := by
  have hh : (r.factorial:ℝ)≤(J.factorial:ℝ) := by
    exact_mod_cast Nat.factorial_le hr
  have hc : 0≤2*A := by positivity
  have hm := mul_le_mul_of_nonneg_left hh hc
  nlinarith [hm,hLarge]

/-- Monotonic original h=-2 n-window derivative threshold
8A²r!2^r+r!A ≤ 8A²J!2^J+J!A for all r≤J. -/
theorem parity_original_eta_n_threshold_mono434
    (A : ℝ) (hA : 0≤A) (J r : ℕ) (hr : r≤J)
    (L : ℝ)
    (hLarge : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
      (J.factorial:ℝ)*A≤L) :
    8*A^2*(r.factorial:ℝ)*(2:ℝ)^r+
      (r.factorial:ℝ)*A≤L := by
  have hFac : (r.factorial:ℝ)≤(J.factorial:ℝ) := by
    exact_mod_cast Nat.factorial_le hr
  have hPow : (2:ℝ)^r≤(2:ℝ)^J := pow_le_pow_right₀ (by norm_num) hr
  have hCoeff : 0≤8*A^2 := by positivity
  have hFPos : 0≤(J.factorial:ℝ) := Nat.cast_nonneg _
  have hProd : (r.factorial:ℝ)*(2:ℝ)^r≤(J.factorial:ℝ)*(2:ℝ)^J :=
    mul_le_mul hFac hPow (by positivity) hFPos
  have hT1 := mul_le_mul_of_nonneg_left hProd hCoeff
  have hT2 := mul_le_mul_of_nonneg_right hFac hA
  nlinarith [hT1,hT2,hLarge]

/-- For L≥8 and K0≥0, original 3D log-order polynomial exponent
(K0+89)(r+1) is increasing in derivative order r, so the same
worst-order J source envelope controls each r≤J. -/
theorem parity_original_3d_source_log_power_mono434
    (L K0 : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (J r : ℕ) (hr : r≤J) :
    L^((K0+89)*((r:ℝ)+1))≤L^((K0+89)*((J:ℝ)+1)) := by
  have hL1 : 1≤L := by linarith
  apply Real.rpow_le_rpow_of_exponent_le hL1
  have hh : (r:ℝ)≤(J:ℝ) := by exact_mod_cast hr
  exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

/-- The common physical five-factor source polynomial weight
R_J(L)=L^((K0+89)(J+1)) is ≥1 on the original domain L≥8,K0≥0. -/
theorem parity_original_3d_source_log_power_ge_one434
    (L K0 : ℝ) (hL : 8≤L) (hK0 : 0≤K0) (J : ℕ) :
    1≤L^((K0+89)*((J:ℝ)+1)) := by
  apply Real.one_le_rpow (by linarith)
  exact mul_nonneg (by linarith) (by positivity)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFiveFactorPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Each of the five literal original Parity (4.14) source cutoff
factors (3 fixed buffers plus moving η_e and fixed η_n) has
uniform order-r Fréchet derivative bound
     ||D^r f_i|| ≤ M_J * L^((K0+89)(J+1))
on the real original fixed log cube, for EVERY r≤J and 0≤ i<5.
The true source thresholds on L depend only on J,A, not k,Z,
e,m,χ, signed epsilon, or target Fourier precision. -/
theorem parity_original_historical_actual_five_factors_all_order_polylog434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 → -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J : ℕ)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
       (J.factorial:ℝ)*A≤L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ∀ (i : Fin 5) (r : ℕ), r≤J →
      ‖iteratedFDeriv ℝ r
        (parityOriginalHistoricalActualFive3DFactors434 L U E V Z hL k buf i) t‖ ≤
      parityOriginalHistoricalFiveFactorFixedBudget434 A buf hBufSmooth hBufSupport J *
        L^((K0+89)*((J:ℝ)+1)) := by
  let M := parityOriginalHistoricalFiveFactorFixedBudget434
    A buf hBufSmooth hBufSupport J
  let R := L^((K0+89)*((J:ℝ)+1))
  have hM : 1≤M := parity_original_historical_five_factor_fixed_budget_ge_one434
    A buf hBufSmooth hBufSupport J
  have hR : 1≤R := parity_original_3d_source_log_power_ge_one434 L K0 hL hK0 J
  have hMR : 0≤M := by linarith
  have hRR : 0≤R := by linarith
  have hB (r : ℕ) (hr : r≤J) :
      (r.factorial:ℝ)*parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434
        A buf hBufSmooth hBufSupport r ≤ M :=
    (parity_original_historical_five_factor_individual_constant_le434
      A buf hBufSmooth hBufSupport J r hr).2.2
  have hEE (r : ℕ) (hr : r≤J) :
      (r.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 r ≤ M :=
    (parity_original_historical_five_factor_individual_constant_le434
      A buf hBufSmooth hBufSupport J r hr).1
  have hNN (r : ℕ) (hr : r≤J) :
      (r.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 r ≤ M :=
    (parity_original_historical_five_factor_individual_constant_le434
      A buf hBufSmooth hBufSupport J r hr).2.1
  have hPower (r : ℕ) (hr : r≤J) :
      L^((K0+89)*((r:ℝ)+1)) ≤ R :=
    parity_original_3d_source_log_power_mono434 L K0 hL hK0 J r hr
  have hBase (i : Fin 3) (r : ℕ) (hr : r≤J) :
      ‖iteratedFDeriv ℝ r
        (fun x : EuclideanSpace ℝ (Fin 3) => buf (x i)) t‖ ≤ M*R := by
    have hh := parity_original_historical_fixed_log_buffer_3d_fderiv_le434
      A buf hBufSmooth hBufSupport i r t
    calc
      _ ≤ (r.factorial:ℝ)*parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434
          A buf hBufSmooth hBufSupport r := hh
      _ ≤ M := hB r hr
      _ = M*1 := by ring
      _ ≤ M*R := mul_le_mul_of_nonneg_left hR hMR
  intro i r hr
  fin_cases i
  · exact hBase 0 r hr
  · exact hBase 1 r hr
  · exact hBase 2 r hr
  · have hThreshold := parity_original_eta_e_threshold_mono434
      A hA.le J r hr L hLargeE
    have hh := parity_original_historical_actual_eta_e_3d_composed_polylog434
      L U E K0 A k hL hK0 hU hE hk hA r hThreshold t h0 h1
    change ‖iteratedFDeriv ℝ r
      ((parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) ∘
       (fun x : EuclideanSpace ℝ (Fin 3) =>
         parityOriginalHistoricalEtaELogArg434 U E k
           (EuclideanSpace.equiv (Fin 3) ℝ x))) t‖ ≤ M*R
    calc
      _ ≤ (r.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 r *
          L^((K0+89)*((r:ℝ)+1)) := hh
      _ ≤ M*L^((K0+89)*((r:ℝ)+1)) := by
        exact mul_le_mul_of_nonneg_right (hEE r hr) (Real.rpow_nonneg (by linarith : 0≤L) _)
      _ ≤ M*R := mul_le_mul_of_nonneg_left (hPower r hr) hMR
  · have hThreshold := parity_original_eta_n_threshold_mono434
      A hA.le J r hr L hLargeN
    have hh := parity_original_historical_actual_eta_n_3d_composed_polylog434
      L U V Z K0 A k hL hK0 hU hV hUV hk hZ hZupper
      hA r hThreshold t h0 h1 h2
    change ‖iteratedFDeriv ℝ r
      (parityOriginalHistoricalActualEtaN434 ∘
       (fun x : EuclideanSpace ℝ (Fin 3) =>
         parityOriginalHistoricalEtaNLogArg434 U V Z k
           (EuclideanSpace.equiv (Fin 3) ℝ x))) t‖ ≤ M*R
    calc
      _ ≤ (r.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 r *
          L^((K0+89)*((r:ℝ)+1)) := hh
      _ ≤ M*L^((K0+89)*((r:ℝ)+1)) := by
        exact mul_le_mul_of_nonneg_right (hNN r hr) (Real.rpow_nonneg (by linarith : 0≤L) _)
      _ ≤ M*R := mul_le_mul_of_nonneg_left (hPower r hr) hMR
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFull3DSourceDerivative -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- Fixed SOURCE constant for the genuine original five-factor
three-dimensional logarithmic Parity (4.14) Schwartz cutoff.
Depends on the fixed buffer, its support radius, and derivative
order J, but NOT on L,k,Z,epsilon,chi, nor frequency truncation. -/
def parityOriginalHistoricalFull3DFixedDerivativeK434
    (A : ℝ) (buf : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀ (s : ℝ), buf s ≠ 0 → -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J : ℕ) : ℝ :=
  parityOriginal3DFiveFactorDerivativeCombinatorial434 J *
    (parityOriginalHistoricalFiveFactorFixedBudget434 A buf hSmooth hSupp J)^5

/-- Actual full original Parity (4.14) complex 3D kernel has all
Fréchet derivatives of order J bounded by the genuine polynomial
L^((5*(K0+89))*(J+1)) on the FIXED real 3D logarithmic buffer box.
This uses the EXACT five source factors, including eta_e(L^-88),
eta_n with the h=-2 correction and the three real log buffers.
No hypothetical Fourier moment or 4.17 cancellation is assumed. -/
theorem parity_original_historical_actual_full_3d_source_derivative_on_box434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 → -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J : ℕ)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
       (J.factorial:ℝ)*A≤L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ‖iteratedFDeriv ℝ J
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport : EuclideanSpace ℝ (Fin 3) → ℂ) t‖ ≤
      parityOriginalHistoricalFull3DFixedDerivativeK434 A buf hBufSmooth
        hBufSupport J * L^((5*(K0+89))*((J:ℝ)+1)) := by
  let F := parityOriginalHistoricalActualFive3DFactors434 L U E V Z hL k buf
  let M := parityOriginalHistoricalFiveFactorFixedBudget434 A buf hBufSmooth hBufSupport J
  let R := L^((K0+89)*((J:ℝ)+1))
  have hMR : 0≤M*R := by
    have hm := parity_original_historical_five_factor_fixed_budget_ge_one434 A buf hBufSmooth hBufSupport J
    have hr := parity_original_3d_source_log_power_ge_one434 L K0 hL hK0 J
    exact mul_nonneg (by linarith) (by linarith)
  have hFive := parity_original_3d_five_factor_derivative_le434
    F (parity_original_historical_actual_five_factors_smooth434
      L U E V Z hL k buf hBufSmooth)
    J t (M*R) hMR
    (parity_original_historical_actual_five_factors_all_order_polylog434
      L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
      buf hBufSmooth hBufSupport J hLargeE hLargeN t h0 h1 h2)
  have hEq := parity_original_historical_actual_five_product_eq_schwartz434
    L U E V Z hL k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  have hfun : (fun x : EuclideanSpace ℝ (Fin 3) => ∏i : Fin 5,F i x) =
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport : EuclideanSpace ℝ (Fin 3) → ℂ) := by
    funext x
    exact hEq x
  rw [hfun] at hFive
  have hPower : R^5=L^((5*(K0+89))*((J:ℝ)+1)) := by
    dsimp [R]
    rw [←Real.rpow_natCast (L^((K0+89)*((J:ℝ)+1))) 5]
    rw [←Real.rpow_mul (by linarith : 0≤L)]
    congr 1
    ring
  calc
    _ ≤ parityOriginal3DFiveFactorDerivativeCombinatorial434 J * (M*R)^5 := hFive
    _ = parityOriginalHistoricalFull3DFixedDerivativeK434 A buf
          hBufSmooth hBufSupport J * L^((5*(K0+89))*((J:ℝ)+1)) := by
        unfold parityOriginalHistoricalFull3DFixedDerivativeK434
        rw [mul_pow,hPower]
        ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFixed3DCube -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The TRUE ORIGINAL fixed logarithmic 3D box, transported into
the Euclidean real inner product coordinates of Mathlib's Fourier
transform, without introducing a sup-norm Fourier transform. -/
def parityOriginalHistoricalEuclideanFixedLogCube434 (A : ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  (EuclideanSpace.equiv (Fin 3) ℝ) ⁻¹'
    (Set.Icc (fun _ : Fin 3 => -Real.log A) (fun _ : Fin 3 => Real.log A))

/-- The genuine original 3D fixed log cube is COMPACT; in
particular, its Euclidean radius can be fixed BEFORE any L,k,Z or
Fourier derivative order is selected. -/
theorem parity_original_historical_euclidean_fixed_log_cube_compact434
    (A : ℝ) : IsCompact (parityOriginalHistoricalEuclideanFixedLogCube434 A) := by
  unfold parityOriginalHistoricalEuclideanFixedLogCube434
  exact ((EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage).mpr
    isCompact_Icc

/-- Original fixed log box permits one explicit EXISTENTIAL radius
R≥1 bounding all Euclidean 3D source log points; R depends ONLY
on fixed original buffer A. It does not depend on L,k,Z, signed
parity epsilon, characters or required frequency accuracy. -/
theorem parity_original_historical_euclidean_fixed_log_cube_radius_exists434
    (A : ℝ) :
    ∃ R : ℝ, 1≤R ∧
      ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A, ‖t‖≤R := by
  obtain ⟨R,hR⟩ :=
    (parity_original_historical_euclidean_fixed_log_cube_compact434 A).isBounded.exists_norm_le
  refine ⟨max 1 R,le_max_left _ _,?_⟩
  intro t ht
  exact (hR t ht).trans (le_max_right _ _)

/-- Membership of a Euclidean 3D logarithmic point in the TRUE
original fixed dyadic buffer box is exactly the three original
coordinate inequalities t_i ∈ [-log A,log A], no hidden fourth
coordinate or product-sup norm assumption. -/
theorem parity_original_historical_fixed_3d_cube_coordinates434
    (A : ℝ) (t : EuclideanSpace ℝ (Fin 3))
    (ht : t∈parityOriginalHistoricalEuclideanFixedLogCube434 A) :
    (∀ i : Fin 3,-Real.log A≤t i ∧ t i≤Real.log A) := by
  change (fun _ : Fin 3 => -Real.log A) ≤
      (EuclideanSpace.equiv (Fin 3) ℝ t) ∧
      (EuclideanSpace.equiv (Fin 3) ℝ t) ≤
      (fun _ : Fin 3 => Real.log A) at ht
  intro i
  exact ⟨ht.1 i,ht.2 i⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFull3DSeminorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The Schwartz support of the ORIGINAL real source moving
η_e,L, fixed η_n and THREE logarithmic buffers is contained in
the EXACT FIXED Euclidean cube, uniformly in L,k,Z,U,E,V.
The physical original nonlinear log source is unchanged. -/
theorem parity_original_historical_actual_source_schwartz_tsupport_cube434
    (L U E V Z A : ℝ) (hL : 8≤L) (k : ℤ)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A) :
    tsupport (parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf (-Real.log A) (Real.log A)
      hBufSmooth hBufSupport : EuclideanSpace ℝ (Fin 3) → ℂ) ⊆
      parityOriginalHistoricalEuclideanFixedLogCube434 A := by
  let etaE := parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL
  let etaN := parityOriginalHistoricalActualEtaN434
  let F := (parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport : EuclideanSpace ℝ (Fin 3) → ℂ)
  have hClosed : IsClosed (parityOriginalHistoricalEuclideanFixedLogCube434 A) :=
    isClosed_Icc.preimage (EuclideanSpace.equiv (Fin 3) ℝ).continuous
  have hSupp : Function.support F ⊆ parityOriginalHistoricalEuclideanFixedLogCube434 A := by
    intro t ht
    have hval : F t ≠ 0 := ht
    have hEval := parity_original_historical_pulled_euclidean_3d_apply434
      U E V Z k buf etaE etaN (-Real.log A) (Real.log A)
      hBufSmooth (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL)
      parity_original_historical_actual_eta_n_smooth434 hBufSupport t
    have hs : parityOriginalHistoricalPulledBuffered3D434
        U E V Z k buf etaE etaN (EuclideanSpace.equiv (Fin 3) ℝ t) ≠ 0 := by
      intro hz
      exact hval (hEval.trans hz)
    have hBox := parity_original_historical_pulled_buffered_3d_support434
      U E V Z k buf etaE etaN (-Real.log A) (Real.log A) hBufSupport hs
    exact hBox
  exact closure_minimal hSupp hClosed

/-- The full original 3D source Schwartz SEMINORM of arbitrary
polynomial weight p and derivative order J is genuinely controlled
by one fixed source constant times L^(5(K0+89)(J+1)).

The fixed real 3D cube radius R is chosen BEFORE L,k,Z; all local
analytic derivative bounds on the cube were proved from the ACTUAL
source eta_e, eta_n and three buffer factors. Outside it, every
Fréchet derivative vanishes by the native Schwartz support lemma.
No source Fourier moment or 4.17 saving is assumed. -/
theorem parity_original_historical_actual_full_3d_source_seminorm_polylog434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J p : ℕ)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
       (J.factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    (SchwartzMap.seminorm ℂ p J)
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) ≤
      R^p * parityOriginalHistoricalFull3DFixedDerivativeK434
        A buf hBufSmooth hBufSupport J *
        L^((5*(K0+89))*((J:ℝ)+1)) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  let C := parityOriginalHistoricalFull3DFixedDerivativeK434
    A buf hBufSmooth hBufSupport J
  let P := L^((5*(K0+89))*((J:ℝ)+1))
  have hM1 := parity_original_historical_five_factor_fixed_budget_ge_one434
    A buf hBufSmooth hBufSupport J
  have hCoeff : 0≤C := mul_nonneg
    (parity_original_3d_five_factor_combinatorial_nonneg434 J)
    (pow_nonneg (by linarith : 0≤parityOriginalHistoricalFiveFactorFixedBudget434
      A buf hBufSmooth hBufSupport J) 5)
  have hP : 0≤P := Real.rpow_nonneg (by linarith : 0≤L) _
  have hRpow : 0≤R^p := pow_nonneg (by linarith) _
  have hM : 0≤R^p*C*P := by positivity
  have hTSupport := parity_original_historical_actual_source_schwartz_tsupport_cube434
    L U E V Z A hL k buf hBufSmooth hBufSupport
  apply SchwartzMap.seminorm_le_bound ℂ p J f hM
  intro t
  by_cases ht : t∈parityOriginalHistoricalEuclideanFixedLogCube434 A
  · have hc := parity_original_historical_fixed_3d_cube_coordinates434 A t ht
    have hD := parity_original_historical_actual_full_3d_source_derivative_on_box434
      L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper
      hA buf hBufSmooth hBufSupport J hLargeE hLargeN t
      (hc 0) (hc 1) (hc 2)
    have hNorm : ‖t‖^p≤R^p :=
      pow_le_pow_left₀ (norm_nonneg t) (hCubeR t ht) p
    calc
      ‖t‖^p * ‖iteratedFDeriv ℝ J (f : EuclideanSpace ℝ (Fin 3) → ℂ) t‖ ≤
        R^p * ‖iteratedFDeriv ℝ J (f : EuclideanSpace ℝ (Fin 3) → ℂ) t‖ :=
          mul_le_mul_of_nonneg_right hNorm (norm_nonneg _)
      _ ≤ R^p*(C*P) := mul_le_mul_of_nonneg_left hD hRpow
      _ = R^p*C*P := by ring
  · have hnot : t∉tsupport (f : EuclideanSpace ℝ (Fin 3) → ℂ) :=
      fun h => ht (hTSupport h)
    have hNo : (iteratedFDeriv ℝ J
        (f : EuclideanSpace ℝ (Fin 3) → ℂ)) t = 0 := by
      have hs : t∉Function.support (iteratedFDeriv ℝ J
          (f : EuclideanSpace ℝ (Fin 3) → ℂ)) :=
        fun h => hnot (support_iteratedFDeriv_subset J h)
      exact not_not.mp hs
    rw [hNo,norm_zero,mul_zero]
    exact hM
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFull3DMomentBound -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- Fully explicit fixed derivative/source constant for Parity's 3D
pre-Fourier Schwartz seminorm sum through order J. All terms are
actual SOURCE constants: fixed 3D Lebesgue geometry, the fixed
logarithmic cube radius, and the five-factor source Schwartz
reference derivatives. This coefficient is fixed BEFORE L,k,Z. -/
def parityOriginalHistoricalFull3DSourceSeminormFixedK434
    (A R : ℝ) (buf : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀ (s : ℝ), buf s ≠ 0 → -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J : ℕ) : ℝ :=
  (2:ℝ)^J * parityOriginal3DSourceGeometricConstant434 *
    (1+R^((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)) *
    ∑j∈Finset.range (J+1),
      parityOriginalHistoricalFull3DFixedDerivativeK434 A buf hSmooth hSupp j

/-- Exact SOURCE finite 3D Schwartz derivative budget B_N of the
constructed original η_e,L η_n log kernel, for ANY N≤J, is
controlled by ONE L-INDEPENDENT fixed reference constant times
L^(5(K0+89)(J+1)). This is the missing finite sum of true global
source seminorms and does not postulate Fourier moment smallness. -/
theorem parity_original_historical_full_3d_finite_seminorm_budget_polylog434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J N : ℕ) (hNJ : N≤J)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
       (J.factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    parityOriginal3DSourceFiniteSeminormBudget434 N
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) ≤
      parityOriginalHistoricalFull3DSourceSeminormFixedK434 A R buf
        hBufSmooth hBufSupport J *
        L^((5*(K0+89))*((J:ℝ)+1)) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf (-Real.log A) (Real.log A)
      hBufSmooth hBufSupport
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let C : ℝ := parityOriginal3DSourceGeometricConstant434
  let K : ℕ → ℝ := fun j =>
    parityOriginalHistoricalFull3DFixedDerivativeK434 A buf hBufSmooth hBufSupport j
  let M : ℝ := ∑j∈Finset.range (J+1),K j
  let Rpow : ℝ := L^((5*(K0+89))*((J:ℝ)+1))
  let D : ℝ := (2:ℝ)^J*C*(1+R^P)*M
  have hK (j : ℕ) : 0≤K j := by
    dsimp [K,parityOriginalHistoricalFull3DFixedDerivativeK434]
    apply mul_nonneg (parity_original_3d_five_factor_combinatorial_nonneg434 j)
    apply pow_nonneg
    have hge := parity_original_historical_five_factor_fixed_budget_ge_one434
      A buf hBufSmooth hBufSupport j
    linarith
  have hM : 0≤M := Finset.sum_nonneg (fun i hi=>hK i)
  have hC : 0≤C := parity_original_3d_source_geometric_constant_nonneg434
  have hRpos : 0≤R^P := pow_nonneg (by linarith) _
  have hRpow : 0≤Rpow := Real.rpow_nonneg (by linarith) _
  have hD : 0≤D := by dsimp [D]; positivity
  have h0 (j : ℕ) (hj : j≤J) :
      (SchwartzMap.seminorm ℂ 0 j) f ≤ K j * Rpow := by
    have hLE := parity_original_eta_e_threshold_mono434
      A hA.le J j hj L hLargeE
    have hLN := parity_original_eta_n_threshold_mono434
      A hA.le J j hj L hLargeN
    have hs := parity_original_historical_actual_full_3d_source_seminorm_polylog434
      L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
      buf hBufSmooth hBufSupport j 0 hLE hLN R hR hCubeR
    have hjReal : (j:ℝ) ≤ (J:ℝ) := by exact_mod_cast hj
    have hExp : (5*(K0+89))*((j:ℝ)+1) ≤ (5*(K0+89))*((J:ℝ)+1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤L) hExp
    have hm : 0≤K j := hK j
    calc
      _ ≤ R^0*K j*L^((5*(K0+89))*((j:ℝ)+1)) := hs
      _ = K j*L^((5*(K0+89))*((j:ℝ)+1)) := by ring
      _ ≤ K j*Rpow := mul_le_mul_of_nonneg_left hp hm
  have hPbound (j : ℕ) (hj : j≤J) :
      (SchwartzMap.seminorm ℂ P j) f ≤ R^P*K j*Rpow := by
    have hLE := parity_original_eta_e_threshold_mono434
      A hA.le J j hj L hLargeE
    have hLN := parity_original_eta_n_threshold_mono434
      A hA.le J j hj L hLargeN
    have hs := parity_original_historical_actual_full_3d_source_seminorm_polylog434
      L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
      buf hBufSmooth hBufSupport j P hLE hLN R hR hCubeR
    have hjReal : (j:ℝ) ≤ (J:ℝ) := by exact_mod_cast hj
    have hExp : (5*(K0+89))*((j:ℝ)+1) ≤ (5*(K0+89))*((J:ℝ)+1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤L) hExp
    calc
      _ ≤ R^P*K j*L^((5*(K0+89))*((j:ℝ)+1)) := hs
      _ ≤ R^P*K j*Rpow := by
        have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg hRpos (hK j))
        exact hh
  have hSum :
      (∑j∈Finset.range (N+1),
        ((SchwartzMap.seminorm ℂ 0 j) f +
         (SchwartzMap.seminorm ℂ P j) f)) ≤
      (1+R^P)*M*Rpow := by
    have hs :
      (∑j∈Finset.range (N+1),
        ((SchwartzMap.seminorm ℂ 0 j) f +
         (SchwartzMap.seminorm ℂ P j) f)) ≤
      ∑j∈Finset.range (N+1), (1+R^P)*K j*Rpow := by
      apply Finset.sum_le_sum
      intro j hj
      have hjJ : j≤J := Nat.le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hNJ
      have hh := add_le_add (h0 j hjJ) (hPbound j hjJ)
      convert hh using 1 <;> ring
    have hSubset : (Finset.range (N+1) : Finset ℕ)⊆Finset.range (J+1) :=
      Finset.range_mono (Nat.succ_le_succ hNJ)
    have hSub : (∑j∈Finset.range (N+1),K j)≤M :=
      Finset.sum_le_sum_of_subset_of_nonneg hSubset
        (fun j hj hnot=>hK j)
    calc
      _ ≤ ∑j∈Finset.range (N+1),(1+R^P)*K j*Rpow := hs
      _ = (1+R^P)*(∑j∈Finset.range (N+1),K j)*Rpow := by
        rw [Finset.mul_sum,Finset.sum_mul]
      _ ≤ (1+R^P)*M*Rpow := by
        have hcoef : 0≤1+R^P := by linarith
        have hm := mul_le_mul_of_nonneg_left hSub hcoef
        exact mul_le_mul_of_nonneg_right hm hRpow
  have hPow : (2:ℝ)^N≤(2:ℝ)^J := pow_le_pow_right₀ (by norm_num) hNJ
  have hFactor : 0≤C*((1+R^P)*M*Rpow) := by positivity
  change (2:ℝ)^N * C *
      (∑j∈Finset.range (N+1),
        ((SchwartzMap.seminorm ℂ 0 j) f+
         (SchwartzMap.seminorm ℂ P j) f)) ≤ D*Rpow
  calc
    _ ≤ (2:ℝ)^N*C*((1+R^P)*M*Rpow) :=
      mul_le_mul_of_nonneg_left hSum
        (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) _) hC)
    _ ≤ (2:ℝ)^J*C*((1+R^P)*M*Rpow) := by
      have h2 : (2:ℝ)^N*C ≤ (2:ℝ)^J*C :=
        mul_le_mul_of_nonneg_right hPow hC
      have hQ : 0≤(1+R^P)*M*Rpow := by positivity
      exact mul_le_mul_of_nonneg_right h2 hQ
    _ = D*Rpow := by dsimp [D]; ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFull3DFourierMomentPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- Fixed true source dimension-three Fourier H-moment constant.
Chosen from actual 3D Euclidean Lebesgue geometry, true historical
five source factors, the single fixed logarithmic buffer and radius.
No L,k,Z,χ, Fourier cutoff T or original signed epsilon appears. -/
def parityOriginalHistoricalActual3DFourierMomentFixedK434
    (A R : ℝ) (buf : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀ (s : ℝ), buf s ≠ 0 → -Real.log A ≤ s ∧ s ≤ Real.log A)
    (H : ℕ) : ℝ :=
  2 * parityOriginal3DSourceGeometricConstant434 *
    parityOriginalHistoricalFull3DSourceSeminormFixedK434
      A R buf hSmooth hSupp
      (H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)

/-- The formerly open **complete original Parity (4.15) 3D Fourier
moment polynomial bound**. The actual SOURCE h=-2 smoothed cutoff
is the same original nonlinear e(t)/E and n(t)/V from (4.14), with
real moving eta_e,L and fixed eta_n and three fixed buffers.

For every H, and sufficiently large L depending only on H and the
fixed buffer A (not k,Z,U,E,V,χ,epsilon), its full real Euclidean
three-dimensional Fourier H-moment satisfies

  M_H ≤ C_H * L^[5(K0+89)(H+P+1)],

where P is the fixed 3D Lebesgue integrablePower. The bound is
PROVED from actual all-order source derivatives and native
Schwartz/Fourier inequalities; not an assumption on the Fourier tail.
The true original nonzero integer k and source dyadic U,V,E,Z
hypotheses are explicit. -/
theorem parity_original_historical_actual_3d_fourier_moment_uniform_polylog434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (H : ℕ)
    (hLargeE : 2*A*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
       (2:ℝ)^(H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
       ((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    (∫ζ : EuclideanSpace ℝ (Fin 3),
      ‖ζ‖^H * ‖(𝓕 (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) :
        𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ‖) ≤
    parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hBufSmooth hBufSupport H *
      L^((5*(K0+89))*(((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  let P := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let J := H+P
  let B := parityOriginalHistoricalFull3DSourceSeminormFixedK434
    A R buf hBufSmooth hBufSupport J
  let C := parityOriginal3DSourceGeometricConstant434
  let Q := L^((5*(K0+89))*((J:ℝ)+1))
  have hm0 := parity_original_historical_full_3d_finite_seminorm_budget_polylog434
    L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
    buf hBufSmooth hBufSupport J 0 (Nat.zero_le J)
    hLargeE hLargeN R hR hCubeR
  have hmJ := parity_original_historical_full_3d_finite_seminorm_budget_polylog434
    L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
    buf hBufSmooth hBufSupport J J le_rfl
    hLargeE hLargeN R hR hCubeR
  have hC : 0≤C := parity_original_3d_source_geometric_constant_nonneg434
  have hB : 0≤B := by
    dsimp [B,parityOriginalHistoricalFull3DSourceSeminormFixedK434]
    have hg := parity_original_3d_source_geometric_constant_nonneg434
    have hr : 0≤R^((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower) := by positivity
    have hkSum : 0≤∑j∈Finset.range (J+1),
        parityOriginalHistoricalFull3DFixedDerivativeK434 A buf hBufSmooth hBufSupport j := by
      apply Finset.sum_nonneg
      intro j hj
      unfold parityOriginalHistoricalFull3DFixedDerivativeK434
      have hGe := parity_original_historical_five_factor_fixed_budget_ge_one434
        A buf hBufSmooth hBufSupport j
      exact mul_nonneg (parity_original_3d_five_factor_combinatorial_nonneg434 j)
        (pow_nonneg (by linarith : 0≤parityOriginalHistoricalFiveFactorFixedBudget434
           A buf hBufSmooth hBufSupport j) 5)
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg
      (by norm_num : (0:ℝ)≤2) _) hg)
      (by linarith : 0≤1+R^((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower))) hkSum
  have hQ : 0≤Q := Real.rpow_nonneg (by linarith : 0≤L) _
  have hMom := parity_original_real_3d_fourier_moment_le_original_source_finite434 H f
  change (∫ζ : EuclideanSpace ℝ (Fin 3), ‖ζ‖^H *
      ‖(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ‖) ≤ (2*C*B)*Q
  calc
    _ ≤ C*(parityOriginal3DSourceFiniteSeminormBudget434 0 f+
      parityOriginal3DSourceFiniteSeminormBudget434 J f) := hMom
    _ ≤ C*((B*Q)+(B*Q)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hm0 hmJ) hC
    _ = (2*C*B)*Q := by ring

/-- Exact physical original Parity (4.15) high-frequency Fourier L1
TAIL bound of arbitrary polynomial order, with the formerly UNKNOWN
source B_H uniformly paid in a fixed polynomial in L. For all T>0:

 tail(‖ζ‖>T) ≤ C_H L^[5(K0+89)(H+P+1)]/T^H.

All original source eta_e, eta_n, 3D log pullbacks, k≠0 and
h=-2 correction, true SOURCE dyadic geometry and fixed buffer
are retained. No 4.17 core cancellation or full TypeII assumed. -/
theorem parity_original_historical_actual_3d_fourier_tail_uniform_polylog434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (H : ℕ)
    (hLargeE : 2*A*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
       (2:ℝ)^(H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
       ((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (T : ℝ) (hT : 0<T) :
    (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _)ᶜ,
      ‖(𝓕 (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) :
        𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ‖) ≤
    parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hBufSmooth hBufSupport H *
      L^((5*(K0+89))*(((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) / T^H := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  have ht := parity_original_historical_3d_fourier_tail_le_moment434
    H U E V Z k buf (parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL)
    parityOriginalHistoricalActualEtaN434 (-Real.log A) (Real.log A)
    hBufSmooth (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL)
    parity_original_historical_actual_eta_n_smooth434 hBufSupport T hT
  have hm := parity_original_historical_actual_3d_fourier_moment_uniform_polylog434
    L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
    buf hBufSmooth hBufSupport H hLargeE hLargeN R hR hCubeR
  exact ht.trans (div_le_div_of_nonneg_right hm (pow_nonneg hT.le H))
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFourierTailAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Elementary exact physical Fourier polynomial scale identity:
for any desired logarithmic precision D, choosing a sufficiently
large but FIXED log-frequency exponent X+D converts a polynomial
X moment with one inverse frequency factor to L^-D. -/
theorem parity_original_real_polylog_ratio_to_tail434
    (L X D : ℝ) (hL : 0<L) :
    L^X / L^(X+D)=L^(-D) := by
  rw [Real.rpow_add hL,Real.rpow_neg hL.le]
  have hp : 0<L^X := Real.rpow_pos_of_pos hL _
  have hd : 0<L^D := Real.rpow_pos_of_pos hL _
  field_simp [hp.ne',hd.ne']

/-- Complete ACTUAL original source Parity (4.15) real 3D Fourier
high-frequency TAIL to ANY prescribed inverse-logarithmic order.
For an arbitrary fixed D≥0 choose the polynomial cutoff

  T=L^(5*(K0+89)*(P+2)+D)

with P the fixed 3D Lebesgue integrablePower. Then

  integral_{||xi||>T} |Fourier(original η_e,L η_n 3D cutoff)|
       ≤ C_1 * L^(-D).

This has NO unproved source smoothness constants, no guessed Fourier
moment, and the same true original sign h=-2 correction and 3D log
box; the cutoff exponent is chosen prior to original k,Z and χ.

Parity(4.17) core identification and summation of outer source cells
remain OPEN. -/
theorem parity_original_historical_actual_3d_fourier_tail_any_log434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (hLargeE : 2*A*((1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
       (2:ℝ)^(1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
       ((1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (D : ℝ) (hD : 0≤D) :
    let X := (5*(K0+89))*(((1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)
    let T := L^(X+D)
    (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _)ᶜ,
      ‖(𝓕 (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) :
        𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ‖) ≤
    parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hBufSmooth hBufSupport 1 * L^(-D) := by
  dsimp only
  let X : ℝ := (5*(K0+89))*(((1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)
  let T := L^(X+D)
  have hLp : 0<L := by linarith
  have hT : 0<T := Real.rpow_pos_of_pos hLp _
  have hTail := parity_original_historical_actual_3d_fourier_tail_uniform_polylog434
    L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
    buf hBufSmooth hBufSupport 1 hLargeE hLargeN R hR hCubeR T hT
  have hRatio := parity_original_real_polylog_ratio_to_tail434 L X D hLp
  have hUpper :
    parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hBufSmooth hBufSupport 1 *
      L^X / T ≤
    parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hBufSmooth hBufSupport 1 *
      L^(-D) := by
    have heq : L^X/T=L^(-D) := hRatio
    apply le_of_eq
    calc
      _ = parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf
          hBufSmooth hBufSupport 1*(L^X/T) := by ring
      _ = parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf
          hBufSmooth hBufSupport 1*L^(-D) := by rw [heq]
  have hTail' :
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _)ᶜ,
        ‖(𝓕 (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf (-Real.log A) (Real.log A)
          hBufSmooth hBufSupport) :
          𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ‖) ≤
      parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hBufSmooth hBufSupport 1 * L^X/T := by
    simpa only [X,pow_one] using hTail
  exact hTail'.trans hUpper
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFull3DBudgetPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The ACTUAL original Parity (4.14) exact PRE-FOURIER finite
source Schwartz derivative budget B_H itself — not just the
Fourier moment which it bounds — has a fixed-source uniform
L-polynomial bound. This is the exact contract needed to replace
B_H in the original finite cofactor signed (4.16) tail theorem.

 B_H(f_{L,k,Z}) ≤ C_H L^[5(K0+89)(H+P+1)]

where C_H is a fixed source buffer/geometry constant independent
of all physical k,Z,e,m,n,χ, signed branch and target precision.
The source h=-2 g_n correction, all five ORIGINAL 3D cutoff
factors and compact logarithmic buffers were already kernel proved. -/
theorem parity_original_historical_actual_source_BH_uniform_polylog434
    (L U E V Z K0 A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (H : ℕ)
    (hLargeE : 2*A*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
       (2:ℝ)^(H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
       ((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    parityOriginal3DSourceMomentFiniteBudget434 H
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) ≤
    parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hBufSmooth hBufSupport H *
      L^((5*(K0+89))*(((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  let P := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let J := H+P
  let B := parityOriginalHistoricalFull3DSourceSeminormFixedK434
    A R buf hBufSmooth hBufSupport J
  let C := parityOriginal3DSourceGeometricConstant434
  let Q := L^((5*(K0+89))*((J:ℝ)+1))
  have hm0 := parity_original_historical_full_3d_finite_seminorm_budget_polylog434
    L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
    buf hBufSmooth hBufSupport J 0 (Nat.zero_le J)
    hLargeE hLargeN R hR hCubeR
  have hmJ := parity_original_historical_full_3d_finite_seminorm_budget_polylog434
    L U E V Z K0 A hL hK0 k hk hU hV hUV hE hZ hZupper hA
    buf hBufSmooth hBufSupport J J le_rfl
    hLargeE hLargeN R hR hCubeR
  have hC : 0≤C := parity_original_3d_source_geometric_constant_nonneg434
  change C*(parityOriginal3DSourceFiniteSeminormBudget434 0 f+
      parityOriginal3DSourceFiniteSeminormBudget434 J f) ≤ (2*C*B)*Q
  calc
    _ ≤ C*((B*Q)+(B*Q)) :=
      mul_le_mul_of_nonneg_left (add_le_add hm0 hmJ) hC
    _ = (2*C*B)*Q := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalFiniteFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- The TRUE logarithmic physical point for one original h=-2
source event (m',n) on its canonical source Z-fibre, at fixed
selected e,m and common genuine source dyadic U,Z. -/
def parityOriginalHistoricalPhysicalFourierEventTriple434
    {ι : Type*} (U Z : ℝ) (e m : ℕ)
    (mp n : ι → ℕ) (i : ι) : EuclideanSpace ℝ (Fin 3) :=
  parityOriginalHistoricalRealLogTriple434 U Z m (mp i)
    (parityOriginalHistoricalCanonicalZ434 e m (mp i) (n i))

/-- Pointwise TRUE original source η_e(e/E)*η_n(n/V) equals the
ACTUAL 3D Schwartz kernel for every valid source event in ONE
common historical nonzero k and dyadic Z. The ORIGINAL b=-2
and Q/P gates stay inside parityOriginalHistoricalPhysicalValidN434.
All three fixed dyadic auxiliary logarithmic buffers equal 1 on
the actual ORIGINAL m,m',z dyads. This has no unknown Fourier
coefficient and uses only SOURCE-proven k, canonical z identities. -/
theorem parity_original_historical_dyadic_eta_physical_point_3d434
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (U E V Z : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (k : ℤ) (hk : parityOriginalHistoricalOffdiagK434 e m mp=k)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)≤2*U)
    (hzLo : Z≤(parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ))
    (hzHi : (parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ)≤2*Z)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ x : ℝ, buf x≠0 → a≤x ∧ x≤b)
    (hBufOne : ∀x∈Set.Icc (0:ℝ) (Real.log 2), buf x=1) :
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ)=
    parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hBufSmooth hBufSupport
      (parityOriginalHistoricalRealLogTriple434 U Z m mp
        (parityOriginalHistoricalCanonicalZ434 e m mp n)) := by
  let etaE := parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL
  let etaN := parityOriginalHistoricalActualEtaN434
  have hSource := parity_original_historical_source_eta_equals_euclidean_3d434
    d L band slot δ Y e m mp n he hneq hValid
    U E V Z hU hE hV hZ buf etaE etaN a b
    hBufSmooth
    (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL)
    parity_original_historical_actual_eta_n_smooth434 hBufSupport
  rw [hk] at hSource
  have hBox := parity_original_historical_log_three_coordinate_box434
    U Z m mp (parityOriginalHistoricalCanonicalZ434 e m mp n)
    hU hZ hmLo hmHi hmpLo hmpHi hzLo hzHi
  have hb0 := hBufOne (Real.log ((m:ℝ)/U)) ⟨hBox.1,hBox.2.1⟩
  have hb1 := hBufOne (Real.log ((mp:ℝ)/U))
    ⟨hBox.2.2.1,hBox.2.2.2.1⟩
  have hb2 := hBufOne (Real.log ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℕ)/Z))
    ⟨hBox.2.2.2.2.1,hBox.2.2.2.2.2⟩
  rw [hb0,hb1,hb2] at hSource
  have hWeight := parity_original_historical_dyadic_eta_weight_is_complex_product434
    L E V hL e n
  simp only [one_mul] at hSource
  exact hWeight.trans hSource.symm

/-- EXACT FULL REAL original source finite physical Fourier identity
on one fixed selected e,m,k,Z and dyadic U,E,V. Every actual
physical (m',n) event is source-valid; each canonical z=m'v is in
its true Z-dyad, and every m' belongs to the SAME canonical k-fibre.
The arbitrary complex W includes true original signed H0, reserved
Q/P, fine b629 alpha, parity and characters; no independence of W
or spectral saving is assumed. The Fourier transform is ONE COMMON
source-constructed η_e,L*η_n Schwartz kernel for all physical events.
This is the precise finite SOURCE pre-(4.16) Fourier factorization. -/
theorem parity_original_historical_source_physical_finite_3d_fourier434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ) (mp n : ι → ℕ)
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (he : Odd e)
    (U E V Z : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (k : ℤ) (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hPhysical : ∀ i∈S, m≠mp i ∧
      parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m (mp i) (n i) ∧
      parityOriginalHistoricalOffdiagK434 e m (mp i)=k ∧
      U≤(mp i:ℝ) ∧ (mp i:ℝ)≤2*U ∧
      Z≤(parityOriginalHistoricalCanonicalZ434 e m (mp i) (n i):ℝ) ∧
      (parityOriginalHistoricalCanonicalZ434 e m (mp i) (n i):ℝ)≤2*Z)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ x : ℝ, buf x≠0 → a≤x ∧ x≤b)
    (hBufOne : ∀x∈Set.Icc (0:ℝ) (Real.log 2), buf x=1) :
    (∑i∈S,W i*((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e (n i):ℝ):ℂ)) =
    ∫ξ : EuclideanSpace ℝ (Fin 3),
      parityOriginal3DPhysicalFiniteTwistedSource434 S W
        (parityOriginalHistoricalPhysicalFourierEventTriple434 U Z e m mp n)
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport) ξ := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hBufSmooth hBufSupport
  let t : ι → EuclideanSpace ℝ (Fin 3) :=
    parityOriginalHistoricalPhysicalFourierEventTriple434 U Z e m mp n
  have hTerm (i : ι) (hi : i∈S) :
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e (n i):ℝ):ℂ)=f (t i) := by
    obtain ⟨hNe,hValid,hK,hMpLo,hMpHi,hZLo,hZHi⟩ := hPhysical i hi
    exact parity_original_historical_dyadic_eta_physical_point_3d434
      d L hL band slot δ Y e m (mp i) (n i) he hNe hValid
      U E V Z hU hE hV hZ k hK hmLo hmHi hMpLo hMpHi hZLo hZHi
      buf a b hBufSmooth hBufSupport hBufOne
  calc
    _ = parityOriginal3DPhysicalFiniteSignal434 S W t f := by
      unfold parityOriginal3DPhysicalFiniteSignal434
      apply Finset.sum_congr rfl
      intro i hi
      rw [hTerm i hi]
    _ = _ := parity_original_3d_physical_finite_source_fourier_fubini434 S W t f
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalFiniteFourierTrunc -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Full source physical fixed-e/m/k/Z finite family with ORIGINAL
h=-2 Q/P-valid cofactor m', canonical z and n, and the same
quantitatively constructed eta_e,L*eta_n cutoff for ALL physical
entries: the low-frequency 3D Fourier integral recovers its
COMPLEX signed weighted cofactor sum with exact ℓ1 tail cost.

This does not assume any cancellation of the true original W_i,
bounded Fourier moments, a particular number of characters, or
full Parity (4.17). Unlike a pointwise kernel fact, this controls the
whole source finite sum after swapping signed character weights
through ONE common Fourier integral. -/
theorem parity_original_historical_physical_finite_3d_truncation434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ) (mp n : ι → ℕ)
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (he : Odd e)
    (U E V Z : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (k : ℤ) (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hPhysical : ∀ i∈S, m≠mp i ∧
      parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m (mp i) (n i) ∧
      parityOriginalHistoricalOffdiagK434 e m (mp i)=k ∧
      U≤(mp i:ℝ) ∧ (mp i:ℝ)≤2*U ∧
      Z≤(parityOriginalHistoricalCanonicalZ434 e m (mp i) (n i):ℝ) ∧
      (parityOriginalHistoricalCanonicalZ434 e m (mp i) (n i):ℝ)≤2*Z)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ x : ℝ, buf x≠0 → a≤x ∧ x≤b)
    (hBufOne : ∀x∈Set.Icc (0:ℝ) (Real.log 2), buf x=1)
    (H : ℕ) (T : ℝ) (hT : 0<T) :
    ‖(∑i∈S,W i*
        ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e (n i):ℝ):ℂ)) -
      (∫ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 S W
          (parityOriginalHistoricalPhysicalFourierEventTriple434 U Z e m mp n)
          (parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hL U E V Z k buf a b hBufSmooth hBufSupport) ξ)‖ ≤
    parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
      (parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport) / T^H) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hBufSmooth hBufSupport
  let t := parityOriginalHistoricalPhysicalFourierEventTriple434 U Z e m mp n
  have hPhysicalFourier := parity_original_historical_source_physical_finite_3d_fourier434
    S W mp n d L hL band slot δ Y e m he
    U E V Z hU hE hV hZ k hmLo hmHi hPhysical
    buf a b hBufSmooth hBufSupport hBufOne
  have hGenericFourier :=
    parity_original_3d_physical_finite_source_fourier_fubini434 S W t f
  have hSame : (∑i∈S,W i*
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e (n i):ℝ):ℂ)) =
      parityOriginal3DPhysicalFiniteSignal434 S W t f :=
    hPhysicalFourier.trans hGenericFourier.symm
  rw [hSame]
  exact parity_original_historical_actual_dyadic_finite_3d_truncation434
    S W t H L hL U E V Z k buf a b hBufSmooth hBufSupport T hT
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualKZFourierCarrier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- The ACTUAL original historical signed Parity (4.13)-(4.15)
finite k,Z physical carrier at fixed selected e,m:
- cofactor m' lies in the GENUINE source canonical quotient fibre
  k=(m'-m)/e with original m'≠m,
- original n lies in the TRUE J dyad and both Q/P/H_0 endpoint
  physical e,vStar gates are nonempty,
- physical canonical z=m'v is POSITIVE and its genuine binary dyadic
  scale is Z, not an independently manufactured z parameter.
No proxy, Ppart extension or original event is added. -/
def parityOriginalHistoricalActualKZPhysicalEventCarrier434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ) :
    Finset (ℕ × ℕ) :=
  ((parityOriginalHistoricalKPrimeFibre434 e m K k).product J).filter
    (fun q =>
      parityOriginalHistoricalPhysicalValidN434
        d L band slot δ Y e m q.1 q.2 ∧
      0 < parityOriginalHistoricalCanonicalZ434 e m q.1 q.2 ∧
      parityOriginalHistoricalActualZDyadicScale434
        (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) = Z)

/-- Every element of the REAL canonical source k/Z carrier satisfies
all hypotheses of the genuine original 3D Fourier physical event:
common k and Z, original m'∈K.erase m, populated Q/P n gates and
positive z∈[Z,2Z]. No unsupported formal n or a distinct synthetic
z is admitted. The cofactor m' dyad is an external original K input. -/
theorem parity_original_historical_actual_k_z_event_physical434
    (d : ℕ) (L U : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (hDyad : ∀mp∈K, U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z) :
    m≠q.1 ∧
    parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m q.1 q.2 ∧
    parityOriginalHistoricalOffdiagK434 e m q.1=k ∧
    U≤(q.1:ℝ) ∧ (q.1:ℝ)≤2*U ∧
    (Z:ℝ)≤(parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ) ∧
    (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)≤2*(Z:ℝ) := by
  have hMem := Finset.mem_filter.mp hq
  have hPr := Finset.mem_product.mp hMem.1
  have hMP := Finset.mem_filter.mp hPr.1
  have hNe := (Finset.mem_erase.mp hMP.1).1.symm
  have hMPK := (Finset.mem_erase.mp hMP.1).2
  have hR := hDyad q.1 hMPK
  obtain ⟨hValid,hZpos,hZscale⟩ := hMem.2
  have hD := parity_original_historical_actual_z_in_own_dyad434
    (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) hZpos
  rw [hZscale] at hD
  refine ⟨hNe,hValid,hMP.2,hR.1,hR.2,?_,?_⟩
  · exact_mod_cast hD.2.1
  · have hh : (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ) <
      2*(Z:ℝ) := by exact_mod_cast hD.2.2
    exact hh.le

/-- Real original full h=-2 Parity source cofactor coefficient with
true physical H0 two-endpoint signed epsilon, full original b629
fine alpha and Dirichlet character modulo 2|k|. The source eta_e/n
weight is intentionally NOT part of W: it is the actual common
3D Schwartz Fourier multiplier on the k/Z physical fibre. -/
def parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs))
    (q : ℕ×ℕ) : ℂ :=
  χ (q.1 : ZMod (2*k.natAbs)) *
    parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e q.2 m q.1

/-- EXACT physical SOURCE signed character k/Z Cauchy sub-fibre
with original n-dependent smoothing weight. No ℓ1 bound or Fourier
saving is applied in this definition. -/
def parityOriginalHistoricalActualKZPhysicalWeightedSource434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) : ℂ :=
  ∑q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,
    parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
      d L band slot δ ξ rho α signed Y e m k χ q *
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2:ℝ):ℂ)

/-- **SOURCE ORIGINAL (4.13)-(4.15) FINITE 3D FOURIER JOIN**.
The literal original Q/P supported k/Z fibre of m' and n, with
canonical z and original signed H0/b629 fine alpha/χ pair, equals
one genuine Euclidean 3D Fourier integral for the quantitatively
constructed original η_e(e/E)η_n(n/V) smoothed Cauchy weight.
No synthetic or additional physical term or Fourier multiplier is
assumed. This closes the exact SOURCE finite k/Z Fourier algebra
before the still-open 4.17 endpoint identification. -/
theorem parity_original_historical_actual_k_z_physical_fourier434
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (U E V : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hDyad : ∀mp∈K, U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x : ℝ, buf x≠0 → a≤x ∧ x≤b)
    (hBufOne : ∀x∈Set.Icc (0:ℝ) (Real.log 2), buf x=1)
    (hZ : 0<Z) :
    parityOriginalHistoricalActualKZPhysicalWeightedSource434
      d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ =
    ∫ζ : EuclideanSpace ℝ (Fin 3),
      parityOriginal3DPhysicalFiniteTwistedSource434
        (parityOriginalHistoricalActualKZPhysicalEventCarrier434
          d L band slot δ Y e m K J k Z)
        (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
          d L band slot δ ξ rho α signed Y e m k χ)
        (parityOriginalHistoricalPhysicalFourierEventTriple434
          (U:ℝ) (Z:ℝ) e m (fun q : ℕ×ℕ=>q.1) (fun q : ℕ×ℕ=>q.2))
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport) ζ := by
  let S := parityOriginalHistoricalActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z
  let W := parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
    d L band slot δ ξ rho α signed Y e m k χ
  let mp : (ℕ×ℕ)→ℕ := fun q=>q.1
  let n : (ℕ×ℕ)→ℕ := fun q=>q.2
  have hPhysical : ∀q∈S,
      m≠mp q ∧ parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m (mp q) (n q) ∧
      parityOriginalHistoricalOffdiagK434 e m (mp q)=k ∧
      U≤(mp q:ℝ) ∧ (mp q:ℝ)≤2*U ∧
      (Z:ℝ)≤(parityOriginalHistoricalCanonicalZ434 e m (mp q) (n q):ℝ) ∧
      (parityOriginalHistoricalCanonicalZ434 e m (mp q) (n q):ℝ)≤2*(Z:ℝ) := by
    intro q hq
    exact parity_original_historical_actual_k_z_event_physical434
      d L U band slot δ Y e m K J k Z hDyad q hq
  have h := parity_original_historical_source_physical_finite_3d_fourier434
    S W mp n d L hL band slot δ Y e m he
    U E V (Z:ℝ) hU hE hV (by exact_mod_cast hZ)
    k hmLo hmHi hPhysical buf a b hBufSmooth hBufSupport hBufOne
  exact h
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualKZFourierTrunc -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- **ACTUAL SOURCE signed Parity (4.13)-(4.15) k/Z Fourier truncation**
with the physical cofactor pair (m',n) range built from its true
original quotient k-fibre and dyadic canonical z, original Q/P/H0
source support, and literal signed chi(m')*b629 alpha/cofactor pair.

The single Euclidean 3D Fourier integral on ||ζ||<=T differs from
the ORIGINAL smoothed physical signed source by at most the EXACT
complex cofactor l1 mass times the FINITE pre-Fourier source
derivative seminorm budget B_H/T^H. No polynomial bound on this
mass or B_H, no full Type II and no Parity (4.17) is assumed. -/
theorem parity_original_historical_actual_k_z_physical_fourier_trunc434
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (U E V : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hDyad : ∀mp∈K, U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x : ℝ, buf x≠0 → a≤x ∧ x≤b)
    (hBufOne : ∀x∈Set.Icc (0:ℝ) (Real.log 2), buf x=1)
    (hZ : 0<Z) (H : ℕ) (T : ℝ) (hT : 0<T) :
    ‖parityOriginalHistoricalActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ -
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434
          (parityOriginalHistoricalActualKZPhysicalEventCarrier434
            d L band slot δ Y e m K J k Z)
          (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
            d L band slot δ ξ rho α signed Y e m k χ)
          (parityOriginalHistoricalPhysicalFourierEventTriple434
            (U:ℝ) (Z:ℝ) e m (fun q : ℕ×ℕ=>q.1) (fun q : ℕ×ℕ=>q.2))
          (parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport) ζ)‖ ≤
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ) *
      (parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport)/T^H) := by
  let S := parityOriginalHistoricalActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z
  let W := parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
    d L band slot δ ξ rho α signed Y e m k χ
  let mp : (ℕ×ℕ)→ℕ := fun q=>q.1
  let n : (ℕ×ℕ)→ℕ := fun q=>q.2
  have hPhysical : ∀q∈S,
      m≠mp q ∧ parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m (mp q) (n q) ∧
      parityOriginalHistoricalOffdiagK434 e m (mp q)=k ∧
      U≤(mp q:ℝ) ∧ (mp q:ℝ)≤2*U ∧
      (Z:ℝ)≤(parityOriginalHistoricalCanonicalZ434 e m (mp q) (n q):ℝ) ∧
      (parityOriginalHistoricalCanonicalZ434 e m (mp q) (n q):ℝ)≤2*(Z:ℝ) := by
    intro q hq
    exact parity_original_historical_actual_k_z_event_physical434
      d L U band slot δ Y e m K J k Z hDyad q hq
  exact parity_original_historical_physical_finite_3d_truncation434
    S W mp n d L hL band slot δ Y e m he
    U E V (Z:ℝ) hU hE hV (by exact_mod_cast hZ)
    k hmLo hmHi hPhysical buf a b hBufSmooth hBufSupport hBufOne
    H T hT
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualKZEventReindex -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- On the actual ORIGINAL Q/P gated h=-2 positive source, selecting
one real binary Z through canonical n→z is EXACTLY the same finite
set as selecting a true supported z in original physical z-support
and then the unique (or explicit) supported canonical n-fibre.
No source m',n term is invented, discarded, multiplied or replaced
by a positive surrogate. This identity is essential to match
SOURCE-weighted character/dyadic outer correlation to one physical
Fourier kernel. -/
theorem parity_original_historical_canonical_k_z_n_event_reindex434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp : ℕ) (J : Finset ℕ) (Z : ℕ)
    (he : Odd e) (hneq : m≠mp) (W : ℕ → ℂ) :
    (∑n∈J.filter (fun n=>
       parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp n ∧
       0<parityOriginalHistoricalCanonicalZ434 e m mp n ∧
       parityOriginalHistoricalActualZDyadicScale434
         (parityOriginalHistoricalCanonicalZ434 e m mp n)=Z), W n) =
    ∑z∈parityOriginalHistoricalActualPhysicalZDyadicFibre434
        d L band slot δ Y e m mp J Z,
      ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
        (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),W n := by
  classical
  let g : ℕ → ℕ := parityOriginalHistoricalCanonicalZ434 e m mp
  let V : ℕ → Prop := parityOriginalHistoricalPhysicalValidN434
    d L band slot δ Y e m mp
  let A : Finset ℕ := J.filter
    (fun n => V n ∧ 0<g n ∧ parityOriginalHistoricalActualZDyadicScale434 (g n)=Z)
  let P : Finset ℕ := parityOriginalHistoricalPhysicalValidZSupport434
    d L band slot δ Y e m mp J
  let PF : Finset ℕ := parityOriginalHistoricalActualPhysicalZDyadicFibre434
    d L band slot δ Y e m mp J Z
  have hImage : A.image g = PF := by
    ext z
    constructor
    · intro hz
      obtain ⟨n,hnA,hgn⟩ := Finset.mem_image.mp hz
      have hnJ := (Finset.mem_filter.mp hnA).1
      obtain ⟨hnV,hnPos,hnScale⟩ := (Finset.mem_filter.mp hnA).2
      have hz0 : z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J := by
        exact Finset.mem_image.mpr ⟨n,hnJ,hgn⟩
      have hnF : n∈parityOriginalHistoricalCanonicalZNFibre434 e m mp J z :=
        Finset.mem_filter.mpr ⟨hnJ,hgn⟩
      have hzPhysical : z∈P := by
        unfold P parityOriginalHistoricalPhysicalValidZSupport434
        exact Finset.mem_filter.mpr ⟨hz0,⟨n,Finset.mem_filter.mpr ⟨hnF,hnV⟩⟩⟩
      unfold PF parityOriginalHistoricalActualPhysicalZDyadicFibre434
      exact Finset.mem_filter.mpr ⟨hzPhysical,by simpa [hgn] using hnScale⟩
    · intro hz
      have hzData := Finset.mem_filter.mp hz
      have hzP : z∈P := hzData.1
      have hzScale : parityOriginalHistoricalActualZDyadicScale434 z=Z := hzData.2
      have hzPhys : z∈parityOriginalHistoricalPhysicalValidZSupport434
          d L band slot δ Y e m mp J := hzP
      have hzPos := (parity_original_historical_physical_supported_z_and_shift_pos434
          d L band slot δ Y e m mp J z he hneq hzPhys).2.1
      have hzNonempty := (Finset.mem_filter.mp hzPhys).2
      obtain ⟨n,hnF⟩ := hzNonempty
      have hnV := (Finset.mem_filter.mp hnF).2
      have hnN := (Finset.mem_filter.mp hnF).1
      have hnJ := (Finset.mem_filter.mp hnN).1
      have hgn := (Finset.mem_filter.mp hnN).2
      have hposn : 0<g n := by
        change 0<parityOriginalHistoricalCanonicalZ434 e m mp n
        rw [hgn]
        exact hzPos
      have hscalen : parityOriginalHistoricalActualZDyadicScale434 (g n)=Z := by
        change parityOriginalHistoricalActualZDyadicScale434
          (parityOriginalHistoricalCanonicalZ434 e m mp n)=Z
        rw [hgn]
        exact hzScale
      have hnA : n∈A := Finset.mem_filter.mpr
        ⟨hnJ,hnV,hposn,hscalen⟩
      exact Finset.mem_image.mpr ⟨n,hnA,hgn⟩
  have hFibre (z : ℕ) (hz : z∈A.image g) :
      A.filter (fun n=>g n=z) =
      (parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter V := by
    have hzData := Finset.mem_filter.mp (hImage ▸ hz)
    have hzP := hzData.1
    have hzScale := hzData.2
    have hzPos := (parity_original_historical_physical_supported_z_and_shift_pos434
        d L band slot δ Y e m mp J z he hneq hzP).2.1
    ext n
    constructor
    · intro hn
      have hnA := (Finset.mem_filter.mp hn).1
      have hgn := (Finset.mem_filter.mp hn).2
      have hnJ := (Finset.mem_filter.mp hnA).1
      have hnV := (Finset.mem_filter.mp hnA).2.1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hnJ,hgn⟩,hnV⟩
    · intro hn
      have hnF := (Finset.mem_filter.mp hn).1
      have hnV := (Finset.mem_filter.mp hn).2
      have hnJ := (Finset.mem_filter.mp hnF).1
      have hgn := (Finset.mem_filter.mp hnF).2
      have hposn : 0<g n := by
        change 0<parityOriginalHistoricalCanonicalZ434 e m mp n
        rw [hgn]
        exact hzPos
      have hscalen : parityOriginalHistoricalActualZDyadicScale434 (g n)=Z := by
        change parityOriginalHistoricalActualZDyadicScale434
          (parityOriginalHistoricalCanonicalZ434 e m mp n)=Z
        rw [hgn]
        exact hzScale
      have hnA : n∈A := Finset.mem_filter.mpr
        ⟨hnJ,hnV,hposn,hscalen⟩
      exact Finset.mem_filter.mpr ⟨hnA,hgn⟩
  have hReindex := Finset.sum_image' (s:=A) (g:=g)
    (f:=fun z => ∑ n∈A.filter (fun n=>g n=z),W n)
    W (by intro n hn;rfl)
  change (∑n∈A,W n)=∑z∈PF,
    ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter V,W n
  calc
    _ = ∑z∈A.image g,∑n∈A.filter (fun n=>g n=z),W n := hReindex.symm
    _ = ∑z∈PF,∑n∈A.filter (fun n=>g n=z),W n := by rw [hImage]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      exact Finset.sum_congr (hFibre z (by simpa only [hImage] using hz))
        (by intro _ _;rfl)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualKZEventDyadicJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- GENUINE ORIGINAL Parity source k/Z family in two equivalent
fully physical forms: (a) the directly supported (m',n) event
carrier used by a SINGLE Schwartz Fourier kernel, (b) the original
nested m'→z→n canonical source dyadic fibre used by the signed
character-outer Cauchy offdiagonal. For odd source e and m'≠m,
all physical canonical z>0, and source k and Z are EXACTLY the same.
This is an exact complex equality for ANY original physical source
coefficient: no positivity or guessed injectivity or Fourier-tail
bound is needed. -/
theorem parity_original_historical_actual_k_z_event_eq_source_dyadic434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (W : ℕ → ℕ → ℂ) :
    (∑q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
       d L band slot δ Y e m K J k Z,W q.1 q.2) =
      ∑mp∈parityOriginalHistoricalActualPhysicalDyadicMFibre434
        d L band slot δ Y e m K J k Z,
        ∑z∈parityOriginalHistoricalActualPhysicalZDyadicFibre434
          d L band slot δ Y e m mp J Z,
          ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
            (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
            W mp n := by
  let M := parityOriginalHistoricalKPrimeFibre434 e m K k
  let PZ : ℕ → Finset ℕ := fun mp =>
    parityOriginalHistoricalPhysicalValidZSupport434 d L band slot δ Y e m mp J
  let S : ℕ → Finset ℕ := fun mp =>
    parityOriginalHistoricalActualPhysicalZDyadicFibre434
      d L band slot δ Y e m mp J Z
  let P : ℕ → ℕ → Prop := fun mp n =>
    parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp n ∧
    0 < parityOriginalHistoricalCanonicalZ434 e m mp n ∧
    parityOriginalHistoricalActualZDyadicScale434
      (parityOriginalHistoricalCanonicalZ434 e m mp n)=Z
  have hOne (mp : ℕ) (hmp : mp∈M) :
      (∑n∈J.filter (P mp),W mp n) =
      ∑z∈S mp,
        ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
          (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
          W mp n := by
    have hne : m≠mp := (Finset.mem_erase.mp (Finset.mem_filter.mp hmp).1).1.symm
    exact parity_original_historical_canonical_k_z_n_event_reindex434
      d L band slot δ Y e m mp J Z he hne (W mp)
  have hFirst :
      (∑q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
       d L band slot δ Y e m K J k Z,W q.1 q.2) =
      ∑mp∈M,∑n∈J.filter (P mp),W mp n := by
    unfold parityOriginalHistoricalActualKZPhysicalEventCarrier434
    change (∑q∈(M.product J).filter (fun q => P q.1 q.2),W q.1 q.2) = _
    rw [Finset.sum_filter]
    change (∑q∈M×ˢJ,if P q.1 q.2 then W q.1 q.2 else 0) = _
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro mp hmp
    rw [Finset.sum_filter]
  have hSkip (mp : ℕ) (hmp : mp∈M)
      (hZ : Z∉(PZ mp).image parityOriginalHistoricalActualZDyadicScale434) :
      S mp = ∅ := by
    by_contra hNE
    have hHas : (S mp).Nonempty := by
      by_contra hEmpty
      exact hNE (Finset.not_nonempty_iff_eq_empty.mp hEmpty)
    obtain ⟨z,hz⟩ := hHas
    have hZMem := Finset.mem_filter.mp hz
    exact hZ (Finset.mem_image.mpr ⟨z,hZMem.1,hZMem.2⟩)
  calc
    _ = ∑mp∈M,∑n∈J.filter (P mp),W mp n := hFirst
    _ = ∑mp∈M,∑z∈S mp,
        ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
          (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
          W mp n := by
      apply Finset.sum_congr rfl
      intro mp hmp
      exact hOne mp hmp
    _ = ∑mp∈M.filter (fun mp=> Z∈(PZ mp).image
        parityOriginalHistoricalActualZDyadicScale434),
        ∑z∈S mp,
          ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
            (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
            W mp n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro mp hmp
      by_cases hZ : Z∈(PZ mp).image parityOriginalHistoricalActualZDyadicScale434
      · simp only [if_pos hZ]
      · have hEmpty := hSkip mp hmp hZ
        simp only [if_neg hZ,hEmpty,Finset.sum_empty]
    _ = _ := rfl

/-- The exact original historical signed χ character cofactor k/Z
SOURCE FIBRE is the same REAL physical event source sum used by the
3D Fourier truncation, including intrinsic H0, original signed
conjugate alpha and the correct n-dependent η_e(e/E)η_n(n/V).
This closes a real missing algebraic source k/Z integration bridge;
no 4.17 correlation bound has yet been applied. -/
theorem parity_original_historical_actual_k_z_weighted_character_eq_original_fibre434
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (E V : ℝ) :
    parityOriginalHistoricalActualKZPhysicalWeightedSource434
      d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ =
    ∑mp∈parityOriginalHistoricalActualPhysicalDyadicMFibre434
        d L band slot δ Y e m K J k Z,
      χ (mp : ZMod (2*k.natAbs)) *
        (∑z∈parityOriginalHistoricalActualPhysicalZDyadicFibre434
          d L band slot δ Y e m mp J Z,
          ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
            (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
            ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) *
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp) := by
  let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hL
  let U : ℕ → ℕ → ℂ := fun mp n =>
    χ (mp : ZMod (2*k.natAbs)) *
      (((w e n:ℝ):ℂ)*parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp)
  have hReindex := parity_original_historical_actual_k_z_event_eq_source_dyadic434
    d L band slot δ Y e m K J k Z he U
  unfold parityOriginalHistoricalActualKZPhysicalWeightedSource434
  calc
    _ = ∑q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
          d L band slot δ Y e m K J k Z,U q.1 q.2 := by
      apply Finset.sum_congr rfl
      intro q hq
      dsimp [U,w,parityOriginalHistoricalActualKZPhysicalSignedCoefficient434]
      ring
    _ = ∑mp∈parityOriginalHistoricalActualPhysicalDyadicMFibre434
          d L band slot δ Y e m K J k Z,
          ∑z∈parityOriginalHistoricalActualPhysicalZDyadicFibre434
            d L band slot δ Y e m mp J Z,
            ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
              (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
              U mp n := hReindex
    _ = _ := by
      apply Finset.sum_congr rfl
      intro mp hmp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSourceCharacterDyadicFourierTrunc -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- HISTORICAL ORIGINAL Parity (4.10)-(4.16) signed physical χ,k,Z
cofactor sum with literal nested original m' → canonical z → n
SOURCE fibres, the actual original full h=-2 Q/P/H0/b629 alpha
and e/n smoothing weight, equals ONE true low-frequency Euclidean
3D Fourier correlation integral, up to an EXPLICIT certified error.

The error is ≤ source actual complex cofactor ℓ1 mass times the
finite ORIGINAL 3D pre-Fourier derivative budget B_H/T^H.
No supposition of B_H<<L^C, no extended or guessed physical term,
no signed-to-positive replacement, no full Parity(4.17) or TypeII(4.2)
is made. This closes the exact algebra from the TRUE nested historical
character/dyadic offdiagonal to its Fourier 3D integral precursor. -/
theorem parity_original_historical_actual_nested_character_dyadic_3d_trunc434
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (U E V : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hDyad : ∀mp∈K, U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x : ℝ, buf x≠0 → a≤x ∧ x≤b)
    (hBufOne : ∀x∈Set.Icc (0:ℝ) (Real.log 2),buf x=1)
    (hZ : 0<Z) (H : ℕ) (T : ℝ) (hT : 0<T) :
    ‖(∑mp∈parityOriginalHistoricalActualPhysicalDyadicMFibre434
        d L band slot δ Y e m K J k Z,
        χ (mp : ZMod (2*k.natAbs)) *
        (∑z∈parityOriginalHistoricalActualPhysicalZDyadicFibre434
          d L band slot δ Y e m mp J Z,
          ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
            (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
            ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) *
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp)) -
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434
          (parityOriginalHistoricalActualKZPhysicalEventCarrier434
            d L band slot δ Y e m K J k Z)
          (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
            d L band slot δ ξ rho α signed Y e m k χ)
          (parityOriginalHistoricalPhysicalFourierEventTriple434
            (U:ℝ) (Z:ℝ) e m (fun q : ℕ×ℕ=>q.1) (fun q : ℕ×ℕ=>q.2))
          (parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport) ζ)‖ ≤
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ) *
      (parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport)/T^H) := by
  have hEq := parity_original_historical_actual_k_z_weighted_character_eq_original_fibre434
    d L hL band slot δ ξ rho α signed Y e m K J k Z χ he E V
  have hTrunc := parity_original_historical_actual_k_z_physical_fourier_trunc434
    d L hL band slot δ ξ rho α signed Y e m K J k Z χ he
    U E V hU hE hV hmLo hmHi hDyad
    buf a b hBufSmooth hBufSupport hBufOne hZ H T hT
  rw [hEq] at hTrunc
  exact hTrunc
end Green64Analytic.Parity

end

end

