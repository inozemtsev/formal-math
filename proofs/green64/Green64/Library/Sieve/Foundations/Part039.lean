module

public import Green64.Library.Sieve.Foundations.Part038
public import Green64.Library.Sieve.Foundations.Part012
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Green64.Library.Sieve.Foundations.Part017
public import Green64.Library.Sieve.Foundations.Part018
public import Green64.Library.Sieve.Foundations.Part032
public import Green64.Library.Sieve.Foundations.Part016
public import Green64.Library.Sieve.Foundations.Part010
public import Green64.Library.Sieve.Foundations.Part013

@[expose] public section

/-!
# Sieve / Foundations / Part039

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PsiMellinRestrictedOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Genuine original Ψ-Mellin OUTER complex integral over a bounded
real frequency range, paying the FIXED Schwartz Fourier L1 norm
and no second Q-selected gate. This is the correct downstream
interface for the cap-free physical Bprime Q-summed source evaluated
at rho=2πs. A strong measurability hypothesis is explicit because
pointwise signed correlations alone do not prove the actual outer
function measurable; this abstract lemma does NOT assert full TypeII.
Unlike bogus |integral of subset| monotonicity, the integrand is
first multiplied by its literal Mellin kernel and then bounded using
complex norm triangle plus the positive integral. -/
theorem parity_original_actual_Psi_Mellin_restricted_outer_L1_bound434
    (L : ℝ) (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (T C : ℝ) (hC : 0≤C)
    (B : ℝ → ℂ) (hMeas : AEStronglyMeasurable B)
    (hBound : ∀s∈Set.Icc (-T) T, ‖B s‖≤C) :
    ‖∫s in Set.Icc (-T) T,
       parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s * B s‖ ≤
      C * (∫s : ℝ, ‖(𝓕 (parityOriginalLogCutoff434
         (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖) := by
  let f := (𝓕 (parityOriginalLogCutoff434
    (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ))
  let K : ℝ → ℂ := parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport
  let S : Set ℝ := Set.Icc (-T) T
  have hS : MeasurableSet S := measurableSet_Icc
  have hKI : Integrable K := parity_original_true_Psi_Mellin_kernel_integrable434
    L Psi hSmooth hSupport
  let G := S.indicator B
  have hGM : AEStronglyMeasurable G := hMeas.indicator hS
  have hGB : ∀s,‖G s‖≤C := by
    intro s
    by_cases hs : s∈S
    · simpa only [G,Set.indicator_of_mem hs] using hBound s hs
    · simp [G,Set.indicator_of_notMem hs,hC]
  have hProdMeas : AEStronglyMeasurable (fun s => K s * G s) :=
    hKI.aestronglyMeasurable.mul hGM
  have hKIprod : Integrable (fun s => K s * G s) := by
    apply (hKI.norm.const_mul C).mono hProdMeas
    filter_upwards [] with s
    rw [norm_mul]
    have hh := mul_le_mul_of_nonneg_left (hGB s) (norm_nonneg (K s))
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC (norm_nonneg (K s))),
      mul_comm] using hh
  have hIntegrand :
      (∫s in S,K s*B s)=(∫s : ℝ,K s*G s) := by
    rw [←integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [] with s
    exact Set.indicator_mul_right S K B
  have hBoundIntegrand :
      ‖∫s : ℝ,K s*G s‖≤C*(∫s:ℝ,‖K s‖) := by
    calc
      _ ≤ ∫s : ℝ,‖K s*G s‖ := norm_integral_le_integral_norm _
      _ ≤ ∫s : ℝ,C*‖K s‖ := by
        apply integral_mono hKIprod.norm ((hKI.norm).const_mul C)
        intro s
        change ‖K s*G s‖≤C*‖K s‖
        calc
          _ = ‖K s‖*‖G s‖ := norm_mul _ _
          _ ≤ ‖K s‖*C := mul_le_mul_of_nonneg_left (hGB s) (norm_nonneg _)
          _ = _ := by ring
      _ = C*(∫s : ℝ,‖K s‖) := integral_const_mul _ _
  rw [hIntegrand]
  calc
    _ ≤ C*(∫s : ℝ,‖K s‖) := hBoundIntegrand
    _ = C*(∫s : ℝ,‖f s‖) := by
      congr 1
      exact parity_original_true_Psi_Mellin_kernel_L1_mass_exact434
        L Psi hSmooth hSupport
end Green64Analytic.Parity

end

end

/-! ## PsiMellinSchwartzTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The TRUE original 2πs Ψ-Mellin kernel has arbitrary polynomial
absolute L1 tails. For any real Mellin cutoff radius R>0 and natural
moment order H, the original high-frequency tail has EXACT loss
R^{-H} times an actual Fourier-Schwartz weighted moment. The
moment is independent of the large parameter L because the
exp(-2πisL) phase is unimodular. This is genuine source analysis,
not a fictitious pointwise cutoff of the e/n/k/z sums or a new
auxiliary Mellin kernel. It can be used to pay the unrestricted
|rho|=2π|s| tail AFTER bounding the physical Bprime coefficients. -/
theorem parity_original_actual_true_Psi_Mellin_Schwartz_abs_tail434
    (L : ℝ) (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (R : ℝ) (hR : 0<R) (H : ℕ) :
    (∫s in {s : ℝ | R≤‖s‖},
      ‖parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s‖) ≤
    (R^H)⁻¹ *
      (∫s : ℝ,‖s‖^H *
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖) := by
  let f := (𝓕 (parityOriginalLogCutoff434
    (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ))
  let M : ℝ → ℂ := parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport
  let S : Set ℝ := {s : ℝ | R≤‖s‖}
  have hRpow : 0<R^H := pow_pos hR _
  have hSclosed : IsClosed S := isClosed_Ici.preimage continuous_norm
  have hS : MeasurableSet S := hSclosed.measurableSet
  have hI0 : Integrable (fun s : ℝ => ‖f s‖) := f.integrable.norm
  have hIH : Integrable (fun s : ℝ => ‖s‖^H*‖f s‖) :=
    f.integrable_pow_mul volume H
  have hIscale : Integrable (fun s : ℝ => (R^H)⁻¹*(‖s‖^H*‖f s‖)) :=
    hIH.const_mul _
  have hMajor (s : ℝ) :
      (S.indicator (fun s : ℝ => ‖f s‖)) s ≤
        (R^H)⁻¹*(‖s‖^H*‖f s‖) := by
    by_cases hs : s∈S
    · simp only [Set.indicator_of_mem hs]
      have hsNorm : R≤‖s‖ := hs
      have hPow : R^H≤‖s‖^H := by gcongr
      have hh := mul_le_mul_of_nonneg_right hPow (norm_nonneg (f s))
      calc
        ‖f s‖ = (R^H)⁻¹*((R^H)*‖f s‖) := by
          rw [←mul_assoc,inv_mul_cancel₀ hRpow.ne',one_mul]
        _ ≤ (R^H)⁻¹*(‖s‖^H*‖f s‖) :=
          mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hRpow.le)
    · simp only [Set.indicator_of_notMem hs]
      positivity
  have hNorm (s : ℝ) : ‖M s‖=‖f s‖ :=
    parity_original_true_Psi_Mellin_kernel_norm_exact434
      L Psi hSmooth hSupport s
  have hEqualSet :
      (∫s in S,‖M s‖)=(∫s in S,‖f s‖) := by
    apply integral_congr_ae
    filter_upwards [] with s
    exact hNorm s
  calc
    (∫s in S,‖M s‖) = ∫s in S,‖f s‖ := hEqualSet
    _ = ∫s : ℝ, S.indicator (fun s => ‖f s‖) s := (integral_indicator hS).symm
    _ ≤ ∫s : ℝ,(R^H)⁻¹*(‖s‖^H*‖f s‖) :=
      integral_mono (hI0.indicator hS) hIscale hMajor
    _ = (R^H)⁻¹*(∫s : ℝ,‖s‖^H*‖f s‖) := integral_const_mul _ _
end Green64Analytic.Parity

end

end

/-! ## PsiMellinSourceUFullTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The ORIGINAL Parity Ψ(u/exp L) Mellin inversion for the literal
reserved-Q e-first physical H0 source. This identity holds at each
u>0 before any post-Cauchy source extension and uses genuine rho=2πs,
without suppressing the original Q/P factorial or the W1/E signed
source. It is an equality of integrals, NOT pointwise in s. -/
theorem parity_original_intrinsic_e_first_Psi_Mellin_exact434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : 0<u) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
      parityOriginalSignedIntrinsicEFirstFullAtU434
        d L E u signed band slot 0 xi =
    ∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      parityOriginalSignedIntrinsicEFirstFullAtU434
        d L E u signed band slot (2*Real.pi*s) xi := by
  let alpha : ℕ → ℂ := fun _ => 0
  let K : Finset ℕ := ∅
  let chi : DirichletCharacter ℂ 1 := 1
  have hOld := parity_original_signed_window_Psi_Mellin_H_exact434
    d L E hL hd u hu signed band slot K alpha 1 chi 0 0 xi
    Psi hSmooth hSupport
  have hZero := parity_original_signed_window_mellin_H_eq_intrinsic_e_first434
    d L E hL hd u hu.ne' signed band slot K alpha 1 chi 0 0 0 xi
  rw [hZero] at hOld
  have hArg (s : ℝ) := parity_original_signed_window_mellin_H_eq_intrinsic_e_first434
    d L E hL hd u hu.ne' signed band slot K alpha 1 chi 0 0 (2*Real.pi*s) xi
  convert hOld using 1
  apply integral_congr_ae
  filter_upwards [] with s
  rw [hArg s]

/-- Mellin integrability of the SAME exact original e-first source.
No extra Fourier envelope or invented norm assumption is inserted. -/
theorem parity_original_intrinsic_e_first_Psi_Mellin_integrable434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : 0<u) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    Integrable (fun s : ℝ =>
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) xi) := by
  let alpha : ℕ → ℂ := fun _ => 0
  let K : Finset ℕ := ∅
  let chi : DirichletCharacter ℂ 1 := 1
  have hOld := parity_original_signed_window_Psi_Mellin_H_integrable434
    d L E hL hd u hu signed band slot K alpha 1 chi 0 0 xi
    Psi hSmooth hSupport
  apply hOld.congr
  filter_upwards [] with s
  rw [parity_original_signed_window_mellin_H_eq_intrinsic_e_first434
    d L E hL hd u hu.ne' signed band slot K alpha 1 chi 0 0 (2*Real.pi*s) xi]

/-- Source Ψ support kills u>2 exp L AFTER integrating the genuine
Mellin s variable. A fixed-frequency Cauchy integrand need not vanish,
so the theorem deliberately states a full Mellin integral equality. -/
theorem parity_original_intrinsic_e_first_Psi_Mellin_outside_u_zero434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : 0<u) (huFar : 2*Real.exp L < (u:ℝ))
    (signed : Bool) (band : Fin (d+1)) (slot : Fin 20)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2) :
    (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      parityOriginalSignedIntrinsicEFirstFullAtU434
        d L E u signed band slot (2*Real.pi*s) xi) = 0 := by
  have hExp : 0<Real.exp L := Real.exp_pos L
  have hRatio : 2 < (u:ℝ)/Real.exp L := by
    apply (lt_div_iff₀ hExp).mpr
    nlinarith [huFar]
  have hPsiZero : Psi ((u:ℝ)/Real.exp L)=0 := by
    by_contra hNonzero
    have hMem : ((u:ℝ)/Real.exp L) ∈ Function.support Psi := by
      simpa only [Function.mem_support] using hNonzero
    have hh := (hPsiSource hMem).2
    exact (not_le_of_gt hRatio) hh
  have hEq := parity_original_intrinsic_e_first_Psi_Mellin_exact434
    d L E hL hd u hu signed band slot xi Psi hSmooth hSupport
  rw [hPsiZero] at hEq
  simp only [Complex.ofReal_zero,zero_mul] at hEq
  exact hEq.symm
end Green64Analytic.Parity

end

end

/-! ## PsiMellinFullFiniteUFubini -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- True finite Fubini for ORIGINAL Parity Ψ Mellin and the complete
reserved Q physical e-first H0 source. The finite u carrier is kept
without an invented hard cutoff; integrability holds at each u>0.
Arbitrary complex W(u) can be the literal original h=-2 sum over
m*n=u+2, including actual alpha_m and beta_n. -/
theorem parity_original_intrinsic_e_first_Psi_Mellin_finite_u_fubini434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (S : Finset ℕ) (hS : ∀u∈S,0<u)
    (signed : Bool) (band : Fin (d+1)) (slot : Fin 20)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (W : ℕ → ℂ) :
    (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      (∑u∈S,
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) xi * W u)) =
    ∑u∈S,
      ((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot 0 xi * W u := by
  classical
  let M : ℝ → ℂ := parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport
  let H : ℕ → ℝ → ℂ := fun u s =>
    parityOriginalSignedIntrinsicEFirstFullAtU434
      d L E u signed band slot (2*Real.pi*s) xi
  let g : ℕ → ℝ → ℂ := fun u s => (M s * H u s) * W u
  have hGI : ∀u∈S, Integrable (g u) := by
    intro u hu
    have hI := parity_original_intrinsic_e_first_Psi_Mellin_integrable434
      d L E hL hd u (hS u hu) signed band slot xi Psi hSmooth hSupport
    exact hI.mul_const (W u)
  have hPhase (s : ℝ) : M s * (∑u∈S,H u s * W u)=∑u∈S,g u s := by
    dsimp [g]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  calc
    (∫ s : ℝ, M s * (∑u∈S,H u s * W u)) =
      ∫ s : ℝ,∑u∈S,g u s := by
        apply integral_congr_ae
        filter_upwards [] with s
        exact hPhase s
    _ = ∑u∈S, ∫ s : ℝ,g u s := integral_finset_sum S hGI
    _ = ∑u∈S,
        ((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
          parityOriginalSignedIntrinsicEFirstFullAtU434
            d L E u signed band slot 0 xi * W u := by
          apply Finset.sum_congr rfl
          intro u hu
          have hEq := parity_original_intrinsic_e_first_Psi_Mellin_exact434
            d L E hL hd u (hS u hu) signed band slot xi
            Psi hSmooth hSupport
          dsimp [g,M,H]
          rw [integral_mul_const]
          exact congrArg (fun z : ℂ => z*W u) hEq.symm

/-- EXPANDING the actual finite u carrier beyond floor(2exp L)
to the corrected Ybox is EXACT only AFTER its complete Ψ-Mellin
integration. For fixed s the newly included source terms need not
vanish. This transports the original pre-Cauchy `u<=2x` source
support to the cap-free Cauchy geometry without any signed-subsum
norm inequality or exponential multiplicity bound. -/
theorem parity_original_intrinsic_Psi_Mellin_finite_u_cap_extension434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (Yhi : ℕ) (hYhi : ⌊2*Real.exp L⌋₊≤Yhi)
    (signed : Bool) (band : Fin (d+1)) (slot : Fin 20)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (W : ℕ → ℂ) :
    (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      (∑u∈Finset.Ioc 0 Yhi,
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) xi * W u)) =
    (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      (∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) xi * W u)) := by
  classical
  let Y0 := ⌊2*Real.exp L⌋₊
  let Sh : Finset ℕ := Finset.Ioc 0 Yhi
  let S0 : Finset ℕ := Finset.Ioc 0 Y0
  have hPosh : ∀u∈Sh,0<u := by
    intro u hu
    exact (Finset.mem_Ioc.mp hu).1
  have hPos0 : ∀u∈S0,0<u := by
    intro u hu
    exact (Finset.mem_Ioc.mp hu).1
  have hSub : S0 ⊆ Sh := by
    intro u hu
    obtain ⟨h0,hu0⟩ := Finset.mem_Ioc.mp hu
    exact Finset.mem_Ioc.mpr ⟨h0,hu0.trans hYhi⟩
  have hTail (u : ℕ) (hu : u∈Sh) (huNot : u∉S0) :
      (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
        L Psi hSmooth hSupport s *
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) xi) = 0 := by
    have huPos : 0<u := hPosh u hu
    have huGt : Y0<u := by
      by_contra hh
      have huLe : u≤Y0 := Nat.le_of_not_gt hh
      exact huNot (Finset.mem_Ioc.mpr ⟨huPos,huLe⟩)
    have hFloor : 2*Real.exp L < (Y0:ℝ)+1 := by
      exact Nat.lt_floor_add_one (2*Real.exp L)
    have hCast : (Y0:ℝ)+1≤(u:ℝ) := by
      have hi : Y0+1≤u := by omega
      exact_mod_cast hi
    have huFar := hFloor.trans_le hCast
    exact parity_original_intrinsic_e_first_Psi_Mellin_outside_u_zero434
      d L E hL hd u huPos huFar signed band slot xi
      Psi hSmooth hSupport hPsiSource
  let H : ℕ → ℂ := fun u =>
    (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      parityOriginalSignedIntrinsicEFirstFullAtU434
        d L E u signed band slot (2*Real.pi*s) xi) * W u
  have hSum : (∑u∈Sh,H u)=(∑u∈S0,H u) := by
    symm
    apply Finset.sum_subset hSub
    intro u hu huNot
    have hh := hTail u hu huNot
    simp only [H,hh,zero_mul]
  have hFubinih := parity_original_intrinsic_e_first_Psi_Mellin_finite_u_fubini434
    d L E hL hd Sh hPosh signed band slot xi Psi hSmooth hSupport W
  have hFubini0 := parity_original_intrinsic_e_first_Psi_Mellin_finite_u_fubini434
    d L E hL hd S0 hPos0 signed band slot xi Psi hSmooth hSupport W
  have hReplace (u : ℕ) (hu : u∈Sh) : H u =
      ((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot 0 xi * W u := by
    have hEq := parity_original_intrinsic_e_first_Psi_Mellin_exact434
      d L E hL hd u (hPosh u hu) signed band slot xi Psi hSmooth hSupport
    dsimp [H]
    exact congrArg (fun z : ℂ => z*W u) hEq.symm
  change (∫s:ℝ, _ * (∑u∈Sh,_)) =
    (∫s:ℝ, _ * (∑u∈S0,_))
  calc
    _ = ∑u∈Sh,H u := by
      rw [hFubinih]
      apply Finset.sum_congr rfl
      intro u hu
      exact (hReplace u hu).symm
    _ = ∑u∈S0,H u := hSum
    _ = _ := by
      rw [hFubini0]
      apply Finset.sum_congr rfl
      intro u hu
      exact hReplace u (hSub hu)
end Green64Analytic.Parity

end

end

/-! ## PsiMellinTrueHighOuterBound -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- True original Parity Ψ-Mellin integral over ALL real |s|>=R, with
its genuine 2π logarithmic Fourier-Schwartz kernel. An arbitrary
complex physical source B(s) may be inserted provided its actual
strong measurability and pointwise uniform norm bound have been
proved; no fictional pointwise cutoff in s and no |signed subsum|
monotonicity are used. The high-s norm is paid with exactly the
true source moment R^-H * integral |s|^H |Ψ-Fourier(s)|. -/
theorem parity_original_true_Psi_Mellin_high_outer_L1_bound434
    (L : ℝ) (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (R : ℝ) (hR : 0<R) (H : ℕ)
    (C : ℝ) (hC : 0≤C)
    (B : ℝ → ℂ) (hMeas : AEStronglyMeasurable B)
    (hBound : ∀s:ℝ,‖B s‖≤C) :
    ‖∫s in {s : ℝ | R≤‖s‖},
        parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s * B s‖ ≤
      C*((R^H)⁻¹ *
        (∫s : ℝ,‖s‖^H *
          ‖(𝓕 (parityOriginalLogCutoff434
            (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖)) := by
  let K : ℝ → ℂ := parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport
  let S : Set ℝ := {s : ℝ | R≤‖s‖}
  have hKInt : Integrable K :=
    parity_original_true_Psi_Mellin_kernel_integrable434 L Psi hSmooth hSupport
  have hMeasProd : AEStronglyMeasurable (fun s => K s*B s) :=
    hKInt.aestronglyMeasurable.mul hMeas
  have hProd : Integrable (fun s => K s*B s) := by
    apply (hKInt.norm.const_mul C).mono hMeasProd
    filter_upwards [] with s
    rw [norm_mul]
    have hLE := mul_le_mul_of_nonneg_left (hBound s) (norm_nonneg (K s))
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC (norm_nonneg _)),
      mul_comm] using hLE
  have hMain :
      ‖∫s in S,K s*B s‖ ≤ C*(∫s in S,‖K s‖) := by
    calc
      _ ≤ ∫s in S,‖K s*B s‖ := norm_integral_le_integral_norm _
      _ ≤ ∫s in S,C*‖K s‖ := by
        apply integral_mono hProd.norm.integrableOn ((hKInt.norm.const_mul C).integrableOn)
        intro s
        change ‖K s*B s‖≤C*‖K s‖
        rw [norm_mul]
        have hh := mul_le_mul_of_nonneg_left (hBound s) (norm_nonneg (K s))
        simpa only [mul_comm] using hh
      _ = C*(∫s in S,‖K s‖) := integral_const_mul _ _
  have hTail := parity_original_actual_true_Psi_Mellin_Schwartz_abs_tail434
    L Psi hSmooth hSupport R hR H
  calc
    _ ≤ C*(∫s in S,‖K s‖) := hMain
    _ ≤ C*((R^H)⁻¹ *
      (∫s : ℝ,‖s‖^H *
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖)) :=
        mul_le_mul_of_nonneg_left hTail hC
end Green64Analytic.Parity

end

end

/-! ## PsiMellinFullSpectrumSplit -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1300000

/-- Correct set identity for the EXACT original real Mellin frequency
cutoff: complement of the open low window (-R,R) equals
{|s|>=R}. In particular the two endpoints must only be deleted on
a Lebesgue-null set; the source cannot treat both Icc and high tail
as strictly disjoint sets. This is a pointwise identity for R>=0. -/
theorem parity_original_true_Mellin_high_set_eq_low_compl434
    (R : ℝ) (hR : 0≤R) :
    (Set.Ioo (-R) R)ᶜ = {s : ℝ | R≤‖s‖} := by
  ext s
  simp only [Set.mem_compl_iff,Set.mem_Ioo,Set.mem_setOf_eq,not_and_or,
    not_lt,Real.norm_eq_abs]
  constructor
  · intro h
    rcases h with hNeg|hPos
    · have hNonpos : s ≤ 0 := by linarith
      rw [abs_of_nonpos hNonpos]
      linarith
    · have hNonneg : 0 ≤ s := by linarith
      rwa [abs_of_nonneg hNonneg]
  · intro h
    rcases le_total s 0 with hs|hs
    · left
      rw [abs_of_nonpos hs] at h
      linarith
    · right
      rwa [abs_of_nonneg hs] at h

/-- Original full real Ψ-Mellin complex integral splits exactly into
the source bounded Icc[-R,R] and Schwartz tail {|s|>=R} after
paying null endpoints. The source integrand remains the SAME complex
F(s)=KΨ(s)*B(s) in both pieces. Its absolute integrability follows
from the true kernel's L1 mass, actual strong measurability of B,
and a uniform physical source norm bound; no monotonicity of a
signed integral is asserted, nor pointwise Y0↔Ybox equivalence. -/
theorem parity_original_true_Psi_Mellin_full_split434
    (L : ℝ) (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (R : ℝ) (hR : 0≤R)
    (B : ℝ → ℂ) (hBmeas : AEStronglyMeasurable B)
    (C : ℝ) (hC : 0≤C) (hBound : ∀s:ℝ,‖B s‖≤C) :
    (∫s : ℝ,
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s * B s) =
    (∫s in Set.Icc (-R) R,
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s * B s) +
    (∫s in {s : ℝ | R≤‖s‖},
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s * B s) := by
  let K : ℝ → ℂ := parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport
  let F : ℝ → ℂ := fun s => K s * B s
  have hKI : Integrable K := parity_original_true_Psi_Mellin_kernel_integrable434
    L Psi hSmooth hSupport
  have hFI : Integrable F := by
    have hFM : AEStronglyMeasurable F := hKI.aestronglyMeasurable.mul hBmeas
    apply (hKI.norm.const_mul C).mono hFM
    filter_upwards [] with s
    change ‖K s*B s‖≤‖C*‖K s‖‖
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC (norm_nonneg _))]
    exact (mul_le_mul_of_nonneg_left (hBound s) (norm_nonneg (K s))).trans_eq
      (by ring)
  have hSet := parity_original_true_Mellin_high_set_eq_low_compl434 R hR
  have hSplit := integral_add_compl (s:=Set.Ioo (-R) R) measurableSet_Ioo hFI
  rw [hSet] at hSplit
  have hBorder :
      (∫s in Set.Icc (-R) R,F s) = (∫s in Set.Ioo (-R) R,F s) :=
    integral_Icc_eq_integral_Ioo
  change (∫s : ℝ,F s) = (∫s in Set.Icc (-R) R,F s) +
    (∫s in {s : ℝ | R≤‖s‖},F s)
  rw [hBorder]
  exact hSplit.symm

/-- Given genuine source low/high complex Mellin norm bounds for
the SAME cap-free Bprime outer and strong measurability, the full
original Mellin integral has the SUM of the two costs. Both use
actual source 2π and no artificial spectral high cutoff. -/
theorem parity_original_true_Psi_Mellin_full_norm_le_parts434
    (L : ℝ) (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (R : ℝ) (hR : 0≤R)
    (B : ℝ → ℂ) (hBmeas : AEStronglyMeasurable B)
    (C : ℝ) (hC : 0≤C) (hBound : ∀s:ℝ,‖B s‖≤C)
    (Dlow Dhigh : ℝ)
    (hLow : ‖∫s in Set.Icc (-R) R,
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s * B s‖≤Dlow)
    (hHigh : ‖∫s in {s : ℝ | R≤‖s‖},
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s * B s‖≤Dhigh) :
    ‖∫s : ℝ,
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s * B s‖≤
      Dlow+Dhigh := by
  rw [parity_original_true_Psi_Mellin_full_split434
    L Psi hSmooth hSupport R hR B hBmeas C hC hBound]
  exact (norm_add_le _ _).trans (add_le_add hLow hHigh)
end Green64Analytic.Parity

end

end

/-! ## PsiMellinTrueYboxExtension -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- The CORRECT original positive containing Ybox=ceil(6UV) is
larger than the old u<=floor(2exp L) pre-Cauchy carrier for ALL
exp L<=UV. This is geometry only, not a complex sum dominance. -/
theorem parity_original_true_Ybox_contains_old_preCauchy_u434
    (L U V : ℝ) (hUV : Real.exp L≤U*V) :
    ⌊2*Real.exp L⌋₊≤Nat.ceil (6*U*V) := by
  have hFloor : ((⌊2*Real.exp L⌋₊:ℕ):ℝ)≤2*Real.exp L :=
    Nat.floor_le (by positivity)
  have hScale : 2*Real.exp L≤6*U*V := by nlinarith [hUV]
  have hCeil : 6*U*V≤((Nat.ceil (6*U*V)):ℝ) := Nat.le_ceil _
  exact_mod_cast hFloor.trans (hScale.trans hCeil)

/-- ORIGINAL pre-Cauchy full e-first Mellin source sum at a fixed
Q frequency is EXACTLY invariant upon extension of the finite
u carrier to Ybox=ceil6UV, after integrating Ψ(u/x) over s.
No fixed-s zero statement or artificial cap Y=floor(2x) is used. -/
theorem parity_original_true_Psi_Mellin_e_first_Ybox_exact434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hUV : Real.exp L≤U*V)
    (signed : Bool) (band : Fin (d+1)) (slot : Fin 20)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (W : ℕ → ℂ) :
    (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      (∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) xi * W u)) =
    (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      (∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) xi * W u)) :=
  parity_original_intrinsic_Psi_Mellin_finite_u_cap_extension434
    d L E hL hd (Nat.ceil (6*U*V))
    (parity_original_true_Ybox_contains_old_preCauchy_u434 L U V hUV)
    signed band slot xi Psi hSmooth hSupport hPsiSource W

/-- This is the complete ORIGINAL e-first Ψ-Mellin and REAL full
Q-Fourier BOX after the genuine finite u cap Ybox, not a hard mask
inserted on s. The original fixed Schwartz kernel Ψ and 2πs remain
inside the integral. -/
theorem parity_original_intrinsic_Psi_Mellin_QBox_Ybox_exact434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hUV : Real.exp L≤U*V)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (T : ℝ) :
    parityOriginalSignedIntrinsicPsiPostIntegrated434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed
      (Nat.ceil (6*U*V)) T =
    parityOriginalSignedIntrinsicPsiPostIntegrated434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed
      ⌊2*Real.exp L⌋₊ T := by
  unfold parityOriginalSignedIntrinsicPsiPostIntegrated434
  apply integral_congr_ae
  filter_upwards [] with xi
  unfold parityOriginalSignedIntrinsicPsiBprimeAtXi434
  exact parity_original_true_Psi_Mellin_e_first_Ybox_exact434
    d L E U V hL hd hUV signed band slot xi
    Psi hSmooth hSupport hPsiSource
    (fun u => ∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
      alpha z.1*beta z.2)

/-- The previously source-validated historical Parity e/n Cauchy Q box
inherits the SAME exact u-support enlargement Y0→Ybox AFTER Mellin.
No fixed-frequency Cauchy sum is truncated erroneously. -/
theorem parity_original_historical_Psi_Mellin_Cauchy_QBox_Ybox_exact434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hUV : Real.exp L≤U*V)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (T : ℝ) :
    parityOriginalActualHistoricalPsiMellinCauchyQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed
      (Nat.ceil (6*U*V)) T =
    parityOriginalActualHistoricalPsiMellinCauchyQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed
      ⌊2*Real.exp L⌋₊ T := by
  have hEq (Y : ℕ) :
      parityOriginalActualHistoricalPsiMellinCauchyQBox434
        d L E band slot Psi hSmooth hSupport K J alpha beta signed Y T =
      parityOriginalSignedIntrinsicPsiPostIntegrated434
        d L E band slot Psi hSmooth hSupport K J alpha beta signed Y T := by
    rw [←parity_original_actual_historical_Psi_Bprime_QBox_eq_Cauchy_Mellin434]
    rw [←parity_original_signed_cartesian_Bprime_eq_historical_AE434]
    exact (parity_original_signed_intrinsic_Psi_post_eq_cartesian434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed Y T).symm
  rw [hEq (Nat.ceil (6*U*V)),hEq ⌊2*Real.exp L⌋₊]
  exact parity_original_intrinsic_Psi_Mellin_QBox_Ybox_exact434
    d L E U V hL hd hUV band slot Psi hSmooth hSupport hPsiSource
    K J alpha beta signed T
end Green64Analytic.Parity

end

end

/-! ## PsiMellinCapfreeBprimeJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13500000

/-- The literal original Parity(4.7) AFTER Ψ-Mellin integration and
full Q-Fourier box, with an honest *cap-free* physical Bprime at each
frequency rho=2πs. There is ONE original selected-Q a_e(e) factor
inside each Bprime, no extra multiplicative Q gate, original beta,
H0, W1 and signed E parity unaltered. -/
def parityOriginalActualPsiMellinCapfreeBprimeQBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t : ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (T : ℝ) : ℂ :=
  ∫ xi : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
          parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
            d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed))
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- Exact SOURCE join from the historical selected Q-allocated
original Psi-Mellin Cauchy source with actual Ybox=ceil(6UV) to
the honest cap-free natural e|u and a_v(u/e) Bprime, including ALL
real Mellin and N-dimensional Q Fourier frequencies. The source
selected e's must be positive (derived from original Q labels for
large L). No new e/Pfree gate is inserted in the subsequent positive
Cauchy square. -/
theorem parity_original_actual_historical_Psi_Mellin_Ybox_eq_capfree434
    (d : ℕ) (L E U V : ℝ)
    (hL : 0<L) (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1)) (slot : Fin 20)
    (hSelected : ∀ (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot delta, 0<e)
    (K J : Finset ℕ) (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t : ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (alpha beta : ℕ → ℂ) (signed : Bool) (T : ℝ) :
    parityOriginalActualHistoricalPsiMellinCauchyQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed
      (Nat.ceil (6*U*V)) T =
    parityOriginalActualPsiMellinCapfreeBprimeQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed T := by
  unfold parityOriginalActualHistoricalPsiMellinCauchyQBox434
    parityOriginalActualPsiMellinCapfreeBprimeQBox434
  apply integral_congr_ae
  filter_upwards [] with xi
  unfold parityOriginalActualHistoricalPsiMellinCauchyAtXi434
  apply integral_congr_ae
  filter_upwards [] with s
  let D := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  have hSourceFinite :
      (∑delta : Fin D → Bool,
        parityOriginalHistoricalCauchyAtDelta434
          d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed
          (Nat.ceil (6*U*V))) =
      (∑delta : Fin D → Bool,
        parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
          d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed) := by
    apply Finset.sum_congr rfl
    intro delta hdelta
    exact parity_original_historical_selected_Q_Cauchy_box_eq_no_u_cap434
      d L E U V hL hU hV band slot delta xi (2*Real.pi*s)
      K J alpha beta signed (hSelected delta) hK hJ
  exact congrArg
    (fun z : ℂ => parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s * z) hSourceFinite

/-- All/source pre-Cauchy original full Psi-Mellin represented at Y0
is exactly the cap-free physical Parity(4.7) Bprime Q-box integral:
first extend Y0 to Ybox AFTER Mellin (proved in source), then use the
original Q-selected e/vStar physical singleton and beta-n identity.
No false pointwise Mellin s support or norm comparison of signed
subsum is used. -/
theorem parity_original_actual_historical_Psi_Mellin_Y0_eq_capfree434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0≤U) (hV : 0≤V) (hUV : Real.exp L≤U*V)
    (band : Fin (d+1)) (slot : Fin 20)
    (hSelected : ∀ (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot delta, 0<e)
    (K J : Finset ℕ) (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t : ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (alpha beta : ℕ → ℂ) (signed : Bool) (T : ℝ) :
    parityOriginalActualHistoricalPsiMellinCauchyQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed
      ⌊2*Real.exp L⌋₊ T =
    parityOriginalActualPsiMellinCapfreeBprimeQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed T := by
  calc
    _ = parityOriginalActualHistoricalPsiMellinCauchyQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed
      (Nat.ceil (6*U*V)) T :=
      (parity_original_historical_Psi_Mellin_Cauchy_QBox_Ybox_exact434
        d L E U V hL hd hUV band slot Psi hSmooth hSupport hPsiSource
        K J alpha beta signed T).symm
    _ = _ := parity_original_actual_historical_Psi_Mellin_Ybox_eq_capfree434
      d L E U V hL hU hV band slot hSelected K J hK hJ
      Psi hSmooth hSupport alpha beta signed T
end Green64Analytic.Parity

end

end

/-! ## CapfreeBprimeRhoContinuous -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The genuine source Mellin phase n^(iρ) is continuous even for
n=0 (its actual source definition uses the real logarithm of n),
so there is no positivity assumption invented at this step. -/
theorem parity_original_actual_mellin_phase_rho_continuous434 (n : ℕ) :
    Continuous (fun rho : ℝ => sourceOriginalPureMellinPhase434 rho n) := by
  unfold sourceOriginalPureMellinPhase434
  fun_prop

/-- Original selected a_e coefficient, including the B590 Q Fourier
Gate and REAL e^(iρ) Mellin twist, is continuous in ρ at fixed ξ,
without inserting a second Q gate. -/
theorem parity_original_historical_AE_rho_continuous434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (e : ℕ) :
    Continuous (fun rho : ℝ =>
      parityOriginalHistoricalWindowAE434 d L E band slot delta xi rho e) := by
  unfold parityOriginalHistoricalWindowAE434
    parityOriginalSelectedEGateMellinCoefficient434
  by_cases hWin : parityOriginalHistoricalEWindow434 L E e
  · simpa only [hWin,ite_true] using
      (parity_original_actual_mellin_phase_rho_continuous434 e).mul_const
        (parityOriginalSelectedEGateFourierCoefficient434
          d L E band slot delta xi e)
  · simpa only [hWin,ite_false] using
      (continuous_const : Continuous (fun _ : ℝ => (0:ℂ)))

/-- Original true signed physical a_v(u/e) is continuous in the
REAL external Mellin ρ at fixed Q allocation, including unchanged
reserved H0, W1 and signed epsilon 1/E. -/
theorem parity_original_actual_intrinsic_AV_rho_continuous434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (signed : Bool) (vStar v : ℕ) :
    Continuous (fun rho : ℝ =>
      parityOriginalIntrinsicSignedAV434 d L band slot delta xi 0 rho signed vStar v) := by
  unfold parityOriginalIntrinsicSignedAV434
  exact ((parity_original_actual_mellin_phase_rho_continuous434 v).mul_const _).mul_const _

/-- The source e|u, vStar=ordinary_P(u/e) gate is fixed across Mellin
ρ; it is the genuine natural ungated post-Cauchy coefficient. -/
theorem parity_original_actual_ungated_EVStar_rho_continuous434
    (d : ℕ) (L : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (e vStar : ℕ) :
    Continuous (fun rho : ℝ =>
      parityOriginalHistoricalUngatedEVStarAtU434
        d L u signed band slot delta xi rho e vStar) := by
  unfold parityOriginalHistoricalUngatedEVStarAtU434
  by_cases hEV : e∣u ∧ vStar=sourceOriginalOrdinaryPart
      ((sourceOriginalPAllGroupIndices 20 L).attach.biUnion
        (sourceOriginalPAllActualBands 20 L)) (u/e)
  · simpa [hEV] using
      parity_original_actual_intrinsic_AV_rho_continuous434
        d L band slot delta xi signed vStar (u/e)
  · simpa [hEV] using (continuous_const : Continuous (fun _ : ℝ => (0:ℂ)))

/-- Literal no-u-cap post-Cauchy n,m physical endpoint with all e
and original source vStar finite carrier, continuous in its genuine
real Mellin phase ρ. No discarded u, n or m changes with ρ. -/
theorem parity_original_actual_ungated_Cauchy_physical_rho_continuous434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (signed : Bool) (e n m : ℕ) :
    Continuous (fun rho : ℝ =>
      parityOriginalHistoricalUngatedCauchyPhysicalNoUCap434
        d L band slot delta xi rho signed e n m) := by
  classical
  unfold parityOriginalHistoricalUngatedCauchyPhysicalNoUCap434
    parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
  apply continuous_finsetSum
  intro u hu
  by_cases hMN : 0 < m ∧ 0 < n ∧ m*n=u+2
  · simp only [hMN,ite_true]
    apply continuous_finsetSum
    intro vStar hVS
    exact parity_original_actual_ungated_EVStar_rho_continuous434
      d L u signed band slot delta xi e vStar
  · simpa only [hMN,ite_false] using
      (continuous_const : Continuous (fun _ : ℝ => (0:ℂ)))

/-- ACTUAL source-selected original Q a_e(e) and cap-free B509 a_v
Bprime are jointly continuous in physical Mellin rho at fixed Q
frequency ξ. This is the missing measurability input to legitimate
outer Ψ-Mellin integration of the *real* physical Bprime. -/
theorem parity_original_actual_capfree_Bprime_rho_continuous434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (signed : Bool) :
    Continuous (fun rho : ℝ =>
      parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
        d L E band slot delta xi rho K J alpha beta signed) := by
  classical
  unfold parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
  apply continuous_finsetSum
  intro e he
  apply continuous_finsetSum
  intro n hn
  have hAE := parity_original_historical_AE_rho_continuous434
    d L E band slot delta xi e
  have hPhysical : Continuous (fun rho : ℝ =>
      ∑m∈K,alpha m *
        parityOriginalHistoricalUngatedCauchyPhysicalNoUCap434
          d L band slot delta xi rho signed e n m) := by
    apply continuous_finsetSum
    intro m hm
    exact continuous_const.mul
      (parity_original_actual_ungated_Cauchy_physical_rho_continuous434
        d L band slot delta xi signed e n m)
  exact (hAE.mul_const (beta n)).mul hPhysical
end Green64Analytic.Parity

end

end

/-! ## HistoricalCauchyMellinJointContinuous -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The full ORIGINAL historical signed source Bprime is JOINTLY
continuous in real Mellin rho and the original variable-length
N-dimensional Q Fourier xi, not merely separately continuous.
The proof is the exact finite trigonometric polynomial
∑_{u:mn=u+2} exp(i rho log u)×actual B590 full Q coefficient.
No a.e. measurable assumption, universal alpha condition, or
new Q gate is inserted. This is the analytic input to the genuine
outer source Ψ Mellin after Lebesgue Q integration. -/
theorem parity_original_historical_Cauchy_joint_mellin_Q_continuous434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    Continuous (fun p : ℝ × (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
      parityOriginalHistoricalCauchyAtDelta434
        d L E band slot delta p.2 p.1 K J alpha beta signed Y) := by
  classical
  let n := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let W : ℕ → ℂ := fun u =>
    ∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
      alpha w.1*beta w.2
  let H : ℕ → (ℝ × (Fin n → ℝ)) → ℂ := fun u p =>
    sourceOriginalPureMellinPhase434 p.1 u *
    parityOriginalSignedFullQWindowAllGateFourierAtU434
      d L E u signed band slot delta p.2 * W u
  have hH (u : ℕ) : Continuous (H u) := by
    have hR : Continuous (fun p : ℝ × (Fin n → ℝ) =>
        sourceOriginalPureMellinPhase434 p.1 u) :=
      (parity_original_actual_mellin_phase_rho_continuous434 u).comp continuous_fst
    have hQ : Continuous (fun p : ℝ × (Fin n → ℝ) =>
        parityOriginalSignedFullQWindowAllGateFourierAtU434
          d L E u signed band slot delta p.2) :=
      (parity_original_actual_signed_window_fullQ_fibre_continuous434
        d L E u signed band slot delta).comp continuous_snd
    exact (hR.mul hQ).mul_const (W u)
  have hSum : Continuous (fun p : ℝ × (Fin n → ℝ) =>
      ∑u∈Finset.Ioc 0 Y,H u p) := by
    apply continuous_finsetSum
    intro u hu
    exact hH u
  have hEquality :
      (fun p : ℝ × (Fin n → ℝ) =>
        parityOriginalHistoricalCauchyAtDelta434
          d L E band slot delta p.2 p.1 K J alpha beta signed Y) =
      (fun p => ∑u∈Finset.Ioc 0 Y,H u p) := by
    funext p
    exact parity_original_historical_Cauchy_Mellin_polynomial434
      d L E hL hd band slot delta p.2 p.1
      K J alpha beta signed Y
  change Continuous (fun p : ℝ × (Fin n → ℝ) =>
      parityOriginalHistoricalCauchyAtDelta434
        d L E band slot delta p.2 p.1 K J alpha beta signed Y)
  rw [hEquality]
  exact hSum
end Green64Analytic.Parity

end

end

/-! ## CapfreeBprimeMellinQMeasurable -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10500000

/-- The ACTUAL original cap-free Bprime physical amplitude is
JOINTLY continuous in (real Mellin rho, full original Q Fourier xi).
This is transferred from the exact historical SOURCE finite-u
Mellin polynomial with the honest Ybox=ceil(6UV) and original
selected-Q e positivity. No replacement of source Q gate, no
pointwise Mellin truncation and no hypothetical measurable Bprime. -/
theorem parity_original_actual_capfree_Bprime_joint_rho_Q_continuous434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (hSelected : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
       d L E band slot delta,0<e)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (signed : Bool)
    (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V) :
    Continuous (fun p : ℝ × (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
        parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
          d L E band slot delta p.2 p.1 K J alpha beta signed) := by
  have hHistorical := parity_original_historical_Cauchy_joint_mellin_Q_continuous434
    d L E hL hd band slot delta K J alpha beta signed (Nat.ceil (6*U*V))
  have hEq :
      (fun p : ℝ × (Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
        parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
          d L E band slot delta p.2 p.1 K J alpha beta signed) =
      (fun p => parityOriginalHistoricalCauchyAtDelta434
          d L E band slot delta p.2 p.1 K J alpha beta signed
          (Nat.ceil (6*U*V))) := by
    funext p
    exact (parity_original_historical_selected_Q_Cauchy_box_eq_no_u_cap434
      d L E U V hL hU hV band slot delta p.2 p.1
      K J alpha beta signed hSelected hK hJ).symm
  rw [hEq]
  exact hHistorical

/-- Entire original Q Fourier volume BOX integral of the actual
cap-free physical Bprime is genuinely StronglyMeasurable in rho,
for all 20 reserved Q slots and independent original Boolean
allocation branches; this discharges the previously explicit
`hMeas` debt of the outer Ψ Mellin restricted integral theorem. -/
theorem parity_original_actual_capfree_all_slots_QBox_rho_stronglyMeasurable434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1))
    (hSelected : ∀ (slot : Fin 20)
      (delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,0<e)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (signed : Bool)
    (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V) (T : ℝ) :
    StronglyMeasurable (fun rho : ℝ =>
      ∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 (N:=(sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length) T,
            parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta xi rho K J alpha beta signed) := by
  classical
  apply Finset.stronglyMeasurable_fun_sum
  intro slot hslot
  apply Finset.stronglyMeasurable_fun_sum
  intro delta hdelta
  let n := (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length
  have hJoint := parity_original_actual_capfree_Bprime_joint_rho_Q_continuous434
    d L E U V hL hd hU hV band slot delta (hSelected slot delta)
    K J alpha beta signed hK hJ
  exact (hJoint.stronglyMeasurable.integral_prod_right' (ν :=
    (volume : Measure (Fin n → ℝ)).restrict
      (parityOriginalActualFullQFrequencyCube434 (N:=n) T)))
end Green64Analytic.Parity

end

end

/-! ## CapfreeRestrictedPsiMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Honest real rho=2*pi*s Mellin spectral range: the fixed source
cutoff |s|<=L^C0/(2*pi) EXACTLY stays in |rho|<=L^C0.
No tuning of the power after evaluating any original source sum. -/
theorem parity_original_true_Psi_Mellin_cutoff_rho_power434
    (L C0 : ℝ) (hL : 0<L)
    (s : ℝ) (hs : s∈Set.Icc (-(L^C0/(2*Real.pi))) (L^C0/(2*Real.pi))) :
    |2*Real.pi*s|≤L^C0 := by
  have hPi : 0<2*Real.pi := by positivity
  have hPow : 0<L^C0 := Real.rpow_pos_of_pos hL _
  have hAbs : |s|≤L^C0/(2*Real.pi) := abs_le.mpr hs
  calc
    |2*Real.pi*s| = (2*Real.pi)*|s| := by rw [abs_mul,abs_of_pos hPi]
    _ ≤ (2*Real.pi)*(L^C0/(2*Real.pi)) :=
      mul_le_mul_of_nonneg_left hAbs hPi.le
    _ = L^C0 := by field_simp

/-- TRUE original real bounded-frequency Ψ-Mellin OUTER integral of
all cap-free Bprime Q-frequency boxes, over ALL 20 reserved slots,
all Boolean allocations, and their actual variable-dimension cubes.
The source alpha/beta and physical signed epsilon are arbitrary here;
the only analytic input is the genuine positive per-rho Q Fourier
source estimate, not any replacement or duplicated Q gate.
The full strong measurability of rho↦Q-integral has been proved
natively using finite SOURCE Mellin polynomial, not assumed.
The true kernel L1 cost is the original fixed Schwartz Fourier mass.
This is not the unrestricted |s|>R Mellin tail. -/
theorem parity_original_actual_capfree_restricted_Psi_Mellin_fullQ_source_bound434
    (d : ℕ) (L E U V C0 T C : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0≤U) (hV : 0≤V) (hC : 0≤C)
    (band : Fin (d+1))
    (hSelected : ∀ (slot : Fin 20)
      (delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,0<e)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (signed : Bool)
    (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hQ : ∀rho:ℝ,|rho|≤L^C0 →
      (∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta xi rho K J alpha beta signed‖) ≤ C) :
    let R := L^C0/(2*Real.pi)
    ‖∫s in Set.Icc (-R) R,
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
        (∑slot : Fin 20,
          ∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → Bool,
            ∫xi in parityOriginalActualFullQFrequencyCube434 T,
              parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed)‖ ≤
      C * (∫s : ℝ,
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖) := by
  classical
  let n : Fin 20 → ℕ := fun slot =>
    (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let S : (slot : Fin 20) → Set (Fin (n slot) → ℝ) := fun slot =>
    parityOriginalActualFullQFrequencyCube434 T
  let F : ℝ → ℂ := fun rho =>
    ∑slot : Fin 20,
      ∑delta : Fin (n slot) → Bool,
        ∫xi in S slot,
          parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
            d L E band slot delta xi rho K J alpha beta signed
  have hSM : StronglyMeasurable F := by
    simpa only [F,S,n] using
      (parity_original_actual_capfree_all_slots_QBox_rho_stronglyMeasurable434
        d L E U V hL hd hU hV band hSelected K J alpha beta signed hK hJ T)
  have hSMs : AEStronglyMeasurable (fun s : ℝ => F (2*Real.pi*s)) :=
    (hSM.comp_measurable (by fun_prop : Measurable (fun s : ℝ => 2*Real.pi*s))).aestronglyMeasurable
  have hPoint (rho : ℝ) (hrho : |rho|≤L^C0) : ‖F rho‖≤C := by
    dsimp [F]
    calc
      _ ≤ ∑slot : Fin 20,
          ‖∑delta : Fin (n slot) → Bool,
            ∫xi in S slot,
              parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                d L E band slot delta xi rho K J alpha beta signed‖ :=
          norm_sum_le _ _
      _ ≤ ∑slot : Fin 20,
          ∑delta : Fin (n slot) → Bool,
            ‖∫xi in S slot,
              parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                d L E band slot delta xi rho K J alpha beta signed‖ := by
          apply Finset.sum_le_sum
          intro slot hslot
          exact norm_sum_le _ _
      _ ≤ ∑slot : Fin 20,
          ∑delta : Fin (n slot) → Bool,
            ∫xi in S slot,
              ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                d L E band slot delta xi rho K J alpha beta signed‖ := by
          apply Finset.sum_le_sum
          intro slot hslot
          apply Finset.sum_le_sum
          intro delta hdelta
          exact norm_integral_le_integral_norm _
      _ ≤ C := by simpa only [S,n] using hQ rho hrho
  have hRbound (s : ℝ)
      (hs : s∈Set.Icc (-(L^C0/(2*Real.pi))) (L^C0/(2*Real.pi))) :
      ‖F (2*Real.pi*s)‖≤C :=
    hPoint _ (parity_original_true_Psi_Mellin_cutoff_rho_power434 L C0 hL s hs)
  have hMain := parity_original_actual_Psi_Mellin_restricted_outer_L1_bound434
    L Psi hSmooth hSupport (L^C0/(2*Real.pi)) C hC
    (fun s => F (2*Real.pi*s)) hSMs hRbound
  dsimp only
  simpa only [F,S,n] using hMain
end Green64Analytic.Parity

end

end

/-! ## CapfreeSingleSlotRestrictedPsiMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1750000

/-- TRUE original one-reserved-Q-slot Parity(4.7) cap-free Bprime,
with ALL its genuine Boolean Q allocations and native full Q Fourier
cubical volume, integrated over the original real Ψ-Mellin window
|s|<=L^C0/(2π). The pointwise positive Q Fourier bound is the
ONLY quantitative input; source rho-joint-Q measurability comes from
the native physical finite polynomial, not an assumed hMeas. The
unique selected-Q phase remains INSIDE a_e(e), with no second gate.
This one-slot form is necessary for comparing to original SOURCE
pre-Cauchy per-slot approximation without invalid complex sum
cancellation. -/
theorem parity_original_actual_capfree_single_slot_restricted_Psi_Mellin_L1_bound434
    (d : ℕ) (L E U V C0 T C : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0≤U) (hV : 0≤V) (hC : 0≤C)
    (band : Fin (d+1)) (slot : Fin 20)
    (hSelected : ∀(delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,0<e)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (signed : Bool)
    (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hQ : ∀rho:ℝ, |rho|≤L^C0 →
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
            d L E band slot delta xi rho K J alpha beta signed‖) ≤ C) :
    let R := L^C0/(2*Real.pi)
    ‖∫s in Set.Icc (-R) R,
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
        (∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed)‖ ≤
      C * (∫s : ℝ,
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖) := by
  classical
  let n := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let S : Set (Fin n → ℝ) := parityOriginalActualFullQFrequencyCube434 T
  let F : ℝ → ℂ := fun rho =>
    ∑delta : Fin n → Bool,
      ∫xi in S,
        parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
          d L E band slot delta xi rho K J alpha beta signed
  have hSM : StronglyMeasurable F := by
    dsimp only [F]
    apply Finset.stronglyMeasurable_fun_sum
    intro delta hdelta
    have hJoint := parity_original_actual_capfree_Bprime_joint_rho_Q_continuous434
      d L E U V hL hd hU hV band slot delta (hSelected delta)
      K J alpha beta signed hK hJ
    exact hJoint.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure (Fin n → ℝ)).restrict S)
  have hSMs : AEStronglyMeasurable (fun s : ℝ => F (2*Real.pi*s)) :=
    (hSM.comp_measurable (by fun_prop : Measurable (fun s : ℝ => 2*Real.pi*s))).aestronglyMeasurable
  have hPoint (rho : ℝ) (hrho : |rho|≤L^C0) : ‖F rho‖≤C := by
    dsimp [F]
    calc
      _ ≤ ∑delta : Fin n → Bool,
          ‖∫xi in S,
            parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta xi rho K J alpha beta signed‖ :=
          norm_sum_le _ _
      _ ≤ ∑delta : Fin n → Bool,
          ∫xi in S,
            ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta xi rho K J alpha beta signed‖ := by
          apply Finset.sum_le_sum
          intro delta hdelta
          exact norm_integral_le_integral_norm _
      _ ≤ C := by simpa only [S,n] using hQ rho hrho
  have hRbound (s : ℝ)
      (hs : s∈Set.Icc (-(L^C0/(2*Real.pi))) (L^C0/(2*Real.pi))) :
      ‖F (2*Real.pi*s)‖≤C :=
    hPoint _ (parity_original_true_Psi_Mellin_cutoff_rho_power434 L C0 hL s hs)
  have hMain := parity_original_actual_Psi_Mellin_restricted_outer_L1_bound434
    L Psi hSmooth hSupport (L^C0/(2*Real.pi)) C hC
    (fun s => F (2*Real.pi*s)) hSMs hRbound
  dsimp only
  simpa only [F,S,n] using hMain
end Green64Analytic.Parity

end

end

/-! ## HistoricalAllSlotQMeas -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- True historical pre-Cauchy Parity(4.7) B590 source, still with
Y0=floor(2exp L), is strongly measurable in the Mellin rho parameter
AFTER integrating every original Q-frequency coordinate and summing
all Boolean Q allocations and twenty reserved slots. The proof is
actual finite-source joint rho×xi continuity plus legitimate
Bochner product integration; no arbitrary hMeas premise or new gate. -/
theorem parity_original_historical_allslots_Qbox_rho_stronglyMeasurable434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (K J : Finset ℕ)
    (alpha beta : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) :
    StronglyMeasurable (fun rho : ℝ =>
      ∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            parityOriginalHistoricalCauchyAtDelta434
              d L E band slot delta xi rho K J alpha beta signed Y) := by
  classical
  apply Finset.stronglyMeasurable_fun_sum
  intro slot hslot
  apply Finset.stronglyMeasurable_fun_sum
  intro delta hdelta
  let n := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  have hJoint := parity_original_historical_Cauchy_joint_mellin_Q_continuous434
    d L E hL hd band slot delta K J alpha beta signed Y
  exact hJoint.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Fin n → ℝ)).restrict
      (parityOriginalActualFullQFrequencyCube434 T))

/-- Consequence in the ORIGINAL inverse-Mellin variable s, with the
actual rho=2πs convention. This removes the last logical hMeas
hypothesis before estimating the high-s historical Q-box remainder. -/
theorem parity_original_historical_allslots_Qbox_s_aestronglyMeasurable434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (K J : Finset ℕ)
    (alpha beta : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) :
    AEStronglyMeasurable (fun s : ℝ =>
      ∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            parityOriginalHistoricalCauchyAtDelta434
              d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed Y) := by
  have h := parity_original_historical_allslots_Qbox_rho_stronglyMeasurable434
    d L E hL hd band K J alpha beta signed Y T
  exact (h.comp_measurable (by fun_prop : Measurable (fun s : ℝ => 2*Real.pi*s))).aestronglyMeasurable
end Green64Analytic.Parity

end

end

/-! ## HistoricalMellinQArithmeticMajorant -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- General positive-real majorant for one complex Bochner integral.
This pays NO hypothetical source cancellation: the actual real
majorant must be integrable and pointwise dominate the complex norm. -/
theorem parity_original_complex_integral_norm_le_actual_majorant434
    {X : Type} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℂ) (M : X → ℝ)
    (hFM : AEStronglyMeasurable F μ)
    (hMI : Integrable M μ)
    (hM0 : ∀ᵐ x ∂μ,0≤M x)
    (hPoint : ∀ᵐ x ∂μ,‖F x‖≤M x) :
    ‖∫x,F x ∂μ‖≤∫x,M x ∂μ := by
  have hFI : Integrable F μ := by
    apply hMI.mono hFM
    filter_upwards [hM0,hPoint] with x h0 hle
    simpa only [Real.norm_eq_abs,abs_of_nonneg h0] using hle
  calc
    _ ≤ ∫x,‖F x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫x,M x ∂μ := integral_mono_ae hFI.norm hMI hPoint

/-- TRUE original historical e/n Cauchy source at fixed physical
Mellin rho and every FULL original Q xi has positive ∑_{u=mn−2}
shifted τ(u+2) and complete B590 factorial weight bound.
This is before both Q integration and external Ψ Mellin integration;
alpha and beta are the physical coefficients with |alpha|<=A,
|beta|<=B, preserving signs, full reserved Q and e-window. -/
theorem parity_original_historical_Cauchy_pointwise_tau434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (rho A B : ℝ)
    (hA : 0≤A) (hB : 0≤B)
    (hAlpha : ∀m∈K,‖alpha m‖≤A)
    (hBeta : ∀n∈J,‖beta n‖≤B) :
    ‖parityOriginalHistoricalCauchyAtDelta434
      d L E band slot delta xi rho K J alpha beta signed Y‖ ≤
      (A*B)*(∑u∈Finset.Ioc 0 Y,
        ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
          d L E u signed band slot delta xi‖ *
          ((u+2).divisors.card:ℝ)) :=
  (parity_original_historical_Cauchy_mellin_uniform_arithmetic_mass434
    d L E hL hd band slot delta xi rho K J alpha beta signed Y).trans
    (parity_original_historical_Bprime_mellin_arithmetic_mass_le_tau434
      d L E band slot delta xi K J alpha beta signed Y A B hA hB hAlpha hBeta)
end Green64Analytic.Parity

end

end

/-! ## HistoricalMellinQPositiveLean -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 950000

/-- Genuine original fixed-rho Parity Cauchy source Bprime
integrated over one REAL original N-dimensional Q Fourier cube.
Complex norm is dominated by actual bounded alpha,beta shifted-tau
B590 source mass, no source e/P gate enlargement, no new Q gate.
All Q variables use actual original sorted Q Fourier dimensions. -/
theorem parity_original_historical_Cauchy_Qcube_rho_tau_bound_lean434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (rho T A B : ℝ)
    (hA : 0≤A) (hB : 0≤B)
    (hAlpha : ∀m∈K,‖alpha m‖≤A)
    (hBeta : ∀n∈J,‖beta n‖≤B) :
    ‖∫xi in parityOriginalActualFullQFrequencyCube434 T,
        parityOriginalHistoricalCauchyAtDelta434
          d L E band slot delta xi rho K J alpha beta signed Y‖ ≤
    (A*B) *
      (∫xi in parityOriginalActualFullQFrequencyCube434 T,
        ∑u∈Finset.Ioc 0 Y,
          ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
            d L E u signed band slot delta xi‖ *
          ((u+2).divisors.card:ℝ)) := by
  classical
  let n := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let F : (Fin n → ℝ) → ℂ := fun xi =>
    parityOriginalHistoricalCauchyAtDelta434
      d L E band slot delta xi rho K J alpha beta signed Y
  let M : (Fin n → ℝ) → ℝ := fun xi =>
    ∑u∈Finset.Ioc 0 Y,
      ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
        d L E u signed band slot delta xi‖ *
        ((u+2).divisors.card:ℝ)
  have hF : Continuous F :=
    parity_original_historical_Cauchy_Q_frequency_continuous434
      d L E hL hd band slot delta rho K J alpha beta signed Y
  have hM : Continuous M := by
    dsimp [M]
    apply continuous_finsetSum
    intro u hu
    exact (parity_original_actual_signed_window_fullQ_fibre_continuous434
      d L E u signed band slot delta).norm.mul_const _
  have hG : Continuous (fun xi : Fin n → ℝ => (A*B)*M xi) :=
    continuous_const.mul hM
  have hPoint (xi : Fin n → ℝ) : ‖F xi‖≤(A*B)*M xi := by
    have hOne := parity_original_historical_Cauchy_mellin_uniform_arithmetic_mass434
      d L E hL hd band slot delta xi rho K J alpha beta signed Y
    have hTwo := parity_original_historical_Bprime_mellin_arithmetic_mass_le_tau434
      d L E band slot delta xi K J alpha beta signed Y
      A B hA hB hAlpha hBeta
    exact hOne.trans hTwo
  have hIntegrated :=
    parity_original_continuous_Q_cube_complex_integral_majorant434
      T F (fun xi => (A*B)*M xi) hF hG hPoint
  calc
    _ ≤ ∫xi in parityOriginalActualFullQFrequencyCube434 T,
      (A*B)*M xi := hIntegrated
    _ = (A*B)*(∫xi in parityOriginalActualFullQFrequencyCube434 T,M xi) :=
      integral_const_mul _ _
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## HistoricalMellinScaledQContinuous -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The real original 2πs Mellin parameter change on a product of
one real spectral variable and the native N-dimensional Q cube is
jointly continuous, without unfolding the actual Parity coefficients. -/
theorem parity_original_mellin_scale_product_continuous434
    {n : ℕ} (F : ℝ × (Fin n → ℝ) → ℂ)
    (hF : Continuous F) :
    Continuous (fun p : ℝ × (Fin n → ℝ) => F (2*Real.pi*p.1,p.2)) := by
  have hScalar : Continuous (fun p : ℝ × (Fin n → ℝ) =>
      2*Real.pi*p.1) := continuous_const.mul continuous_fst
  have hMap : Continuous (fun p : ℝ × (Fin n → ℝ) =>
      (2*Real.pi*p.1,p.2)) := hScalar.prodMk continuous_snd
  exact hF.comp hMap

/-- Literal original fixed-Q-allocation e/n historical Cauchy
amplitude evaluated at rho=2πs, jointly continuous in all (s,xi)
from the already native joint source Mellin/Q theorem. The helper
factorizes composition BEFORE Lean unfolds the massive source tensor. -/
theorem parity_original_historical_Cauchy_single_joint_s_Q_continuous434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    Continuous (fun p : ℝ × (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
        parityOriginalHistoricalCauchyAtDelta434
          d L E band slot delta p.2 (2*Real.pi*p.1) K J alpha beta signed Y) := by
  let n := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let F : ℝ × (Fin n → ℝ) → ℂ := fun p =>
    parityOriginalHistoricalCauchyAtDelta434
      d L E band slot delta p.2 p.1 K J alpha beta signed Y
  have hF : Continuous F :=
    parity_original_historical_Cauchy_joint_mellin_Q_continuous434
      d L E hL hd band slot delta K J alpha beta signed Y
  have hScaled := parity_original_mellin_scale_product_continuous434 F hF
  change Continuous (fun p : ℝ × (Fin n → ℝ) => F (2*Real.pi*p.1,p.2))
  exact hScaled
end Green64Analytic.Parity

end

end

/-! ## HistoricalSingleSlotHighMellinTau -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1700000

/-- ORIGINAL h=-2 historical Parity(4.7) reserved-Q **ONE SLOT**
complex high-|s| Ψ-Mellin tail, with ALL its Boolean allocations and
real Q frequency integration, bounded by the genuine one-slot
positive B590 τ(u+2) arithmetic mass times R^-H Ψ-Schwartz moment.
Unlike the all-slot complex sum, this can be compared directly with
the original per-slot pre-Cauchy source approximation. No false
complex-subsum norm monotonicity, no Y0=Ybox at fixed s, no new
e/P gate. Actual integrability in Mellin follows from native joint
source rho/Q continuity and compact Q cube. -/
theorem parity_original_historical_single_slot_high_Psi_Mellin_Q_tau_bound434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hAlpha : ∀m∈K,‖alpha m‖≤A)
    (hBeta : ∀n∈J,‖beta n‖≤B)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (R : ℝ) (hR : 0<R) (H : ℕ) (T : ℝ) :
    ‖∫s in {s : ℝ | R≤‖s‖},
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalCauchyAtDelta434
            d L E band slot delta xi (2*Real.pi*s)
            K J alpha beta signed Y)‖ ≤
      ((A*B)*(∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          ∑u∈Finset.Ioc 0 Y,
            ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
              d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ))) *
       ((R^H)⁻¹ *
        (∫s : ℝ, ‖s‖^H *
          ‖(𝓕 (parityOriginalLogCutoff434
            (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖)) := by
  classical
  let n := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let M : ℝ := ∑delta : Fin n → Bool,
    ∫xi in parityOriginalActualFullQFrequencyCube434 T,
      ∑u∈Finset.Ioc 0 Y,
        ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
          d L E u signed band slot delta xi‖ *
          ((u+2).divisors.card:ℝ)
  let C : ℝ := (A*B)*M
  let F : ℝ → ℂ := fun s => ∑delta : Fin n → Bool,
    ∫xi in parityOriginalActualFullQFrequencyCube434 T,
      parityOriginalHistoricalCauchyAtDelta434
        d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed Y
  have hM : 0≤M := by
    dsimp [M]
    apply Finset.sum_nonneg
    intro delta hdelta
    apply integral_nonneg
    intro xi
    apply Finset.sum_nonneg
    intro u hu
    positivity
  have hC : 0≤C := mul_nonneg (mul_nonneg hA hB) hM
  have hMeasRho : StronglyMeasurable (fun rho : ℝ =>
      ∑delta : Fin n → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalCauchyAtDelta434
            d L E band slot delta xi rho K J alpha beta signed Y) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro delta hdelta
    have hJoint := parity_original_historical_Cauchy_joint_mellin_Q_continuous434
      d L E hL hd band slot delta K J alpha beta signed Y
    exact hJoint.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure (Fin n → ℝ)).restrict
        (parityOriginalActualFullQFrequencyCube434 T))
  have hMeas : AEStronglyMeasurable F :=
    (hMeasRho.comp_measurable
      (by fun_prop : Measurable (fun s : ℝ => 2*Real.pi*s))).aestronglyMeasurable
  have hBound (s : ℝ) : ‖F s‖≤C := by
    have hOne (delta : Fin n → Bool) :
        ‖∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalCauchyAtDelta434
            d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed Y‖ ≤
        (A*B) * (∫xi in parityOriginalActualFullQFrequencyCube434 T,
          ∑u∈Finset.Ioc 0 Y,
            ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
              d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) :=
      parity_original_historical_Cauchy_Qcube_rho_tau_bound_lean434
        d L E hL hd band slot delta K J alpha beta signed Y
        (2*Real.pi*s) T A B hA hB hAlpha hBeta
    change ‖∑delta : Fin n → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 T,
        parityOriginalHistoricalCauchyAtDelta434
          d L E band slot delta xi (2*Real.pi*s)
            K J alpha beta signed Y‖≤(A*B)*M
    calc
      _ ≤ ∑delta : Fin n → Bool,
        ‖∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalCauchyAtDelta434
            d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed Y‖ := norm_sum_le _ _
      _ ≤ ∑delta : Fin n → Bool, (A*B)*
          (∫xi in parityOriginalActualFullQFrequencyCube434 T,
            ∑u∈Finset.Ioc 0 Y,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                d L E u signed band slot delta xi‖ *
                ((u+2).divisors.card:ℝ)) := by
          apply Finset.sum_le_sum
          intro delta hdelta
          exact hOne delta
      _ = (A*B)*M := by dsimp [M]; rw [Finset.mul_sum]
  have hMain := parity_original_true_Psi_Mellin_high_outer_L1_bound434
    L Psi hSmooth hSupport R hR H C hC F hMeas hBound
  simpa only [F,C,M] using hMain
end Green64Analytic.Parity

end

end

/-! ## PsiMellinQJointShort -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Exact original historical finite Boolean Q-allocation sum is
jointly continuous in the real inverse-Mellin s and original N-dimensional
Q Fourier xi. This uses actual source one-allocation continuity
at rho=2πs, no inlining or loss of selected/skipped Q prime tuples. -/
theorem parity_original_historical_allocation_joint_s_Q_short434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    Continuous (fun p : ℝ × (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
      ∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        parityOriginalHistoricalCauchyAtDelta434
          d L E band slot delta p.2 (2*Real.pi*p.1)
          K J alpha beta signed Y) := by
  classical
  apply continuous_finsetSum
  intro delta hdelta
  exact parity_original_historical_Cauchy_single_joint_s_Q_continuous434
    d L E hL hd band slot delta K J alpha beta signed Y

/-- True original log-Psi Mellin kernel is continuous in the real s
at its literal 2πs logarithmic Fourier normalization. -/
theorem parity_original_true_Psi_Mellin_kernel_s_continuous_short434
    (L : ℝ) (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    Continuous (parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport) := by
  let f := (𝓕 (parityOriginalLogCutoff434
    (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ))
  have hPhase : Continuous (fun s : ℝ =>
    Complex.exp (((-2*Real.pi*s*Real.log (Real.exp L):ℝ):ℂ)*Complex.I)) := by
    fun_prop
  change Continuous (fun s : ℝ => f s *
    Complex.exp (((-2*Real.pi*s*Real.log (Real.exp L):ℝ):ℂ)*Complex.I))
  exact f.continuous.mul hPhase

/-- Literal original Parity(4.7) source integrand, the REAL Ψ-Mellin
kernel times the complete historical 2^N allocation sum of e/n
Bprime amplitudes, is JOINTLY continuous on (s,xi). Does NOT
introduce a duplicated Fourier gate or a fake pointwise s cutoff.
This is the native proof of compact source Fubini integrability. -/
theorem parity_original_historical_Psi_Mellin_allocation_joint_short434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    Continuous (fun p : ℝ × (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport p.1 *
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        parityOriginalHistoricalCauchyAtDelta434
          d L E band slot delta p.2 (2*Real.pi*p.1)
          K J alpha beta signed Y)) :=
  ((parity_original_true_Psi_Mellin_kernel_s_continuous_short434
      L Psi hSmooth hSupport).comp continuous_fst).mul
    (parity_original_historical_allocation_joint_s_Q_short434
      d L E hL hd band slot K J alpha beta signed Y)
end Green64Analytic.Parity

end

end

/-! ## HistoricalSingleSlotFullMellinFubini -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2100000

/-- The COMPLETE original signed historical Parity(4.7) source at ONE
reserved Q slot has lawful FULL REAL Ψ-Mellin↔N-dimensional Q Fourier
Fubini. This is noncompact in s; the source kernel is Schwartz and
the actual Q-positive B590 shifted τ(u+2) sum is an integrable
uniform majorant independent of s. No false compactification,
no exchange between complex different reserved slots, no new
selected-Q gate or fictitious Y0/Ybox pointwise identity.
This theorem keeps the genuine Y cutoff and exact 2πs Mellin phase. -/
theorem parity_original_historical_single_slot_full_Psi_Mellin_Q_Fubini434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (T : ℝ)
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hAlpha : ∀m∈K,‖alpha m‖≤A)
    (hBeta : ∀n∈J,‖beta n‖≤B)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    (∫xi in parityOriginalActualFullQFrequencyCube434 T,
      ∫s : ℝ,
        parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
          (∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → Bool,
            parityOriginalHistoricalCauchyAtDelta434
              d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed Y)) =
    (∫s : ℝ,
      ∫xi in parityOriginalActualFullQFrequencyCube434 T,
        parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
          (∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → Bool,
            parityOriginalHistoricalCauchyAtDelta434
              d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed Y)) := by
  classical
  let n := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let Kpsi : ℝ → ℂ := parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport
  let M : (Fin n → ℝ) → ℝ := fun xi =>
    (A*B)*(∑delta : Fin n → Bool,
      ∑u∈Finset.Ioc 0 Y,
        ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
          d L E u signed band slot delta xi‖ *
          ((u+2).divisors.card:ℝ))
  let F : ℝ → (Fin n → ℝ) → ℂ := fun s xi =>
    Kpsi s * (∑delta : Fin n → Bool,
      parityOriginalHistoricalCauchyAtDelta434
        d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed Y)
  have hKInt : Integrable Kpsi := parity_original_true_Psi_Mellin_kernel_integrable434
    L Psi hSmooth hSupport
  have hMCont : Continuous M := by
    dsimp [M]
    apply Continuous.mul continuous_const
    apply continuous_finsetSum
    intro delta hdelta
    apply continuous_finsetSum
    intro u hu
    exact (parity_original_actual_signed_window_fullQ_fibre_continuous434
      d L E u signed band slot delta).norm.mul_const _
  have hMInt : IntegrableOn M (parityOriginalActualFullQFrequencyCube434 T) :=
    hMCont.continuousOn.integrableOn_compact
      (parity_original_true_full_Q_frequency_cube_compact434 T)
  have hMnonneg (xi : Fin n → ℝ) : 0≤M xi := by
    dsimp [M]
    apply mul_nonneg (mul_nonneg hA hB)
    apply Finset.sum_nonneg
    intro delta hdelta
    apply Finset.sum_nonneg
    intro u hu
    positivity
  have hFCont : Continuous (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2) :=
    parity_original_historical_Psi_Mellin_allocation_joint_short434
      d L E hL hd band slot Psi hSmooth hSupport K J alpha beta signed Y
  have hPoint (s : ℝ) (xi : Fin n → ℝ) :
      ‖F s xi‖≤‖Kpsi s‖*M xi := by
    have hSingle (delta : Fin n → Bool) :=
      parity_original_historical_Cauchy_pointwise_tau434
        d L E hL hd band slot delta xi K J alpha beta signed Y
        (2*Real.pi*s) A B hA hB hAlpha hBeta
    have hBound :
        ‖∑delta : Fin n → Bool,
            parityOriginalHistoricalCauchyAtDelta434
              d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed Y‖ ≤ M xi := by
      calc
        _ ≤ ∑delta : Fin n → Bool,
          ‖parityOriginalHistoricalCauchyAtDelta434
              d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed Y‖ := norm_sum_le _ _
        _ ≤ ∑delta : Fin n → Bool,(A*B)*
            (∑u∈Finset.Ioc 0 Y,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                d L E u signed band slot delta xi‖ *
                ((u+2).divisors.card:ℝ)) := by
              apply Finset.sum_le_sum
              intro delta hdelta
              exact hSingle delta
        _ = M xi := by dsimp [M]; rw [Finset.mul_sum]
    change ‖Kpsi s * (∑delta : Fin n → Bool,
      parityOriginalHistoricalCauchyAtDelta434
        d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed Y)‖ ≤
        ‖Kpsi s‖*M xi
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hBound (norm_nonneg (Kpsi s))
  have hSwap := parity_original_true_high_Mellin_Q_Fubini_dominated434
    (0:ℝ) T Kpsi M F hKInt hMInt hMnonneg hFCont hPoint
  have hAll : ({s : ℝ | (0:ℝ)≤‖s‖}) = Set.univ := by
    ext s
    simp
  rw [hAll] at hSwap
  simp only [setIntegral_univ] at hSwap
  simpa only [F,Kpsi,M,n] using hSwap
end Green64Analytic.Parity

end

end

/-! ## SignedFullQW1GatePointwise -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- The real original B590 Fourier gate's complete N-dimensional
complex modulus is independent of its labelled Q prime tuple:
all original arithmetic source Fourier phases have complex modulus 1.
This is an identity, not an L1 averaging assumption. -/
theorem parity_original_actual_B590_fullQ_gate_norm_eq_common434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ)
    (delta : Fin N → Bool) (p : Fin N → ℕ)
    (xi : Fin N → ℝ) :
    ‖parityOriginalB590AllGateFourierIntegrand434 E s delta p xi‖ =
      ∏ i : Fin N,
        ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (xi i)‖ := by
  unfold parityOriginalB590AllGateFourierIntegrand434
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]

/-- The original complete r20 factorial/W1 labelled source and
true signed epsilon have modulus bounded by ONE source W1(P,u)
times ONE genuine f0/f1 B590 Fourier gate product, at each xi and
every selected-e historical window. No multiplication by another
Q-gate or source 20! cardinal, no P-free or odd e restriction.
This is the essential physical bound for a polylog Mellin tail. -/
theorem parity_original_actual_signed_fullQ_window_fibre_norm_le_W1_gate434
    (d : ℕ) (L E : ℝ) (hL : 0<L) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
      d L E u signed band slot delta xi‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        (∏i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length,
          ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (xi i)‖) := by
  classical
  let N := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let Q : ℝ := ∏i : Fin N,
      ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (xi i)‖
  let S : Type := ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
  let w : S → ℝ := fun f =>
      parityActualOriginalSignedFullTupleWeight434 d L u signed f
  let G : S → ℂ := fun f =>
      parityOriginalB590AllGateFourierIntegrand434 E
        (sourceActualSortedFrequencyScales 20 d L band slot)
        delta (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) xi
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hG (f : S) : ‖G f‖=Q := by
    simpa only [G,Q] using
      parity_original_actual_B590_fullQ_gate_norm_eq_common434 E
        (sourceActualSortedFrequencyScales 20 d L band slot)
        delta (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) xi
  have hOne (f : S) :
      ‖(if parityOriginalHistoricalEWindow434 L E
            (paritySourceOrderedAllocatedE434 delta
              (parityActualSourceRemainingFullQTuple434 d L band slot f))
        then ((w f:ℝ):ℂ)*G f else 0)‖ ≤ |w f| * Q := by
    split_ifs with he
    · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,hG]
    · have hh : 0≤|w f| * Q := mul_nonneg (abs_nonneg _) hQ
      simpa using hh
  have hMass : (∑f:S,|w f|) ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
    exact parity_original_signed_full_Q_total_variation_le_W1434 d L hL u signed
  unfold parityOriginalSignedFullQWindowAllGateFourierAtU434
  calc
    _ ≤ ∑f:S,‖(if parityOriginalHistoricalEWindow434 L E
            (paritySourceOrderedAllocatedE434 delta
              (parityActualSourceRemainingFullQTuple434 d L band slot f))
        then ((w f:ℝ):ℂ)*G f else 0)‖ := norm_sum_le _ _
    _ ≤ ∑f:S,|w f| * Q := by
      apply Finset.sum_le_sum
      intro f hf
      exact hOne f
    _ = (∑f:S,|w f|)*Q := by rw [Finset.sum_mul]
    _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u * Q :=
      mul_le_mul_of_nonneg_right hMass hQ
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## SignedFullQWTauSeparation -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- The genuine original signed 20! Q-labelled historical B590
arithmetic τ(u+2) weight separates WITHOUT paying another Q gate:

  Σ_{1≤u≤Y} |B590_src(u,δ,ξ)| τ(u+2)
   ≤ [Σ_{1≤u≤Y} W1(P,u) τ(u+2)] × ∏_i |F(f_{δi})(ξ_i)|.

This holds at ANY original finite Y, signed ε=1 or ε=E, and
historical selected e window. Source original QSkip factorials
are already inside the W1 mass. -/
theorem parity_original_signed_fullQ_tau_source_separates_W1_gate434
    (d : ℕ) (L E : ℝ) (hL : 0<L) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Y : ℕ) :
    (∑u∈Finset.Ioc 0 Y,
      ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
        d L E u signed band slot delta xi‖ *
        ((u+2).divisors.card:ℝ)) ≤
    (∑u∈Finset.Ioc 0 Y,
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        ((u+2).divisors.card:ℝ)) *
      (∏i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length,
          ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (xi i)‖) := by
  let Q : ℝ := ∏i : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length,
      ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (xi i)‖
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hOne (u : ℕ) :
      ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
        d L E u signed band slot delta xi‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u * Q :=
    parity_original_actual_signed_fullQ_window_fibre_norm_le_W1_gate434
      d L E hL u signed band slot delta xi
  calc
    _ ≤ ∑u∈Finset.Ioc 0 Y,
        (sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u * Q) *
          ((u+2).divisors.card:ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_right (hOne u) (Nat.cast_nonneg _)
    _ = (∑u∈Finset.Ioc 0 Y,
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        ((u+2).divisors.card:ℝ)) * Q := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ = _ := rfl

/-- At EXACT historic Parity Ψ source Y0=floor(2exp L), the arithmetic
weighted shifted-divisor factor is already bounded by real source
W1 τ polylog mass. Thus for both signed original source branches the
entire 20!-label Q-labelled τ B590 source mass has explicit bound
`x L^(C_W1+16) * common Fourier gate`, with no factorial/Q count.
This DOES NOT extend to capfree Ybox pointwise in Mellin s; there the
old Y0≠Ybox until complete Ψ inversion. -/
theorem parity_eventually_original_signed_fullQ_tau_Y0_polylog_gate434 :
    ∀ᶠ L : ℝ in atTop, 0<L ∧
      ∀ (d : ℕ) (E : ℝ) (signed : Bool)
        (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (xi : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ),
      (∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
        ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
          d L E u signed band slot delta xi‖ *
        ((u+2).divisors.card:ℝ)) ≤
      (Real.exp L * L^parityOriginalW1PolylogExponent434 * L^16) *
        (∏i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length,
          ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (xi i)‖) := by
  filter_upwards [parity_eventually_original_W1_shifted_tau_total_mass_polylog434,
    eventually_gt_atTop (0:ℝ)] with L hTau hL
  refine ⟨hL,?_⟩
  intro d E signed band slot delta xi
  let Q : ℝ := ∏i : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length,
      ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (xi i)‖
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hSum := parity_original_signed_fullQ_tau_source_separates_W1_gate434
    d L E hL signed band slot delta xi ⌊2*Real.exp L⌋₊
  calc
    _ ≤ (∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        ((u+2).divisors.card:ℝ)) * Q := hSum
    _ ≤ (Real.exp L * L^parityOriginalW1PolylogExponent434 * L^16) * Q :=
      mul_le_mul_of_nonneg_right hTau hQ
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## SignedWTauQCubeIntegrated -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- TRUE SOURCE fixed-δ ORIGINAL shifted τ B590 Q Fourier mass,
in the actual physical cube, bounded by ONE original arithmetic
W1(P,u)τ(u+2) scalar times the FULL ℝ^N Fourier variation of
ONE common source Q gate. No second selected-Q prime phase,
no Q factorial multiplicity, no unjustified signed subsum norm.
Q-integrability is proved from literal finite-source continuity
on a compact cube, not stipulated. -/
theorem parity_original_signed_fullQ_tau_Qcube_integral_le_W1_L1434
    (d : ℕ) (L E T : ℝ) (hL : 0<L) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) :
    (∫xi in parityOriginalActualFullQFrequencyCube434 T,
      ∑u∈Finset.Ioc 0 Y,
        ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
          d L E u signed band slot delta xi‖ *
        ((u+2).divisors.card:ℝ)) ≤
    (∑u∈Finset.Ioc 0 Y,
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        ((u+2).divisors.card:ℝ)) *
      (∫xi : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ,
        ‖parityOriginalActualPostCauchyQGate434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) xi delta‖) := by
  let n := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let S : Set (Fin n → ℝ) := parityOriginalActualFullQFrequencyCube434 T
  let G : (Fin n → ℝ) → ℂ := fun xi =>
    parityOriginalActualPostCauchyQGate434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) xi delta
  let M : (Fin n → ℝ) → ℝ := fun xi =>
    ∑u∈Finset.Ioc 0 Y,
      ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
        d L E u signed band slot delta xi‖ *
      ((u+2).divisors.card:ℝ)
  let W : ℝ := ∑u∈Finset.Ioc 0 Y,
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        ((u+2).divisors.card:ℝ)
  have hW : 0≤W := by
    dsimp [W]
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (source_original_W1_nonneg _ _) (Nat.cast_nonneg _)
  have hMcont : Continuous M := by
    dsimp [M]
    apply continuous_finsetSum
    intro u hu
    exact (parity_original_actual_signed_window_fullQ_fibre_continuous434
      d L E u signed band slot delta).norm.mul_const _
  have hMInt : IntegrableOn M S :=
    hMcont.continuousOn.integrableOn_compact
      (parity_original_true_full_Q_frequency_cube_compact434 T)
  have hGInt : Integrable (fun xi : Fin n → ℝ => ‖G xi‖) :=
    (parity_original_actual_post_cauchy_Q_gate_integrable434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) delta).norm
  have hPoint (xi : Fin n → ℝ) : M xi≤W*‖G xi‖ := by
    have h := parity_original_signed_fullQ_tau_source_separates_W1_gate434
      d L E hL signed band slot delta xi Y
    rw [parity_original_actual_post_cauchy_Q_gate_norm434 E
      (sourceActualSortedFrequencyScales 20 d L band slot)]
    exact h
  calc
    (∫xi in S,M xi) ≤ ∫xi in S,W*‖G xi‖ :=
      integral_mono hMInt ((hGInt.const_mul W).integrableOn) (fun xi => hPoint xi)
    _ = W*(∫xi in S,‖G xi‖) := integral_const_mul _ _
    _ ≤ W*(∫xi : Fin n → ℝ,‖G xi‖) :=
      mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hGInt (Filter.Eventually.of_forall
          (fun xi => norm_nonneg (G xi)))) hW
end Green64Analytic.Parity

end

end

/-! ## SignedWTauAllQSlots -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2800000

/-- Original shifted τ(Y0=u+2) arithmetic mass across ALL 2^N
B590 allocation branches and ALL 20 reserved slots of a fixed
original Q band. Each source labelled Q prime tuple and reserved
prime is ALREADY present in W1(P,u); no multiplicity factor besides
the literal 20 outer slots. The true Q gate Fourier variation is
integrated once over ℝ^N, not pointwise bounded by a fictitious
Schwartz constant. This is the quantitative high-Mellin-tail
source mass the earlier native Ψ checkpoint left open. -/
theorem parity_eventually_original_signed_fullQ_tau_all_slots_integrated_polylog434 :
    ∀ᶠ L : ℝ in atTop, 0<L ∧
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)),
      (∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 L,
            ∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                (sourceOriginalLiteralDepth 20 L) L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) ≤
        20*Real.exp L*L^parityOriginalW1PolylogExponent434*L^16*
          L^parityOriginalB590FixedFourierPolynomialExponent434 := by
  filter_upwards [parity_eventually_original_W1_shifted_tau_total_mass_polylog434,
    parity_eventually_original_actual_post_cauchy_Q_gate_L1_polylog434,
    eventually_gt_atTop (0:ℝ)] with L hTau hGate hL
  refine ⟨hL,?_⟩
  intro E signed band
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let Mass := ∑u∈Finset.Ioc 0 Y,
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      ((u+2).divisors.card:ℝ)
  let B := Real.exp L*L^parityOriginalW1PolylogExponent434*L^16
  let C := L^parityOriginalB590FixedFourierPolynomialExponent434
  have hMass : 0≤Mass := by
    dsimp [Mass]
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (source_original_W1_nonneg _ _) (Nat.cast_nonneg _)
  have hMassB : Mass≤B := hTau
  have hB : 0≤B := by dsimp [B]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have hSlot (slot : Fin 20) :
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 L,
            ∑u∈Finset.Ioc 0 Y,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) ≤ B*C := by
    let n := (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length
    have hOne (delta : Fin n → Bool) :
        (∫xi in parityOriginalActualFullQFrequencyCube434 L,
            ∑u∈Finset.Ioc 0 Y,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) ≤
        Mass*(∫xi : Fin n → ℝ,
          ‖parityOriginalActualPostCauchyQGate434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) xi delta‖) :=
      parity_original_signed_fullQ_tau_Qcube_integral_le_W1_L1434
        d L E L hL signed band slot delta Y
    have hGateOne := hGate band slot E
    dsimp only at hGateOne
    calc
      _ ≤ ∑delta : Fin n → Bool,
        Mass*(∫xi : Fin n → ℝ,
          ‖parityOriginalActualPostCauchyQGate434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) xi delta‖) := by
          apply Finset.sum_le_sum
          intro delta hdelta
          exact hOne delta
      _ = Mass*(∑delta : Fin n → Bool,
          ∫xi : Fin n → ℝ,
            ‖parityOriginalActualPostCauchyQGate434 E
              (sourceActualSortedFrequencyScales 20 d L band slot) xi delta‖) := by
          rw [Finset.mul_sum]
      _ ≤ Mass*C := mul_le_mul_of_nonneg_left hGateOne hMass
      _ ≤ B*C := mul_le_mul_of_nonneg_right hMassB hC
  have hAll :
      (∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 L,
            ∑u∈Finset.Ioc 0 Y,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) ≤ 20*(B*C) := by
    calc
      _ ≤ ∑_slot : Fin 20, B*C := by
        apply Finset.sum_le_sum
        intro slot hslot
        exact hSlot slot
      _ = 20*(B*C) := by simp
  calc
    _ ≤ 20*(B*C) := by simpa only [d,Y] using hAll
    _ = 20*Real.exp L*L^parityOriginalW1PolylogExponent434*L^16*
        L^parityOriginalB590FixedFourierPolynomialExponent434 := by
          dsimp [B,C]
          ring
end Green64Analytic.Parity

end

end

/-! ## HistoricalAllSlotQPositiveTau -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- True original pre-Cauchy historical Parity(4.7) source after taking
all original complex Q-cube integrals, EVERY Boolean Q allocation
and all twenty reserved slots. At each real Mellin rho its norm is
bounded by the actual positive full-Q weighted W1,τ(u+2) mass with
factor ||alpha||∞||beta||∞. This is obtained from the fully verified
fixed-Q-cube 4.7 source bound via COMPLEX norm triangle before any
majorization, not a false complex signed-subsum monotonicity.
The historical u cutoff Y and exact source 2π convention are retained. -/
theorem parity_original_historical_allslots_Qbox_rho_tau_positive434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (K J : Finset ℕ)
    (alpha beta : ℕ → ℂ) (signed : Bool) (Y : ℕ)
    (T A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hAlpha : ∀m∈K,‖alpha m‖≤A)
    (hBeta : ∀n∈J,‖beta n‖≤B)
    (rho : ℝ) :
    ‖∑slot : Fin 20,
      ∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            parityOriginalHistoricalCauchyAtDelta434
              d L E band slot delta xi rho K J alpha beta signed Y‖ ≤
      (A*B)*(∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            ∑u∈Finset.Ioc 0 Y,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) := by
  classical
  let n : Fin 20 → ℕ := fun slot =>
    (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let H : (slot : Fin 20) → (Fin (n slot) → Bool) → ℂ := fun slot delta =>
    ∫xi in parityOriginalActualFullQFrequencyCube434 T,
      parityOriginalHistoricalCauchyAtDelta434
        d L E band slot delta xi rho K J alpha beta signed Y
  let M : (slot : Fin 20) → (Fin (n slot) → Bool) → ℝ := fun slot delta =>
    ∫xi in parityOriginalActualFullQFrequencyCube434 T,
      ∑u∈Finset.Ioc 0 Y,
        ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
          d L E u signed band slot delta xi‖ *
        ((u+2).divisors.card:ℝ)
  have hBound (slot : Fin 20) (delta : Fin (n slot) → Bool) :
      ‖H slot delta‖ ≤ (A*B)*M slot delta :=
    parity_original_historical_Cauchy_Qcube_rho_tau_bound_lean434
      d L E hL hd band slot delta K J alpha beta signed Y
      rho T A B hA hB hAlpha hBeta
  have hSlot (slot : Fin 20) :
      ‖∑delta : Fin (n slot) → Bool,H slot delta‖ ≤
        (A*B)*(∑delta : Fin (n slot) → Bool,M slot delta) := by
    calc
      _ ≤ ∑delta : Fin (n slot) → Bool, ‖H slot delta‖ := norm_sum_le _ _
      _ ≤ ∑delta : Fin (n slot) → Bool, (A*B)*M slot delta := by
        apply Finset.sum_le_sum
        intro delta hdelta
        exact hBound slot delta
      _ = (A*B)*(∑delta : Fin (n slot) → Bool,M slot delta) :=
        by rw [Finset.mul_sum]
  have hOuter :
      ‖∑slot : Fin 20,∑delta : Fin (n slot) → Bool,H slot delta‖ ≤
        (A*B)*(∑slot : Fin 20,∑delta : Fin (n slot) → Bool,M slot delta) := by
    calc
      _ ≤ ∑slot : Fin 20,‖∑delta : Fin (n slot) → Bool,H slot delta‖ :=
        norm_sum_le _ _
      _ ≤ ∑slot : Fin 20,(A*B)*(∑delta : Fin (n slot) → Bool,M slot delta) := by
        apply Finset.sum_le_sum
        intro slot hslot
        exact hSlot slot
      _ = (A*B)*(∑slot : Fin 20,∑delta : Fin (n slot) → Bool,M slot delta) :=
        by rw [Finset.mul_sum]
  simpa only [H,M,n] using hOuter
end Green64Analytic.Parity

end

end

/-! ## HistoricalAllSlotTrueHighMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1300000

/-- TRUE original Parity(4.7) unrestricted high-Ψ-Mellin tail of the
complex Q Fourier integral, over every original reserved Q slot,
all Boolean allocations and the FULL original real N-dimensional
Q frequency cube. This is a genuine analytical inequality, not a
conditional `hMeas` interface: strong measurability of the whole
historic Q-integrated source in s is proved from its 2πs finite
polynomial, Q-integrated complex norm is paid by the exact positive
shifted-divisor τ(u+2) mass, and Mellin kernel by the original
R^-H Ψ-Schwartz moment. No enlargement Y0→Ybox before Mellin
inversion; actual historical finite source Y is retained. -/
theorem parity_original_historical_allslots_high_Psi_Mellin_Q_tau_bound434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (K J : Finset ℕ)
    (alpha beta : ℕ → ℂ) (signed : Bool) (Y : ℕ)
    (T A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hAlpha : ∀m∈K,‖alpha m‖≤A)
    (hBeta : ∀n∈J,‖beta n‖≤B)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (R : ℝ) (hR : 0<R) (H : ℕ) :
    ‖∫s in {s : ℝ | R≤‖s‖},
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
      (∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            parityOriginalHistoricalCauchyAtDelta434
              d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed Y)‖ ≤
    ((A*B)*(∑slot : Fin 20,
      ∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          ∑u∈Finset.Ioc 0 Y,
            ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
              d L E u signed band slot delta xi‖ *
            ((u+2).divisors.card:ℝ))) *
      ((R^H)⁻¹ *
        (∫s : ℝ,‖s‖^H *
          ‖(𝓕 (parityOriginalLogCutoff434
            (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖)) := by
  classical
  let D : ℝ := ∑slot : Fin 20,
    ∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 T,
        ∑u∈Finset.Ioc 0 Y,
          ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
            d L E u signed band slot delta xi‖ *
          ((u+2).divisors.card:ℝ)
  let C : ℝ := (A*B)*D
  let F : ℝ → ℂ := fun s => ∑slot : Fin 20,
    ∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 T,
        parityOriginalHistoricalCauchyAtDelta434
          d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed Y
  have hD : 0≤D := by
    dsimp [D]
    apply Finset.sum_nonneg
    intro slot hslot
    apply Finset.sum_nonneg
    intro delta hdelta
    apply integral_nonneg
    intro xi
    apply Finset.sum_nonneg
    intro u hu
    positivity
  have hC : 0≤C := mul_nonneg (mul_nonneg hA hB) hD
  have hSM : AEStronglyMeasurable F :=
    parity_original_historical_allslots_Qbox_s_aestronglyMeasurable434
      d L E hL hd band K J alpha beta signed Y T
  have hBound (s : ℝ) : ‖F s‖≤C := by
    have h := parity_original_historical_allslots_Qbox_rho_tau_positive434
      d L E hL hd band K J alpha beta signed Y T A B hA hB
      hAlpha hBeta (2*Real.pi*s)
    simpa only [F,C,D] using h
  have hMain := parity_original_true_Psi_Mellin_high_outer_L1_bound434
    L Psi hSmooth hSupport R hR H C hC F hSM hBound
  simpa only [F,C,D] using hMain
end Green64Analytic.Parity

end

end

/-! ## SourceToCapfreePsiMellinAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Original signed Parity(4.2) 20!-labelled pre-Cauchy source with
its ORIGINAL smooth Psi(u/exp L) is O_A(x L^-A)-close to the REAL,
cap-free natural a_v(u/e) Bprime, integrated over the complete
one-dimensional 2*pi Mellin and ORIGINAL N-dimensional Q-frequency
box, with the same selected e and its B509 H0/Q/P/factorial weights.
This result uses the exact Mellin-integrated extension from the old
u<=floor(2x) to the true Ybox=ceil(6UV); no false pointwise-in-s
vanishing, no extra Q gate, and no P-free gate on post-Cauchy e.
The original source constraints on E and source K/J are stated
explicitly; this does not assert full TypeII(4.2) until the
outer Ψ-Mellin and all signed branches are bounded. -/
theorem parity_eventually_original_signed_source_to_actual_capfree_Psi_Mellin_Bprime_all_log434
    (betaP A : ℝ) (hbetaP : 0<betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E U V : ℝ), 1≤E → E≤Real.exp ((1-betaP)*L) →
        0≤U → 0≤V → Real.exp L≤U*V →
      ∀ (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
        (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ))),
        (∀t,0≤Psi t) → (∀t,Psi t≤1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0≤Acoef → 0≤Bcoef →
        (∀m∈K, ‖alpha m‖≤Acoef) → (∀n∈J, ‖beta n‖≤Bcoef) →
        (∀m∈K,(m:ℝ)≤2*U) → (∀n∈J,(n:ℝ)≤3*V) →
      ∀ (signed : Bool),
      ‖parityOriginalShiftTwoSignedBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J alpha beta signed 0
          ⌊2*Real.exp L⌋₊ -
        parityOriginalActualPsiMellinCapfreeBprimeQBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi hSmooth (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
          K J alpha beta signed L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_source_to_historical_Psi_Mellin_Cauchy_QBox_all_log434
    betaP A hbetaP jQ hBand,
    parity_eventually_original_cartesian_selected_e_odd_unit434] with L hOld hOdd
  refine ⟨hOld.1,hOld.2.1,?_⟩
  intro band hb E U V hE hEhi hU hV hUV Psi hSupport hSmooth
    hPsiPos hPsiLe slot K J alpha beta Acoef Bcoef hAcoef hBcoef
    hAlpha hBeta hK hJ signed
  have hSelected :
      ∀ (δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ,0<e := by
    intro δ e he
    have he0 : e∈parityOriginalReservedCartesianESupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ :=
      (Finset.mem_filter.mp he).1
    exact (hOdd.2 band slot δ e he0).2.1
  have hL : 0<L := by nlinarith [hOld.1]
  have hEq := parity_original_actual_historical_Psi_Mellin_Y0_eq_capfree434
    (sourceOriginalLiteralDepth 20 L) L E U V hL rfl hU hV hUV
    band slot hSelected K J hK hJ Psi hSmooth
    (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
    hSupport alpha beta signed L
  have hBound := hOld.2.2 band hb E hE hEhi Psi hSupport hSmooth
    hPsiPos hPsiLe slot K J alpha beta Acoef Bcoef hAcoef hBcoef
    hAlpha hBeta signed
  rw [hEq] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

