module

public import Green64.Sieve.ApproximationError

@[expose] public section

/-!
# Choose approximation parameters in their required order

Choose the analytic precision parameters needed by the balanced proxy
estimate. The eventual bounds are collected under a common threshold
so the final sieve can use them simultaneously.
-/

section

set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology ContDiff
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT FrozenBins

/-- Close every master-error parameter by native
witnesses. Fixed D*=230, b1,kappa,N, reserved Q and precision precede
K0,H,J,B,S; bin endpoints and the eventual L come afterwards. -/
theorem proxy_parameters_exist
    (Psi : ℝ → ℝ) (hPsiSmooth : ContDiff ℝ ∞ Psi)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀ t, 0 ≤ Psi t) (hPsiLe : ∀ t, Psi t ≤ 1)
    (hPsiInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t)
    (N : ℕ) (b1 kappa : ℝ) (hb1 : 0 < b1) (hb1Small : b1 < 1 / 100)
    (hkappa : 0 < kappa) (hkappaSmall : kappa < 1 / 50) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2 * ((B : ℝ) + 1) + 3 < S ∧
      ∀ t : ℕ → ℝ, Monotone t → t 0 = b1 → t N = 1 / 2 - kappa →
      ∀ rho : ℝ, (rho = 1 ∨ rho = -1) →
      Asymptotics.IsLittleO atTop
        (fun L : ℝ => requiredProxyError
          (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N t ⌊2 * Real.exp L⌋₊)
        (fun L : ℝ => localizedMass Psi rho L / L) ∧
      Asymptotics.IsLittleO atTop
        (fun L : ℝ => allOrdersProxyError
          (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N t ⌊2 * Real.exp L⌋₊)
        (fun L : ℝ => localizedMass Psi rho L / L) := by
  let betaP : ℝ := b1 / 12
  let beta : ℝ := b1 / 3
  have hbetaP : 0 < betaP := by dsimp [betaP]; positivity
  have hbstar : 2 * betaP ≤ b1 / 3 := by dsimp [betaP]; linarith
  have hBeta : beta ≤ 2 * (b1 / 3) := by dsimp [beta]; linarith
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  obtain ⟨jQ, hBand⟩ := parity_original_exists_fixed_reserved_Q_band434 betaP hbetaP
  obtain ⟨target, K0, hTarget, hPrecision, hK0, hK0Target⟩ :=
    parity_original_TypeII_target_K0_precision_compatible434 ((230 : ℝ) + 2)
  obtain ⟨A, hA64, R, hR, buf, hSmooth, hSupport, hOne4, hCube⟩ :=
    parity_original_true_smooth_psi_uniform_fourier_buffer_exists434
  have hPsiComplex : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hPsiSmooth
  have hPsiWide : ∀t : ℝ, (Psi t : ℂ) ≠ 0 → (1 / 64 : ℝ) ≤ t ∧ t ≤ 64 := by
    intro t ht
    have hne : Psi t ≠ 0 := by simpa only [ne_eq, Complex.ofReal_eq_zero] using ht
    have hs := hPsiSet hne
    constructor <;> linarith [hs.1, hs.2]
  exact parity_original_sieve_D230_total_proxy_error_littleO_Xrho434
    N b1 kappa hb1 hb1Small hkappa hkappaSmall
    jQ target 1 beta betaP K0 A R hbetaP hbstar hBeta hBand
    (by norm_num) hTarget hK0Target hPrecision hbeta hK0 (by linarith) hR
    buf hSmooth hSupport hOne4 hCube Psi hPsiComplex hPsiWide hPsiSet
    hPsiPos hPsiLe hPsiInterior

end Green64Analytic.Parity

end
