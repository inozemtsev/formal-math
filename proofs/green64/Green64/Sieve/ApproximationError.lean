module

public import Green64.Sieve.BalancedApproximation
public import Green64.Library.Sieve.Foundations.Part055
public import Green64.Library.Sieve.Foundations.Part053

@[expose] public section

/-!
# The two successive proxy replacements

Bound the error from replacing both sharp prime indicators by proxies.
The finite identities keep both replacement orders and their coefficient
norms explicit.
-/

section

set_option maxHeartbeats 2200000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology ContDiff
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT FrozenBins

noncomputable def balancedTwoStepError
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (S b kappa : ℝ) (Y : ℕ) : ℝ :=
  ‖balancedFactorSum false false d L rho Psi S b kappa Y-
    balancedFactorSum true false d L rho Psi S b kappa Y‖ +
  ‖balancedFactorSum true false d L rho Psi S b kappa Y-
    balancedFactorSum true true d L rho Psi S b kappa Y‖

/-- Both successive balanced replacements are exact terms of
the two-sign source ledger, including the nonsmooth second step. -/
theorem balanced_two_step_error_le_required
    (d : ℕ) (L rho : ℝ) (hRho : rho = 1 ∨ rho = -1)
    (Psi : ℝ → ℝ) (S b kappa : ℝ)
    (N : ℕ) (t : ℕ → ℝ) (Y : ℕ) :
    balancedTwoStepError d L rho Psi S b kappa Y ≤
      requiredProxyError d L Psi S b kappa N t Y := by
  let R := fun sign : Bool =>
    (∑ i : Fin N,
      ‖parityOriginalSieveUnbalancedBinSource434 false false d L
          (if sign then 1 else -1) Psi S (t i) (t (i + 1)) Y-
        parityOriginalSieveUnbalancedBinSource434 true false d L
          (if sign then 1 else -1) Psi S (t i) (t (i + 1)) Y‖) +
    ‖balancedFactorSum false false d L
        (if sign then 1 else -1) Psi S b kappa Y-
      balancedFactorSum true false d L
        (if sign then 1 else -1) Psi S b kappa Y‖ +
    ‖balancedFactorSum true false d L
        (if sign then 1 else -1) Psi S b kappa Y-
      balancedFactorSum true true d L
        (if sign then 1 else -1) Psi S b kappa Y‖
  have hflag : ∃ flag : Bool, rho = (if flag then 1 else -1) := by
    rcases hRho with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  obtain ⟨flag, rfl⟩ := hflag
  have hProject : R flag ≤ ∑ sign : Bool, R sign :=
    Finset.single_le_sum (fun sign _ => by dsimp [R]; positivity)
      (Finset.mem_univ flag)
  have hUnbalanced : 0 ≤ ∑ i : Fin N,
      ‖parityOriginalSieveUnbalancedBinSource434 false false d L
          (if flag then 1 else -1) Psi S (t i) (t (i + 1)) Y-
        parityOriginalSieveUnbalancedBinSource434 true false d L
          (if flag then 1 else -1) Psi S (t i) (t (i + 1)) Y‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hBranch : balancedTwoStepError d L
      (if flag then 1 else -1) Psi S b kappa Y ≤ R flag := by
    dsimp [balancedTwoStepError, R]
    linarith
  exact hBranch.trans hProject

/-- Exact sharp source is bounded by its double full-cell proxy
and the shared ledger. No aggregate-source identity is assumed. -/
theorem balanced_sharp_le_proxy_error
    (d : ℕ) (L rho : ℝ) (hRho : rho = 1 ∨ rho = -1)
    (Psi : ℝ → ℝ) (S b kappa : ℝ)
    (N : ℕ) (t : ℕ → ℝ) (Y : ℕ) :
    (balancedFactorSum false false d L rho Psi S b kappa Y).re ≤
      (balancedFactorSum true true d L rho Psi S b kappa Y).re +
        requiredProxyError d L Psi S b kappa N t Y := by
  have h1 := Complex.re_le_norm
    (balancedFactorSum false false d L rho Psi S b kappa Y-
      balancedFactorSum true false d L rho Psi S b kappa Y)
  have h2 := Complex.re_le_norm
    (balancedFactorSum true false d L rho Psi S b kappa Y-
      balancedFactorSum true true d L rho Psi S b kappa Y)
  rw [Complex.sub_re] at h1 h2
  have he := balanced_two_step_error_le_required
    d L rho hRho Psi S b kappa N t Y
  unfold balancedTwoStepError at he
  linarith

end Green64Analytic.Parity

end
