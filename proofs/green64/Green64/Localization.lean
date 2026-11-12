module

public import Green64.Library.Sieve.Foundations.Part055
public import Green64.Library.Correlation.Part001

@[expose] public section

/-!
# A concrete smooth localizing function

Construct a smooth function supported in `[1, 2]`, bounded between zero
and one, and positive at an interior point. This fixed cutoff supplies the
analytic hypotheses used to extract arbitrarily large primes.
-/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- A concrete localization, with support in [1,2] and
unit value at 3/2, obtained from the native compact smooth source bump. -/
def localizingBump (x : ℝ) : ℝ :=
  sourceCompactBump434 (2 * x - 3)

theorem localizingBump_smooth :
    ContDiff ℝ ∞ localizingBump :=
  sourceCompactBump434.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem localizingBump_support :
    Function.support localizingBump ⊆ Set.Icc 1 2 := by
  intro x hx
  have hBall : 2 * x - 3 ∈ Metric.ball (0 : ℝ) sourceCompactBump434.rOut := by
    rw [← sourceCompactBump434.support_eq]
    exact hx
  have hAbs : |2 * x - 3| < 1 := by
    simpa [Metric.mem_ball, Real.dist_eq, sourceCompactBump434] using hBall
  obtain ⟨hl, hu⟩ := abs_lt.mp hAbs
  constructor <;> linarith

theorem localizingBump_nonneg (x : ℝ) :
    0 ≤ localizingBump x := sourceCompactBump434.nonneg

theorem localizingBump_le_one (x : ℝ) :
    localizingBump x ≤ 1 := sourceCompactBump434.le_one

theorem localizingBump_interior :
    ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < localizingBump t := by
  have hCenter : sourceCompactBump434 (0 : ℝ) = 1 :=
    sourceCompactBump434.one_of_mem_closedBall
      (by simp [Metric.mem_closedBall, sourceCompactBump434])
  refine ⟨3 / 2, by norm_num, by norm_num, ?_⟩
  norm_num [localizingBump, hCenter]

/-- Nonvacuous source mass for a concrete Psi and both original
parity branches, by direct specialization of the established (1.9). -/
theorem localizingBump_mass_lower_bound :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ᶠ L : ℝ in atTop, ∀ rho : ℝ, (rho = 1 ∨ rho = -1) →
      c0 * Real.exp L * L ^ (-221 : ℝ) ≤
        localizedMass localizingBump rho L :=
  localizedMass_lower_bound
    localizingBump localizingBump_smooth.continuous
    localizingBump_support localizingBump_nonneg
    localizingBump_interior

/-- Completely concrete negative-parity (8.3), retaining only
the permitted balanced-width parameter. This is not a prime-only
positive-mass conclusion: the balanced-composite mass remains. -/
theorem localizingBump_prime_or_composite_mass
    (kappa : ℝ) (hKappa : 0 < kappa) (hKappaUpper : kappa < 1 / 50) :
    ∀ᶠ L : ℝ in atTop,
      (singularSeries / 2) *
        (localizedMass localizingBump (-1) L / L) ≤
      primeMass localizingBump (-1) L +
        balancedCompositeMass (sourceOriginalLiteralDepth 20 L)
          L (-1) localizingBump kappa ⌊2 * Real.exp L⌋₊ :=
  negative_prime_or_composite_mass_lower_bound
    localizingBump localizingBump_smooth
    localizingBump_support localizingBump_nonneg
    localizingBump_le_one localizingBump_interior
    kappa hKappa hKappaUpper
end Green64Analytic.Parity

end

end
