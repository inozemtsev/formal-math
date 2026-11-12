module

public import Green64.Library.Analysis.Estimates.Part007

@[expose] public section

/-!
# Weights / LiteralEndpointProfiles

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## LiteralEndpointProfiles -/

section

open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The SAME fixed source smooth window chosen in the original constructor
proof, with A=16.  It is an endpoint buffer; the native dyadic psi is not
replaced by it.  The choice precedes every scale and Fourier parameter. -/
def sourceB578EndpointTheta434 : ℝ → ℂ :=
  Classical.choose (source_harmonic_physical_window434 (16:ℝ) (by norm_num))

theorem source_B578_literal_theta_fields434 :
    ContDiff ℝ ∞ sourceB578EndpointTheta434 ∧
    HasCompactSupport sourceB578EndpointTheta434 ∧
    (∀r,sourceB578EndpointTheta434 r≠0 → 1/(64:ℝ) ≤ r ∧ r ≤ 64) ∧
    (∀r ∈ Set.Icc (1/(16:ℝ)) 16,sourceB578EndpointTheta434 r=1) ∧
    (∀r,‖sourceB578EndpointTheta434 r‖ ≤ 1) := by
  simpa only [sourceB578EndpointTheta434,show (4:ℝ)*16=64 by norm_num] using
    (Classical.choose_spec (source_harmonic_physical_window434 (16:ℝ) (by norm_num)))

theorem source_B578_theta_budget_exists434 :
    ∃ K : ℕ → ℝ, (∀j,0 ≤ K j) ∧ ∀L : ℝ,
      sourceLogDerivativeBudget 0 K L (fun u=>sourceB578EndpointTheta434 (Real.exp u)) ∧
      sourceLogDerivativeBudget 0 K L
        (fun u=>sourceB578EndpointTheta434 (Real.exp u)/((Real.exp u:ℝ):ℂ)) :=
  source_fixed_harmonic_profile_budget434 64 sourceB578EndpointTheta434 (by norm_num)
    source_B578_literal_theta_fields434.1 source_B578_literal_theta_fields434.2.2.1

/-- A fixed common derivative sequence for the actual original theta and
its harmonic reciprocal theta/r; it is chosen before L, all marks and phases. -/
def sourceB578ThetaBudget434 : ℕ → ℝ :=
  Classical.choose source_B578_theta_budget_exists434

theorem source_B578_literal_theta_budget_nonneg434 :
    ∀j,0 ≤ sourceB578ThetaBudget434 j :=
  (Classical.choose_spec source_B578_theta_budget_exists434).1

/-- Both literal source endpoint profiles, BEFORE their separate Mellin
phases. true is the reciprocal first endpoint, false the second endpoint. -/
def sourceB578EndpointProfile434 (reciprocal : Bool) (r : ℝ) : ℂ :=
  if reciprocal then sourceB578EndpointTheta434 r/(r:ℂ) else sourceB578EndpointTheta434 r

/-- All profile gates needed by the original comparison record are proved
for the actual two endpoints. There is no assumed derivative budget here. -/
theorem source_B578_literal_endpoint_profile_fields434 (reciprocal : Bool) :
    ContDiff ℝ ∞ (sourceB578EndpointProfile434 reciprocal) ∧
    (∀r,sourceB578EndpointProfile434 reciprocal r≠0 →
      1/(64:ℝ) ≤ r ∧ r ≤ 64) ∧
    (∀L : ℝ,sourceLogDerivativeBudget 0 sourceB578ThetaBudget434 L
      (fun u=>sourceB578EndpointProfile434 reciprocal (Real.exp u))) ∧
    sourceB578EndpointProfile434 reciprocal 1=1 := by
  have h := source_B578_literal_theta_fields434
  have hBudget := (Classical.choose_spec source_B578_theta_budget_exists434).2
  have hOne := h.2.2.2.1 1 (by constructor <;> norm_num)
  cases reciprocal
  · change ContDiff ℝ ∞ sourceB578EndpointTheta434 ∧
        (∀r,sourceB578EndpointTheta434 r≠0 → 1/(64:ℝ) ≤ r ∧ r ≤ 64) ∧
        (∀L : ℝ,sourceLogDerivativeBudget 0 sourceB578ThetaBudget434 L
          (fun u=>sourceB578EndpointTheta434 (Real.exp u))) ∧
        sourceB578EndpointTheta434 1=1
    exact ⟨h.1,h.2.2.1,fun L=>(hBudget L).1,hOne⟩
  · refine ⟨?_,?_,?_,?_⟩
    · exact source_harmonic_reciprocal_smooth434 sourceB578EndpointTheta434 (1/64)
        (by norm_num) h.1 (fun r hr=>(h.2.2.1 r hr).1)
    · intro r hr
      apply h.2.2.1 r
      intro hz
      exact hr (by simp [sourceB578EndpointProfile434,hz])
    · exact fun L=>(hBudget L).2
    · simp [sourceB578EndpointProfile434,hOne]
end Green64Analytic.CorrelationSquare

end

end

