module

public import Green64.Library.Analysis.Estimates.AllPrimeSum
public import Green64.Library.Weights.Part024

@[expose] public section

/-!
# Weights / MarkedPathReturn

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MarkedPathReturn -/

section

open Classical MeasureTheory
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

private theorem b648_edge_weight_theta {N : ℕ}
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (ω : B643AllPrimePath434 SP BP J ell m patterns N) (i : Fin N) :
    b643AllPrimeEdgeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω i =
      b643AllPrimeEdgeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta 0 k ω i *
      b648ReturnCharacter434 theta (physicalAlternatingSign i.val*k*
        (b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℤ)) := by
  unfold b643AllPrimeEdgeWeight434
  dsimp only
  split_ifs with h
  · rw [b648_original_edge_theta434]
    ring
  · simp

/-- The full original marked-path coefficient has precisely one final
physical displacement phase. Every initial mass and all original frame
factors are unchanged, including paths whose coefficient is zero. -/
theorem b648_all_prime_weight_theta434 {N : ℕ}
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (ω : B643AllPrimePath434 SP BP J ell m patterns N) :
    b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω =
      b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta 0 k ω *
      b648ReturnCharacter434 theta
        (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k N) := by
  let d (i : Fin N) : ℤ := physicalAlternatingSign i.val*k*
    (b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℤ)
  have hoff : b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k N =
      ∑ i : Fin N,d i := by
    unfold b643AllPrimeOffset434
    apply Finset.sum_congr rfl
    intro i hi
    exact ite_eq_left i.isLt
  have he : (∏ i : Fin N,b643AllPrimeEdgeWeight434 SP smallMod BP bigMod J ell m patterns
      Vsmall Vbig Knu zeta theta k ω i) =
      (∏ i : Fin N,b643AllPrimeEdgeWeight434 SP smallMod BP bigMod J ell m patterns
        Vsmall Vbig Knu zeta 0 k ω i) * (∏ i : Fin N,b648ReturnCharacter434 theta (d i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact b648_edge_weight_theta SP smallMod BP bigMod J ell m patterns
      Vsmall Vbig Knu zeta theta k ω i
  unfold b643AllPrimeWeight434
  rw [he,b648_return_character_product434,← hoff]
  ring

theorem b648_all_prime_weight_continuous434 {N : ℕ}
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (k : ℤ) (ω : B643AllPrimePath434 SP BP J ell m patterns N) :
    Continuous (fun theta : ℝ =>
      b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω) := by
  have hf : (fun theta : ℝ =>
      b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω) =
      fun theta : ℝ =>
        b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta 0 k ω *
        b648ReturnCharacter434 theta
          (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k N) := by
    funext theta
    exact b648_all_prime_weight_theta434 SP smallMod BP bigMod J ell m patterns
      Vsmall Vbig Knu zeta theta k ω
  rw [hf]
  exact continuous_const.mul (b648_return_character_continuous434 _)

/-- Exact S02 physical-position return projection of the FULL signed
marked-path sum. The terminal ordered marks remain free; only offset_N=0
is imposed. The residue factor can be the actual integer average or Haar
model, and the projector is taken before any absolute value or norm. -/
theorem b648_all_prime_return_projection434 {N : ℕ}
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (k : ℤ) (F : B643AllPrimePath434 SP BP J ell m patterns N → ℂ) :
    (∫ theta : ℝ in (0:ℝ)..1,
      ∑ ω : B643AllPrimePath434 SP BP J ell m patterns N,
        b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω * F ω) =
    ∑ ω : B643AllPrimePath434 SP BP J ell m patterns N,
      if b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k N=0 then
        b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta 0 k ω * F ω
      else 0 := by
  have hi (ω : B643AllPrimePath434 SP BP J ell m patterns N) :
      IntervalIntegrable (fun theta : ℝ =>
        b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω * F ω)
      volume 0 1 :=
    ((b648_all_prime_weight_continuous434 SP smallMod BP bigMod J ell m patterns
      Vsmall Vbig Knu zeta k ω).mul continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (fun ω _ => hi ω)]
  apply Finset.sum_congr rfl
  intro ω hω
  have hf : (fun theta : ℝ =>
      b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω * F ω) =
      fun theta : ℝ =>
        (b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta 0 k ω * F ω) *
        b648ReturnCharacter434 theta
          (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k N) := by
    funext theta
    rw [b648_all_prime_weight_theta434]
    ring
  rw [hf,intervalIntegral.integral_const_mul,b648_return_character_integral434]
  split_ifs <;> simp

/-- A uniform bound on the unrestricted complex sum passes to the exact
position-return projection after, not before, the theta integration. -/
theorem b648_all_prime_return_projection_norm434 {N : ℕ}
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (k : ℤ) (F : B643AllPrimePath434 SP BP J ell m patterns N → ℂ)
    (B : ℝ) (hB : ∀ theta : ℝ,
      ‖∑ ω : B643AllPrimePath434 SP BP J ell m patterns N,
        b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω * F ω‖ ≤ B) :
    ‖∑ ω : B643AllPrimePath434 SP BP J ell m patterns N,
      if b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k N=0 then
        b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta 0 k ω * F ω
      else 0‖ ≤ B := by
  rw [← b648_all_prime_return_projection434]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) (fun theta _ => hB theta)
end Green64FullPhysicalE

end

end

