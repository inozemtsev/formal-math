module

public import Green64.Library.Analysis.Estimates.AllPrimeDamping

@[expose] public section

/-!
# Analysis / Estimates / AllPrimeHaar

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## AllPrimeHaar -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 14000000
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

local instance b643AllPrimeHaarSmallNeZero434 (gp : PhysicalSourcePrime SP) : NeZero (physicalSourcePrimeValue SP smallMod gp) :=
  inferInstanceAs (NeZero (smallMod gp.1 gp.2))
local instance b643AllPrimeHaarBigNeZero434 (gp : PhysicalSourcePrime BP) : NeZero (physicalSourcePrimeValue BP bigMod gp) :=
  inferInstanceAs (NeZero (bigMod gp.1 gp.2))

/-- Both genuine initial Haar masses, with every original numerical
coordinate retained. All initial V^-M masses belong to the path weight. -/
def b643AllPrimeHaarMass434 : ℝ :=
  (∏ g : SG, Green64SmallHaar.haarAtomMass (smallMod g)) *
  (∏ g : BG, Green64SmallHaar.haarAtomMass (bigMod g))

/-- Complete SMALL and BIG product local model for an original marked path.
Each family uses the same signed physical offsets and actual marked visits. -/
def b643AllPrimeHaarModel434 {N : ℕ} (q : ℝ)
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ) : ℝ :=
  memoryFrozenHaarExpectation (physicalSourcePrimeValue SP smallMod)
    (sourceVisitEta q N) (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k)
    (b643MarkVisits434 SP (J+ell) N ω.1) (N+1) *
  memoryFrozenHaarExpectation (physicalSourcePrimeValue BP bigMod)
    (sourceVisitEta q N) (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k)
    (b643MarkVisits434 BP (J+ell) N ω.2.1) (N+1)

private theorem b643_family_haar_mass_real :
    (∏ g : SG, Green64SmallHaar.haarAtomMass (smallMod g)) =
    1/(∏ gp : PhysicalSourcePrime SP, (smallMod gp.1 gp.2 : ℝ)) := by
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_prod,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_natCast] using memory_ind_BIG_Haar_mass_exact SP smallMod

theorem b643_all_prime_haar_mass_nonneg434 : 0 ≤ b643AllPrimeHaarMass434 SP smallMod BP bigMod := by
  unfold b643AllPrimeHaarMass434
  rw [b643_family_haar_mass_real SP smallMod,b643_family_haar_mass_real BP bigMod]
  positivity

/-- Exact normalization of the two actual initial anchors. This is a finite
sum equality with the true denominator product over ALL SMALL and BIG primes. -/
theorem b643_all_prime_haar_mean434 {N : ℕ} (q : ℝ)
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ) :
    b643AllPrimeHaarMass434 SP smallMod BP bigMod *
      (∑ c : B643AllPrimeAnchor434 SP smallMod BP bigMod,
        b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q ω k c) =
    b643AllPrimeHaarModel434 SP smallMod BP bigMod J ell m patterns q ω k := by
  unfold b643AllPrimeHaarMass434 b643AllPrimeHaarModel434
  rw [b643_family_haar_mass_real SP smallMod,b643_family_haar_mass_real BP bigMod]
  rw [← memory_ind_BIG_physical_anchor_eq_original_frozen_Haar SP smallMod,
    ← memory_ind_BIG_physical_anchor_eq_original_frozen_Haar BP bigMod]
  unfold memoryIndBIGPhysicalHaarExpectation
  rw [Fintype.sum_prod_type]
  unfold b643AllPrimeAnchorIntegrand434
  rw [← Finset.sum_mul_sum]
  ring

/-- Complete product of prime-local means, with original sourceVisitEta =
1 - sourceVisitQ and the physical anchor reflection already accounted for. -/
theorem b643_all_prime_haar_product434 {N : ℕ} (q : ℝ)
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ) :
    b643AllPrimeHaarModel434 SP smallMod BP bigMod J ell m patterns q ω k =
    (∏ gp : PhysicalSourcePrime SP,
      memoryPrimeHaar (smallMod gp.1 gp.2) (sourceVisitEta q N)
        (fun i => (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k i :
          ZMod (smallMod gp.1 gp.2))) (b643MarkVisits434 SP (J+ell) N ω.1 gp) (N+1)) *
    (∏ gp : PhysicalSourcePrime BP,
      memoryPrimeHaar (bigMod gp.1 gp.2) (sourceVisitEta q N)
        (fun i => (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k i :
          ZMod (bigMod gp.1 gp.2))) (b643MarkVisits434 BP (J+ell) N ω.2.1 gp) (N+1)) := by
  unfold b643AllPrimeHaarModel434
  rw [memory_frozen_Haar_product,memory_frozen_Haar_product]
  rfl

theorem b643_all_prime_haar_model_nonneg434 {N : ℕ} (q : ℝ) (hq : 0 ≤ q)
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ) :
    0 ≤ b643AllPrimeHaarModel434 SP smallMod BP bigMod J ell m patterns q ω k := by
  rw [← b643_all_prime_haar_mean434]
  apply mul_nonneg (b643_all_prime_haar_mass_nonneg434 SP smallMod BP bigMod)
  apply Finset.sum_nonneg
  intro c hc
  exact b643_all_prime_integrand_nonneg434 SP smallMod BP bigMod J ell m patterns q hq ω k c
end Green64FullPhysicalE

end

end

