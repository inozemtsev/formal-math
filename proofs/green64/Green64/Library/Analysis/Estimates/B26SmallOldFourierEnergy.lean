module

public import Green64.Library.Weights.Part026

@[expose] public section

/-!
# Analysis / Estimates / B26SmallOldFourierEnergy

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26SmallOldFourierEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000

private theorem character_sum_pair434
    {G : Type} [Fintype G] [AddCommGroup G]
    (psi phi : AddChar G ℂ) :
    (∑ r : G, (starRingEnd ℂ) (psi r) * phi r) =
      if psi = phi then (Fintype.card G : ℂ) else 0 := by
  have h := AddChar.wInner_cWeight_eq_boole psi phi
  have h' : (∑ r : G, (starRingEnd ℂ) (psi r) * phi r) /
      (Fintype.card G : ℂ) = if psi = phi then 1 else 0 := by
    simpa only [RCLike.wInner_cWeight_eq_expect,
      Fintype.expect_eq_sum_div_card, RCLike.inner_apply, mul_comm] using h
  have hn : (Fintype.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hh := (div_eq_iff hn).mp h'
  split_ifs at hh ⊢ <;> simpa using hh

private theorem fourier_synthesis_pair434
    {G : Type} [Fintype G] [AddCommGroup G]
    (a b : AddChar G ℂ → ℂ) :
    (∑ r : G,
      (starRingEnd ℂ) (∑ psi : AddChar G ℂ, a psi * psi r) *
        (∑ phi : AddChar G ℂ, b phi * phi r)) =
    (Fintype.card G : ℂ) *
      ∑ psi : AddChar G ℂ, (starRingEnd ℂ) (a psi) * b psi := by
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ phi : AddChar G ℂ, ∑ psi : AddChar G ℂ,
        ((starRingEnd ℂ) (a psi) * b phi) *
          (∑ r : G, (starRingEnd ℂ) (psi r) * phi r) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro phi _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro psi _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      simp_rw [character_sum_pair434]
      simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

private theorem fourier_synthesis_energy434
    {G : Type} [Fintype G] [AddCommGroup G]
    (a : AddChar G ℂ → ℂ) :
    (∑ r : G, ‖∑ psi : AddChar G ℂ, a psi * psi r‖^2) =
    (Fintype.card G : ℝ) * ∑ psi : AddChar G ℂ, ‖a psi‖^2 := by
  have h := fourier_synthesis_pair434 a a
  simp only [RCLike.conj_mul] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

theorem source_original_B26_full_fourier_energy434
    {G : Type} [Fintype G] [AddCommGroup G] (f : G → ℂ) :
    (∑ r : G, ‖f r‖^2) =
    (Fintype.card G : ℝ) *
      ∑ psi : AddChar G ℂ, ‖(AddChar.complexBasis G).repr f psi‖^2 := by
  have he (r : G) :
      f r = ∑ psi : AddChar G ℂ,
        (AddChar.complexBasis G).repr f psi * psi r := by
    have h := congrFun ((AddChar.complexBasis G).sum_repr f) r
    simpa only [AddChar.complexBasis_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h.symm
  calc
    _ = ∑ r : G, ‖∑ psi : AddChar G ℂ,
        (AddChar.complexBasis G).repr f psi * psi r‖^2 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [he]
    _ = _ := fourier_synthesis_energy434 _

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell : ℕ) (cap sizes : BG → ℕ)
variable (hsizes : ∀ g,sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
local notation "Small" => Green64SmallHaar.GroupState SP smallMod (J+ell)
local notation "SmallTorus" => Green64SmallHaar.GroupTorus SP smallMod
local notation "SmallPerm" => Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "Active" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bigMod sizes prime
local notation "Torus" => memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime


/-- The actual P_d family on the full SMALL/OLD torus satisfies Parseval
with its original counting factor. There is no number-of-frequencies loss. -/
theorem source_original_B26_SMALL_OLD_FOURIER_ENERGY434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (ss : SmallPerm) (U : Small → Active → Old → ℂ) :
    (Fintype.card Torus : ℝ) *
      (∑ d : Shared,∑ psi : AddChar Torus ℂ,∑ a : Active,
        sourceOriginalB26SectorMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime Vs mu a *
        ‖(AddChar.complexBasis Torus).repr
          (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
            J ell sizes prime q Vs ss d U a) psi‖^2) ≤
    memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
      ∑ a : Active,∑ xs : Small,∑ t : Old,
        sourceOriginalB26SectorMass434 SP smallMod BP bigMod
          J ell cap sizes hsizes prime Vs mu a * ‖U xs a t‖^2 := by
  classical
  let mass := sourceOriginalB26SectorMass434 SP smallMod BP bigMod
    J ell cap sizes hsizes prime Vs mu
  let P := sourceOriginalB26SmallLift434 SP smallMod BP bigMod
    J ell sizes prime q Vs ss (U := U)
  have hex : (∑ d : Shared,∑ a : Active,∑ r : Torus,mass a*‖P d a r‖^2) =
      (Fintype.card Torus : ℝ) *
        ∑ d : Shared,∑ psi : AddChar Torus ℂ,∑ a : Active,
          mass a*‖(AddChar.complexBasis Torus).repr (P d a) psi‖^2 := by
    calc
      _ = ∑ d : Shared,∑ a : Active,mass a*(∑ r : Torus,‖P d a r‖^2) := by
        simp only [Finset.mul_sum]
      _ = ∑ d : Shared,∑ a : Active,mass a*((Fintype.card Torus:ℝ)*
          ∑ psi : AddChar Torus ℂ,‖(AddChar.complexBasis Torus).repr (P d a) psi‖^2) := by
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro a _
        rw [source_original_B26_full_fourier_energy434]
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro psi _
        apply Finset.sum_congr rfl
        intro a _
        ring
  rw [← hex]
  exact source_original_B26_SMALL_OLD_ENERGY434 SP smallMod BP bigMod
    J ell cap sizes hsizes prime q hq hq1 Vs hVs mu hmu ss U
end Green64FullPhysicalE

end

end

