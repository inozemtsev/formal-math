module

public import Green64.Library.Weights.Part065

@[expose] public section

/-!
# Weights / ActualInitialVacuumDisintegration

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualInitialVacuumDisintegration -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 24000000

private theorem fock_vacuum_unique434
    {U : Type} [Fintype U] [DecidableEq U] {B : ℕ}
    (x : Green64Fock.FockState U B)
    (hx : Green64Fock.fockMultiset x = 0) :
    x = Green64Fock.vacuumState U B := by
  have hzero : x.1.val = 0 := by
    have hh := congrArg Multiset.card hx
    simpa [Green64Fock.fockMultiset] using hh
  rcases x with ⟨⟨n,hn⟩,f⟩
  dsimp only at hzero
  subst n
  apply congrArg (fun f : Fin 0 → U => (⟨⟨0,hn⟩,f⟩ : Green64Fock.FockState U B))
  funext i
  exact i.elim0

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

/-- Exact disintegration of the initial vacuum mass back to original
ordered physical states. No Fock factor, baseline or initial gate is lost. -/
theorem source_original_ACTUAL_initial_mass_ordered434
    (J ell : ℕ) (cap : BG → ℕ) (q : ℝ)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g) (V : BG → ℝ) (hV : ∀ g,0 < V g)
    (R : ℕ) (hb : ∀ g p,0 < physicalSourceBaseline BP bm q (2*R) g p) :
    sourceOriginalActualInitialVacuumMass434 SP sm BP bm J ell cap q Vs V R =
    ‖(physicalSourceBaselineProduct BP bm q (2*R):ℂ)‖ *
      ∑ x : FullPhysicalState SP sm BP bm (J+ell) cap,
        fullPhysicalMass SP sm BP bm (J+ell) cap Vs
          (physicalSourceMuTilde BP bm q (2*R) V) x *
        ‖physicalVacuum SP sm BP bm J ell
          (physicalFockProjection SP sm BP bm (J+ell) cap x)‖ *
        (if (physicalOutputInitialBirths SP sm BP bm J ell
          (physicalFockProjection SP sm BP bm (J+ell) cap x)).Nodup then 1 else 0) := by
  let mu := physicalSourceMuTilde BP bm q (2*R) V
  have hmu (g : BG) (p : BP g) : 0 < mu g p := by
    dsimp [mu,physicalSourceMuTilde]
    exact div_pos zero_lt_one (mul_pos (mul_pos (hV g)
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (bm g p)))) (hb g p))
  let pr := physicalFockProjection SP sm BP bm (J+ell) cap
  let w := fun y : FullPhysicalOutput SP sm BP bm (J+ell) =>
    ‖physicalVacuum SP sm BP bm J ell y‖ *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then (1:ℝ) else 0)
  have he :
      (∑ x : FullPhysicalState SP sm BP bm (J+ell) cap,
        fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x * w (pr x)) =
      ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y * w y := by
    have hh := Green64Fock.finite_sum_by_image
      (Finset.univ : Finset (FullPhysicalState SP sm BP bm (J+ell) cap)) pr
      (fun x => ((fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x * w (pr x):ℝ):ℂ))
    have hhR :
      (∑ x : FullPhysicalState SP sm BP bm (J+ell) cap,
        fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x * w (pr x)) =
      ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        ∑ x ∈ (Finset.univ : Finset (FullPhysicalState SP sm BP bm (J+ell) cap))
          with pr x=y,fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x*w (pr x) := by
      exact_mod_cast hh
    rw [hhR]
    apply Finset.sum_congr rfl
    intro y hy
    rw [physicalOrbitMass,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  unfold sourceOriginalActualInitialVacuumMass434
  dsimp only
  congr 1
  simp_rw [mul_assoc]
  rw [he]
  apply Finset.sum_congr rfl
  intro y hy
  have hp := physicalOrbitMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu y hy
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
end Green64Analytic.CorrelationSquare

end

end

