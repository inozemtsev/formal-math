module

public import Green64.Library.Weights.ActualInitialVacuumDisintegration

@[expose] public section

/-!
# Weights / ActualInitialVacuumFactor

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualInitialVacuumFactor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 26000000

private theorem fock_zero_unique434
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

private theorem vacuum_fock_sum434
    (cap : BG → ℕ) (mu : (g : BG) → BP g → ℝ) :
    (∑ f : (g : BG) → Green64Fock.FockState (Green64Fock.Atom (BP g) (bm g)) (cap g),
      (∏ g,Green64Fock.fockMass (Green64Fock.sourceAtomMu (mu g)) (f g)) *
      (if ∀ g,Green64Fock.fockMultiset (f g)=0 then (1:ℝ) else 0))=1 := by
  let f0 := fun g => Green64Fock.vacuumState (Green64Fock.Atom (BP g) (bm g)) (cap g)
  rw [Finset.sum_eq_single f0]
  · have hz : ∀ g,Green64Fock.fockMultiset (f0 g)=0 := by
      intro g
      simp [f0,Green64Fock.fockMultiset,Green64Fock.vacuumState]
    rw [if_pos hz,mul_one]
    simp only [f0,Green64Fock.vacuum_fockMass,Finset.prod_const_one]
  · intro f hf hne
    have hn : ¬∀ g,Green64Fock.fockMultiset (f g)=0 := by
      intro hh
      apply hne
      funext g
      exact fock_zero_unique434 (f g) (hh g)
    simp [hn]
  · simp

/-- Exact initial vacuum boundary reduction to original SMALL physical
mass and BIG active arrays. This removes all Fock sectors using their
actual vacuum fibre and retains the numerical initial birth filter. -/
theorem source_original_ACTUAL_initial_mass_vacuum_factor434
    (J ell : ℕ) (cap : BG → ℕ) (q : ℝ)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g) (V : BG → ℝ) (hV : ∀ g,0 < V g)
    (R : ℕ) (hb : ∀ g p,0 < physicalSourceBaseline BP bm q (2*R) g p) :
    sourceOriginalActualInitialVacuumMass434 SP sm BP bm J ell cap q Vs V R =
    ‖(physicalSourceBaselineProduct BP bm q (2*R):ℂ)‖ *
      ∑ s : GroupState SP sm (J+ell),∑ a : (g : BG) → Fin (J+ell) → BP g,
        groupStateMass SP sm (J+ell) Vs *
        (∏ g,activeMass (J+ell) (physicalSourceMuTilde BP bm q (2*R) V g) (a g)) *
        (if (physicalOutputInitialBirths SP sm BP bm J ell
          (s,fun g => (a g,0))).Nodup then 1 else 0) := by
  rw [source_original_ACTUAL_initial_mass_ordered434 SP sm BP bm J ell cap q Vs hVs V hV R hb]
  congr 1
  let A := (g : BG) → Fin (J+ell) → BP g
  let F := (g : BG) → Green64Fock.FockState (Green64Fock.Atom (BP g) (bm g)) (cap g)
  let S := GroupState SP sm (J+ell)
  let e : FullPhysicalState SP sm BP bm (J+ell) cap ≃ S × A × F :=
    { toFun := fun x => (x.1,(fun g => (x.2 g).1),(fun g => (x.2 g).2))
      invFun := fun x => (x.1,fun g => (x.2.1 g,x.2.2 g))
      left_inv := by intro x;rfl
      right_inv := by intro x;rfl }
  let mu := physicalSourceMuTilde BP bm q (2*R) V
  let w := fun x : FullPhysicalState SP sm BP bm (J+ell) cap =>
    fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x *
    ‖physicalVacuum SP sm BP bm J ell (physicalFockProjection SP sm BP bm (J+ell) cap x)‖ *
    (if (physicalOutputInitialBirths SP sm BP bm J ell
      (physicalFockProjection SP sm BP bm (J+ell) cap x)).Nodup then (1:ℝ) else 0)
  have he := Fintype.sum_equiv e w (fun x => w (e.symm x))
    (by intro x;rw [e.symm_apply_apply])
  change (∑ x,w x)=_
  rw [he,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  have hp (f : F) :
      w (e.symm (s,a,f)) =
      (groupStateMass SP sm (J+ell) Vs * (∏ g,activeMass (J+ell) (mu g) (a g)) *
        (if (physicalOutputInitialBirths SP sm BP bm J ell (s,fun g => (a g,0))).Nodup then (1:ℝ) else 0)) *
      ((∏ g,Green64Fock.fockMass (Green64Fock.sourceAtomMu (mu g)) (f g)) *
        (if ∀ g,Green64Fock.fockMultiset (f g)=0 then (1:ℝ) else 0)) := by
    dsimp only [w,e,Equiv.coe_fn_symm_mk,fullPhysicalMass,bigGroupStateMass,bigStateMass,
      physicalVacuum,physicalFockProjection,physicalOutputInitialBirths]
    rw [Finset.prod_mul_distrib]
    split_ifs <;> simp_all only [norm_one,norm_zero] <;> ring
  simp_rw [hp]
  rw [←Finset.mul_sum,vacuum_fock_sum434 BP bm cap mu,mul_one]

/-- The original global initial filter and baseline pay the complete
BIG active and Fock boundary. Only the exact SMALL marked-state mass
remains; no factor depending on J, BIG groups or cap is paid. -/
theorem source_original_ACTUAL_initial_mass_le_SMALL_mass434
    (J ell : ℕ) (cap : BG → ℕ) (q : ℝ)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g) (V : BG → ℝ) (hV : ∀ g,0 < V g)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
    (R : ℕ) (hb : ∀ g p,0 < physicalSourceBaseline BP bm q (2*R) g p)
    (hb1 : ∀ g p,physicalSourceBaseline BP bm q (2*R) g p ≤ 1) :
    sourceOriginalActualInitialVacuumMass434 SP sm BP bm J ell cap q Vs V R ≤
      ∑ s : GroupState SP sm (J+ell),groupStateMass SP sm (J+ell) Vs := by
  rw [source_original_ACTUAL_initial_mass_vacuum_factor434 SP sm BP bm
    J ell cap q Vs hVs V hV R hb,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsm : 0 ≤ groupStateMass SP sm (J+ell) Vs :=
    Finset.prod_nonneg (fun g _ => (stateMass_positive (sm g) (J+ell) (Vs g) (hVs g)).le)
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ a : (g : BG) → Fin (J+ell) → BP g,
      groupStateMass SP sm (J+ell) Vs *
        (∏ g,activeMass (J+ell) (fun p => 1/(V g*(bm g p:ℝ))) (a g)) := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs with hn
      · rw [mul_one,mul_left_comm]
        exact mul_le_mul_of_nonneg_left
          (source_original_ACTUAL_initial_nodup_baseline_cancel434 SP sm BP bm
            J ell q (2*R) V hV (s,fun g => (a g,0)) hn hb hb1) hsm
      · simp only [mul_zero]
        apply mul_nonneg hsm
        exact Finset.prod_nonneg (fun g _ => activeMass_nonneg (J+ell) _
          (fun p => div_nonneg zero_le_one (mul_nonneg (hV g).le (Nat.cast_nonneg _))) (a g))
    _ = _ := by
      rw [←Finset.mul_sum,source_original_ACTUAL_active_harmonic_mass_one434 BP bm
        (J+ell) V hV hHarmonic,mul_one]
end Green64Analytic.CorrelationSquare

end

end

