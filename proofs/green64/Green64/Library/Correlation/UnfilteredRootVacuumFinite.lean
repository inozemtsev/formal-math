module

public import Green64.Library.Correlation.Part063
public import Green64.Library.Weights.Part014
public import Green64.Library.Correlation.RetiredPhysicalVacuum

@[expose] public section

/-!
# Correlation / UnfilteredRootVacuumFinite

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredRootVacuumFinite -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The actual SMALL measure needs no exact harmonic normalization:
its true Haar fibre is summed once, retaining injective marked tuples. -/
theorem source_original_root_SMALL_HARMONIC_BOUND434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (M : ℕ) (V : ℝ) (hV : 0 < V) :
    (∑ x : SmallState modulus M,stateMass modulus M V) ≤
      ((∑ p : P,1/(modulus p:ℝ))/V)^M := by
  rw [source_original_ACTUAL_SMALL_state_mass_marked_moment434]
  calc
    _ ≤ (1/V^M)*(∑ p : P,1/(modulus p:ℝ))^M :=
      mul_le_mul_of_nonneg_left
        (source_original_ACTUAL_SMALL_injective_moment_le_power434 M
          (fun p : P => 1/(modulus p:ℝ)) (fun p => by positivity)) (by positivity)
    _ = _ := by rw [div_pow]; ring

private theorem root_fock_zero_unique434
    {U : Type} [Fintype U] [DecidableEq U] {B : ℕ}
    (x : Green64Fock.FockState U B)
    (hx : Green64Fock.fockMultiset x=0) :
    x=Green64Fock.vacuumState U B := by
  have hz : x.1.val=0 := by
    have hh := congrArg Multiset.card hx
    simpa [Green64Fock.fockMultiset] using hh
  rcases x with ⟨⟨n,hn⟩,f⟩
  dsimp only at hz
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

private theorem root_fock_vacuum_sum434
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
      exact root_fock_zero_unique434 (f g) (hh g)
    simp [hn]
  · simp

/-- Bvac is the energy of the WHOLE empty-OLD subset. BIG active arrays
remain free; their tilted mass is retained rather than normalized away. -/
theorem source_original_root_VACUUM_ENERGY_EXACT434
    (J ell : ℕ) (cap : BG → ℕ) (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) :
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (physicalVacuum SP sm BP bm J ell) =
      (∑ s : GroupState SP sm (J+ell),groupStateMass SP sm (J+ell) Vs) *
        ∏ g,(∑ p : BP g,mu g p)^(J+ell) := by
  rw [←source_original_physical_ORDERED_ORBIT_ENERGY434,
    ←source_original_RETIRED_boundary_base_exact434 BP (J+ell) SP sm Vs mu]
  let A := (g : BG) → Fin (J+ell) → BP g
  let F := (g : BG) → Green64Fock.FockState (Green64Fock.Atom (BP g) (bm g)) (cap g)
  let S := GroupState SP sm (J+ell)
  let e : FullPhysicalState SP sm BP bm (J+ell) cap ≃ S × A × F :=
    { toFun := fun x => (x.1,(fun g => (x.2 g).1),(fun g => (x.2 g).2))
      invFun := fun x => (x.1,fun g => (x.2.1 g,x.2.2 g))
      left_inv := by intro x;rfl
      right_inv := by intro x;rfl }
  let w := fun x : FullPhysicalState SP sm BP bm (J+ell) cap =>
    fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x *
      ‖physicalVacuum SP sm BP bm J ell (physicalFockProjection SP sm BP bm (J+ell) cap x)‖^2
  have he := Fintype.sum_equiv e w (fun x => w (e.symm x))
    (by intro x;rw [e.symm_apply_apply])
  change (∑ x,w x)=_
  rw [he,Fintype.sum_prod_type]
  unfold sourceOriginalRetiredBoundaryBase434
  apply Finset.sum_congr rfl
  intro s hs
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  have hp (f : F) :
      w (e.symm (s,a,f)) =
      (groupStateMass SP sm (J+ell) Vs * ∏ g,activeMass (J+ell) (mu g) (a g)) *
      ((∏ g,Green64Fock.fockMass (Green64Fock.sourceAtomMu (mu g)) (f g)) *
        (if ∀ g,Green64Fock.fockMultiset (f g)=0 then (1:ℝ) else 0)) := by
    dsimp only [w,e,Equiv.coe_fn_symm_mk,fullPhysicalMass,bigGroupStateMass,bigStateMass,
      physicalVacuum,physicalFockProjection]
    rw [Finset.prod_mul_distrib]
    split_ifs <;> simp_all only [norm_one,norm_zero,one_pow,zero_pow (by decide : 2≠0)] <;> ring
  simp_rw [hp]
  rw [←Finset.mul_sum,root_fock_vacuum_sum434 BP bm cap mu,mul_one]
  rfl

theorem source_original_root_VACUUM_FINITE_BOUND434
    (J ell : ℕ) (cap : BG → ℕ) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hMass : ∀ g,(∑ p : BP g,mu g p)≤2) :
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (physicalVacuum SP sm BP bm J ell) ≤
      (∏ g : SG,((∑ p : SP g,1/(sm g p:ℝ))/Vs g)^(J+ell)) *
        (2:ℝ)^((J+ell)*Fintype.card BG) := by
  rw [source_original_root_VACUUM_ENERGY_EXACT434]
  have hSmall :
      (∑ s : GroupState SP sm (J+ell),groupStateMass SP sm (J+ell) Vs) ≤
        ∏ g : SG,((∑ p : SP g,1/(sm g p:ℝ))/Vs g)^(J+ell) := by
    change (∑ s : (g : SG) → SmallState (sm g) (J+ell),
      ∏ g,stateMass (sm g) (J+ell) (Vs g)) ≤ _
    rw [←Fintype.prod_sum (fun (g : SG) (_ : SmallState (sm g) (J+ell)) =>
      stateMass (sm g) (J+ell) (Vs g))]
    apply Finset.prod_le_prod₀
    · intro g hg
      exact Finset.sum_nonneg (fun s hs => (stateMass_positive (sm g) (J+ell) (Vs g) (hVs g)).le)
    · intro g hg
      exact source_original_root_SMALL_HARMONIC_BOUND434 (sm g) (J+ell) (Vs g) (hVs g)
  have hBig : (∏ g : BG,(∑ p : BP g,mu g p)^(J+ell)) ≤ (2:ℝ)^((J+ell)*Fintype.card BG) := by
    calc
      _ ≤ ∏ _g : BG,(2:ℝ)^(J+ell) := Finset.prod_le_prod₀
        (fun g hg => pow_nonneg (Finset.sum_nonneg (fun p hp => hmu g p)) _)
        (fun g hg => pow_le_pow_left₀ (Finset.sum_nonneg (fun p hp => hmu g p)) (hMass g) _)
      _ = _ := by simp [←pow_mul]
  exact mul_le_mul hSmall hBig
    (Finset.prod_nonneg (fun g hg => pow_nonneg (Finset.sum_nonneg (fun p hp => hmu g p)) _))
    (Finset.prod_nonneg (fun g hg => pow_nonneg
      (div_nonneg (Finset.sum_nonneg (fun p hp => by positivity)) (hVs g).le) _))
end Green64Analytic.CorrelationSquare

end

end

