module

public import Green64.Library.Correlation.Part016
public import Green64.Library.Correlation.Part007

@[expose] public section

/-!
# Correlation / PhysicalActualLiteralGhostBirthWeight

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalActualLiteralGhostBirthWeight -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Complex weights of group-tagged ordered births, no extra symmetry
or Fock factorial and no identification of repeated numerical labels. -/
private theorem complex_birth_flatMap
    {A : Type} (xs : List A) (f : A → List ℂ) :
    (xs.flatMap f).prod = (xs.map (fun a => (f a).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.prod_append, ih]

private theorem complex_birth_groups
    {G : Type} [Fintype G] [DecidableEq G] (f : G → List ℂ) :
    ((Finset.univ.toList : List G).flatMap f).prod =
      ∏ g : G, (f g).prod := by
  rw [complex_birth_flatMap]
  induction (Finset.univ : Finset G) using Finset.induction_on with
  | empty => simp
  | @insert g s hg ih => simpa [Finset.prod_insert hg, ih]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
variable (q rho : ℝ) (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (k : ℤ) (N : ℕ)
variable (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
  J ell m cap patterns q rho Vbig muBig k N)

/-- All actual ordered ghost births, group by group, have exactly the
source mu-tilde measure, with every slot integrated once. -/
theorem physical_actual_ghost_group_birth_product (i : ℕ) :
    ((physicalActualLiteralGhostBatch SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).map
      (fun x => (physicalSourceMuTilde BP bigMod q N Vbig x.1 x.2 : ℂ))).prod =
    ∏ g : BG, ∏ j : Fin ((H.ghost i g).2.1.val),
      (physicalSourceMuTilde BP bigMod q N Vbig g
        ((H.ghost i g).2.2 j).1 : ℂ) := by
  simp only [physicalActualLiteralGhostBatch,
    physicalActualLiteralGhostGroup, List.map_flatMap, List.map_map]
  rw [complex_birth_groups]
  apply Finset.prod_congr rfl
  intro g hg
  simp only [List.map_map, List.map_ofFn, List.prod_ofFn]
  rfl

/-- Source branch muBig is a parameter of the raw G witness.
This hypothesis is essential, rather than inferred from the history. -/
theorem physical_actual_ghost_group_birth_muBig
    (hmu : ∀ g : BG, ∀ p : BP g,
      (muBig g p : ℂ) =
        (physicalSourceMuTilde BP bigMod q N Vbig g p : ℂ))
    (i : ℕ) :
    ((physicalActualLiteralGhostBatch SP smallMod BP bigMod
        J ell m cap patterns q rho Vbig muBig k N H i).map
      (fun x => (physicalSourceMuTilde BP bigMod q N Vbig x.1 x.2 : ℂ))).prod =
    ∏ g : BG, ∏ j : Fin ((H.ghost i g).2.1.val),
      (muBig g ((H.ghost i g).2.2 j).1 : ℂ) := by
  rw [physical_actual_ghost_group_birth_product]
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro j hj
  exact (hmu g ((H.ghost i g).2.2 j).1).symm
end Green64FullPhysicalE

end

