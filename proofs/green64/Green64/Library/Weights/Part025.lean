module

public import Green64.Library.Correlation.Part021
public import Green64.Library.Weights.Part014

@[expose] public section

/-!
# Weights / Part025

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OrderedMarkedMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]

/-- Every original ordered injective marked list in every SMALL and BIG
group, with no residues and no physical position fixed yet. -/
abbrev B657OrderedMarks434 (M : ℕ) :=
  ((g : SG) → Fin M ↪ SP g) × ((g : BG) → Fin M ↪ BP g)

/-- Complete product of all selected primes, including every group.
For the actual disjoint prime bands every factor is distinct. -/
def b657OrderedMarkProduct434 (M : ℕ) (s : B657OrderedMarks434 SP BP M) : ℕ :=
  (∏ g : SG, ∏ j : Fin M, sm g (s.1 g j)) *
  (∏ g : BG, ∏ j : Fin M, bm g (s.2 g j))

theorem b657_ordered_mark_product_pos434 (M : ℕ) (s : B657OrderedMarks434 SP BP M) :
    0 < b657OrderedMarkProduct434 SP sm BP bm M s := by
  exact mul_pos
    (Finset.prod_pos (fun g _ => Finset.prod_pos (fun j _ => NeZero.pos (sm g (s.1 g j)))))
    (Finset.prod_pos (fun g _ => Finset.prod_pos (fun j _ => NeZero.pos (bm g (s.2 g j)))))

/-- The original harmonic normalization pays for ALL ordered mark lists
without a factorial, a cardinality term, or any dependence in the cap on M. -/
theorem b657_group_ordered_harmonic_mass434 (M : ℕ)
    (V : SG → ℝ) (hV : ∀ g, 0 < V g)
    (hH : ∀ g, V g = ∑ p : SP g, 1/(sm g p:ℝ)) :
    (∏ g : SG, 1/(V g)^M) *
      (∑ s : (g : SG) → Fin M ↪ SP g,
        ∏ g : SG, ∏ j : Fin M, 1/(sm g (s g j):ℝ)) ≤ 1 := by
  have ht : (∑ s : (g : SG) → Fin M ↪ SP g,
        ∏ g : SG, ∏ j : Fin M, 1/(sm g (s g j):ℝ)) =
      ∏ g : SG, ∑ s : Fin M ↪ SP g, ∏ j : Fin M, 1/(sm g (s j):ℝ) :=
    (Fintype.prod_sum (f:=fun g (s : Fin M ↪ SP g) => ∏ j : Fin M, 1/(sm g (s j):ℝ))).symm
  rw [ht,←Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ _g : SG, (1:ℝ) := by
      apply Finset.prod_le_prod₀
      · intro g hg
        apply mul_nonneg (one_div_nonneg.mpr (pow_nonneg (hV g).le M))
        exact Finset.sum_nonneg fun s _ => Finset.prod_nonneg fun j _ =>
          one_div_nonneg.mpr (Nat.cast_nonneg _)
      · intro g hg
        have hb := source_original_ACTUAL_SMALL_injective_moment_le_power434
          M (fun p : SP g => 1/(sm g p:ℝ)) (fun p => one_div_nonneg.mpr (Nat.cast_nonneg _))
        rw [←hH g] at hb
        calc
          _ ≤ (1/(V g)^M)*(V g)^M :=
            mul_le_mul_of_nonneg_left hb (one_div_nonneg.mpr (pow_nonneg (hV g).le M))
          _ = 1 := by field_simp [ne_of_gt (pow_pos (hV g) M)]
    _ = 1 := by simp

/-- Exact separation of the full reciprocal marked product into the
SMALL and BIG ordered harmonic sums. -/
theorem b657_ordered_mark_reciprocal_sum434 (M : ℕ) :
    (∑ s : B657OrderedMarks434 SP BP M,
      1/(b657OrderedMarkProduct434 SP sm BP bm M s:ℝ)) =
    (∑ s : (g : SG) → Fin M ↪ SP g, ∏ g : SG, ∏ j : Fin M, 1/(sm g (s g j):ℝ)) *
    (∑ s : (g : BG) → Fin M ↪ BP g, ∏ g : BG, ∏ j : Fin M, 1/(bm g (s g j):ℝ)) := by
  have hw (s : B657OrderedMarks434 SP BP M) :
      1/(b657OrderedMarkProduct434 SP sm BP bm M s:ℝ) =
        (∏ g : SG, ∏ j : Fin M, 1/(sm g (s.1 g j):ℝ)) *
        (∏ g : BG, ∏ j : Fin M, 1/(bm g (s.2 g j):ℝ)) := by
    unfold b657OrderedMarkProduct434
    push_cast
    simp only [one_div,mul_inv_rev,Finset.prod_inv_distrib]
    ring
  simp_rw [hw]
  change (∑ s : ((g : SG) → Fin M ↪ SP g) × ((g : BG) → Fin M ↪ BP g), _) = _
  rw [Fintype.sum_prod_type,Finset.sum_mul_sum]

/-- Cancellation of the COMPLETE original physical mark mass against
1/D. This is the actual mark-count-free normalization used in the L2
estimate, not a bound on the number of marks at a physical integer. -/
theorem b657_full_ordered_harmonic_mass434 (J ell : ℕ)
    (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hHs : ∀ g, Vs g = ∑ p : SP g, 1/(sm g p:ℝ))
    (hHb : ∀ g, Vb g = ∑ p : BP g, 1/(bm g p:ℝ)) :
    b650IntegerStateMass434 (SG:=SG) (BG:=BG) J ell Vs Vb *
      (∑ s : B657OrderedMarks434 SP BP (J+ell),
        1/(b657OrderedMarkProduct434 SP sm BP bm (J+ell) s:ℝ)) ≤ 1 := by
  rw [b657_ordered_mark_reciprocal_sum434]
  unfold b650IntegerStateMass434
  let A := ∑ s : (g : SG) → Fin (J+ell) ↪ SP g,
    ∏ g : SG, ∏ j : Fin (J+ell), 1/(sm g (s g j):ℝ)
  let B := ∑ s : (g : BG) → Fin (J+ell) ↪ BP g,
    ∏ g : BG, ∏ j : Fin (J+ell), 1/(bm g (s g j):ℝ)
  have hB : 0 ≤ (∏ g : BG, 1/(Vb g)^(J+ell))*B := by
    apply mul_nonneg
      (Finset.prod_nonneg (fun g _ => one_div_nonneg.mpr (pow_nonneg (hVb g).le _)))
    exact Finset.sum_nonneg fun s _ => Finset.prod_nonneg fun g _ =>
      Finset.prod_nonneg fun j _ => one_div_nonneg.mpr (Nat.cast_nonneg _)
  calc
    _ = ((∏ g : SG, 1/(Vs g)^(J+ell))*A)*
        ((∏ g : BG, 1/(Vb g)^(J+ell))*B) := by dsimp [A,B]; ring
    _ ≤ 1*1 := mul_le_mul (b657_group_ordered_harmonic_mass434 SP sm (J+ell) Vs hVs hHs)
      (b657_group_ordered_harmonic_mass434 BP bm (J+ell) Vb hVb hHb) hB (by norm_num)
    _ = 1 := by norm_num
end Green64FullPhysicalE

end

end

/-! ## PhysicalMarkReadout -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell : ℕ)

/-- Read every physical ordered mark and retain its injectivity proof.
No marks are merged or relabelled by their numerical primes. -/
def b657PhysicalMarkReadout434 (positions : Finset ℤ)
    (x : B650IntegerPhysicalState434 SP sm BP bm J ell positions) :
    B657OrderedMarks434 SP BP (J+ell) :=
  ((fun g => ⟨Green64SmallHaar.marks (sm g) (J+ell) (x.val.2.1 g),
    Green64SmallHaar.marks_injective (sm g) (J+ell) (x.val.2.1 g)⟩),
   (fun g => ⟨Green64SmallHaar.marks (bm g) (J+ell) (x.val.2.2 g),
    Green64SmallHaar.marks_injective (bm g) (J+ell) (x.val.2.2 g)⟩))

/-- Physical position and both complete ordered mark lists determine the
whole original native state. All residue coordinates are forced by that
same physical integer, so the L2 reindexing has multiplicity exactly one. -/
theorem b657_physical_position_marks_injective434 (positions : Finset ℤ) :
    Function.Injective (fun x : B650IntegerPhysicalState434 SP sm BP bm J ell positions =>
      (x.val.1.val,b657PhysicalMarkReadout434 SP sm BP bm J ell positions x)) := by
  intro x y h
  have hp := congrArg Prod.fst h
  have hm := congrArg Prod.snd h
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hp
  · apply Prod.ext
    · funext g
      apply Subtype.ext
      apply Prod.ext
      · funext p
        exact (x.property.1 g p).trans ((congrArg (fun n : ℤ => (n:ZMod (sm g p))) hp).trans (y.property.1 g p).symm)
      · exact congrArg (fun s : B657OrderedMarks434 SP BP (J+ell) =>
          (s.1 g : Fin (J+ell) → SP g)) hm
    · funext g
      apply Subtype.ext
      apply Prod.ext
      · funext p
        exact (x.property.2 g p).trans ((congrArg (fun n : ℤ => (n:ZMod (bm g p))) hp).trans (y.property.2 g p).symm)
      · exact congrArg (fun s : B657OrderedMarks434 SP BP (J+ell) =>
          (s.2 g : Fin (J+ell) → BP g)) hm

/-- Every physical marked prime divides the same positive integer.
This is literal divisibility from the original forced zero residues. -/
theorem b657_physical_mark_divides434 (positions : Finset ℤ)
    (x : B650IntegerPhysicalState434 SP sm BP bm J ell positions)
    (hx : 0 ≤ x.val.1.val) :
    (∀ g j, sm g ((b657PhysicalMarkReadout434 SP sm BP bm J ell positions x).1 g j) ∣
      x.val.1.val.toNat) ∧
    (∀ g j, bm g ((b657PhysicalMarkReadout434 SP sm BP bm J ell positions x).2 g j) ∣
      x.val.1.val.toNat) := by
  let hm := b650IntegerStateMarksEquiv434 SP sm BP bm J ell x.val.1.val
    ⟨x.val.2,x.property⟩
  constructor
  · intro g j
    have hz : (sm g ((b657PhysicalMarkReadout434 SP sm BP bm J ell positions x).1 g j):ℤ) ∣ x.val.1.val :=
      (hm.1 g).property.2 j
    rw [←Int.toNat_of_nonneg hx] at hz
    exact_mod_cast hz
  · intro g j
    have hz : (bm g ((b657PhysicalMarkReadout434 SP sm BP bm J ell positions x).2 g j):ℤ) ∣ x.val.1.val :=
      (hm.2 g).property.2 j
    rw [←Int.toNat_of_nonneg hx] at hz
    exact_mod_cast hz
end Green64FullPhysicalE

end

end

