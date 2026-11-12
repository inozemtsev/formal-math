module

public import Green64.Library.Weights.Part028

@[expose] public section

/-!
# Correlation / PhysicalGhostBackgroundSplit

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalGhostBackgroundSplit -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

theorem source_original_partition_sdiff434
    {U : Type} [DecidableEq U] (S A B : Finset U)
    (p : U → Prop) [DecidablePred p]
    (ha : ∀ a ∈ A,p a) (hb : ∀ b ∈ B,¬p b) :
    S \ (A ∪ B) = ((S.filter p) \ A) ∪ ((S.filter (fun a => ¬p a)) \ B) := by
  ext a
  have haa := ha a
  have hbb := hb a
  simp only [Finset.mem_sdiff,Finset.mem_union,Finset.mem_filter]
  tauto

def sourceOriginalGhostPiecePending434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (old deleted : Finset (Atom P modulus)) (born : Finset P) :
    Multiset (Atom P modulus) :=
  (∑ z ∈ old \ deleted,({z} : Multiset (Atom P modulus))) +
    ∑ p ∈ born,({⟨p,0⟩} : Multiset (Atom P modulus))

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ)
variable (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm M)

def sourceOriginalPhysicalGhostPartitionOutput434
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    FullPhysicalOutput SP sm BP bm M :=
  (y.1,fun g => ((y.2 g).1,
    sourceOriginalGhostPiecePending434 (bm g)
      ((y.2 g).2.toFinset.filter (fun z => z.1 ∈ background g)) (a g).1.1 (a g).2.1 +
    sourceOriginalGhostPiecePending434 (bm g)
      ((y.2 g).2.toFinset.filter (fun z => z.1 ∉ background g)) (b g).1.1 (b g).2.1))

theorem source_original_PHYSICAL_G_partition_output434
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y
      (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y
        (sourceOriginalPhysicalGhostRecombine434 SP sm BP bm M background y a b)) =
    sourceOriginalPhysicalGhostPartitionOutput434 SP sm BP bm M background y a b := by
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · have ha : ∀ z ∈ (a g).1.1,z.1 ∈ background g :=
        fun z hz => (Finset.mem_filter.mp ((Finset.mem_powerset.mp (a g).1.2) hz)).2
      have hb : ∀ z ∈ (b g).1.1,z.1 ∉ background g :=
        fun z hz => (Finset.mem_filter.mp ((Finset.mem_powerset.mp (b g).1.2) hz)).2
      have hds : Disjoint
          (((y.2 g).2.toFinset.filter (fun z => z.1 ∈ background g)) \ (a g).1.1)
          (((y.2 g).2.toFinset.filter (fun z => z.1 ∉ background g)) \ (b g).1.1) := by
        apply Finset.disjoint_left.mpr
        intro z hz hw
        exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hw).1).2
          (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).2
      have hdb : Disjoint (a g).2.1 (b g).2.1 := by
        apply Finset.disjoint_left.mpr
        intro p hp hq
        exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp (b g).2.2) hq)).2
          (Finset.mem_filter.mp ((Finset.mem_powerset.mp (a g).2.2) hp)).2
      change
        (∑ z ∈ (y.2 g).2.toFinset \ ((a g).1.1 ∪ (b g).1.1),({z}:Multiset (Atom (BP g) (bm g)))) +
        (∑ z ∈ ((a g).2.1 ∪ (b g).2.1).map (sourceOriginalZeroAtomEmbedding434 (bm g)),
          ({z}:Multiset (Atom (BP g) (bm g)))) = _
      rw [source_original_partition_sdiff434 _ _ _ (fun z => z.1 ∈ background g) ha hb,
        Finset.sum_union hds,Finset.sum_map,Finset.sum_union hdb]
      simp only [sourceOriginalPhysicalGhostPartitionOutput434,
        sourceOriginalGhostPiecePending434,sourceOriginalZeroAtomEmbedding434]
      ac_rfl

def sourceOriginalPhysicalGhostBackgroundSplitRow434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) : ℂ :=
  ∑ ab : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y ×
      SourceOriginalGhostActiveChoice434 SP sm BP bm M background y,
    if ((∀ g,∀ p ∈ (ab.1 g).2.1,bm g p ∉ seen) ∧
        (∀ g,∀ p ∈ (ab.2 g).2.1,bm g p ∉ seen)) then
      (sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y q rho N i V mu ab.1 *
        sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y q rho N i V mu ab.2) *
      F (sourceOriginalPhysicalGhostPartitionOutput434 SP sm BP bm M background y ab.1 ab.2)
        (seen ∪ ((Finset.univ.biUnion (fun g => (ab.1 g).2.1.image (bm g))) ∪
          (Finset.univ.biUnion (fun g => (ab.2 g).2.1.image (bm g)))))
    else 0

/-- Literal all-group G row with its actual signed weights, both
pending pieces, and the complete global no-rebirth/seen observation.
The decomposition is exact for arbitrary joint F. -/
theorem source_original_PHYSICAL_G_background_split_row434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm M q rho N i V mu y seen F =
    sourceOriginalPhysicalGhostBackgroundSplitRow434 SP sm BP bm M background y q rho N i V mu seen F := by
  let H : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y → ℂ := fun d =>
    if ∀ g,∀ p ∈ (d g).2,bm g p ∉ seen then
      F (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y
        (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d))
        (seen ∪ sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm M y d)
    else 0
  have hh := source_original_PHYSICAL_G_partition_joint_sum434
    SP sm BP bm M background y q rho N i V mu H
  unfold sourceOriginalPhysicalGhostUnseenPrimeRow434 sourceOriginalPhysicalGhostBackgroundSplitRow434
  simp only [H,mul_ite,mul_zero] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [source_original_PHYSICAL_G_partition_output434,
    source_original_PHYSICAL_G_partition_births434]
  have he := source_original_PHYSICAL_G_partition_gate434
    SP sm BP bm M background y seen ab.1 ab.2
  by_cases h : (∀ g,∀ p ∈ (ab.1 g).2.1,bm g p ∉ seen) ∧
      (∀ g,∀ p ∈ (ab.2 g).2.1,bm g p ∉ seen)
  · rw [if_pos h,if_pos (he.mpr h)]
  · rw [if_neg h,if_neg (fun hh => h (he.mp hh))]

/-- Application to the original physical marked G, not a new model row. -/
theorem source_original_PHYSICAL_MARKED_G_background_split434
    (cap : BG → ℕ) (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i V mu x seen F =
    sourceOriginalPhysicalGhostBackgroundSplitRow434 SP sm BP bm M background
      (physicalFockProjection SP sm BP bm M cap x) q rho N i V mu seen F := by
  rw [source_original_PHYSICAL_MARKED_G_atom_row434
    SP sm BP bm M cap q rho N i V mu x seen hx hcap F,
    source_original_PHYSICAL_G_unseen_prime_row434 SP sm BP bm M hi,
    source_original_PHYSICAL_G_background_split_row434]
end Green64Analytic.CorrelationSquare

end

end

