module

public import Green64.Library.Correlation.Part030

@[expose] public section

/-!
# Correlation / PhysicalGhostOutputSeparation

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalGhostOutputSeparation -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

private theorem ghostPieceSupport
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (old deleted : Finset (Atom P modulus)) (born : Finset P)
    (pred : P → Prop)
    (ho : ∀ z ∈ old,pred z.1) (hb : ∀ p ∈ born,pred p) :
    ∀ z ∈ sourceOriginalGhostPiecePending434 modulus old deleted born,pred z.1 := by
  intro z hz
  unfold sourceOriginalGhostPiecePending434 at hz
  rcases Multiset.mem_add.mp hz with hz | hz
  · obtain ⟨a,ha,hza⟩ := Multiset.mem_sum.mp hz
    have hza' : z=a := Multiset.mem_singleton.mp hza
    subst z
    exact ho a (Finset.mem_sdiff.mp ha).1
  · obtain ⟨p,hp,hzp⟩ := Multiset.mem_sum.mp hz
    have hzp' : z=⟨p,0⟩ := Multiset.mem_singleton.mp hzp
    subst z
    exact hb p hp

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm M)

/-- The literal G output with only its non-background pending piece.
The source SMALL and BIG active data are retained. -/
def sourceOriginalPhysicalGhostActiveOutput434
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    FullPhysicalOutput SP sm BP bm M :=
  (y.1,fun g => ((y.2 g).1,
    sourceOriginalGhostPiecePending434 (bm g)
      ((y.2 g).2.toFinset.filter (fun z => z.1 ∉ background g)) (b g).1.1 (b g).2.1))

/-- Filtering the literal joint G output recovers exactly its
background pending piece, with all multiplicities preserved. -/
theorem source_original_PHYSICAL_G_partition_background_pending434
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y)
    (g : BG) :
    (((sourceOriginalPhysicalGhostPartitionOutput434 SP sm BP bm M background y a b).2 g).2.filter
      (fun z => z.1 ∈ background g)) =
    sourceOriginalGhostPiecePending434 (bm g)
      ((y.2 g).2.toFinset.filter (fun z => z.1 ∈ background g)) (a g).1.1 (a g).2.1 := by
  have ha := ghostPieceSupport (bm g)
    ((y.2 g).2.toFinset.filter (fun z => z.1 ∈ background g)) (a g).1.1 (a g).2.1
    (fun p => p ∈ background g)
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun p hp => (Finset.mem_filter.mp ((Finset.mem_powerset.mp (a g).2.2) hp)).2)
  have hb := ghostPieceSupport (bm g)
    ((y.2 g).2.toFinset.filter (fun z => z.1 ∉ background g)) (b g).1.1 (b g).2.1
    (fun p => p ∉ background g)
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun p hp => (Finset.mem_filter.mp ((Finset.mem_powerset.mp (b g).2.2) hp)).2)
  change Multiset.filter _ (_+_) = _
  rw [Multiset.filter_add,Multiset.filter_eq_self.mpr ha,Multiset.filter_eq_nil.mpr hb,add_zero]

/-- The actual input of the next E frame is independent of the
background G birth/deletion choice: after removing background pending,
the entire physical output is the explicit non-background output. -/
theorem source_original_PHYSICAL_G_partition_remove_background434
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    sourceOriginalRemovePendingBackground434 SP sm BP bm M background
      (sourceOriginalPhysicalGhostPartitionOutput434 SP sm BP bm M background y a b) =
    sourceOriginalPhysicalGhostActiveOutput434 SP sm BP bm M background y b := by
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · have ha := ghostPieceSupport (bm g)
        ((y.2 g).2.toFinset.filter (fun z => z.1 ∈ background g)) (a g).1.1 (a g).2.1
        (fun p => p ∈ background g)
        (fun z hz => (Finset.mem_filter.mp hz).2)
        (fun p hp => (Finset.mem_filter.mp ((Finset.mem_powerset.mp (a g).2.2) hp)).2)
      have hb := ghostPieceSupport (bm g)
        ((y.2 g).2.toFinset.filter (fun z => z.1 ∉ background g)) (b g).1.1 (b g).2.1
        (fun p => p ∉ background g)
        (fun z hz => (Finset.mem_filter.mp hz).2)
        (fun p hp => (Finset.mem_filter.mp ((Finset.mem_powerset.mp (b g).2.2) hp)).2)
      change Multiset.filter _ (_+_) = _
      rw [Multiset.filter_add,
        Multiset.filter_eq_nil.mpr (fun z hz hh => hh (ha z hz)),
        Multiset.filter_eq_self.mpr hb,zero_add]
      rfl
end Green64Analytic.CorrelationSquare

end

end

