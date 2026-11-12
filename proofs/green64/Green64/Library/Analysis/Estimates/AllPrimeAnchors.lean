module

public import Green64.Library.Correlation.Part020

@[expose] public section

/-!
# Analysis / Estimates / AllPrimeAnchors

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## AllPrimeAnchors -/

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

/-- Two complete original tori, one initial anchor for SMALL and one
for BIG, equivalently one coordinate for every prime in the full family. -/
abbrev B643AllPrimeAnchor434 :=
  MemoryIndependentBIGTorus SP smallMod × MemoryIndependentBIGTorus BP bigMod

private theorem b643_offset_zero {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ) :
    b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k 0=0 := by
  simp [b643AllPrimeOffset434]

private theorem b643_offset_step {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ) (i : Fin N) :
    b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k (i.val+1) -
      b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k i.val =
    physicalAlternatingSign i.val*k*(b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℤ) := by
  let F (j : Fin N) := physicalAlternatingSign j.val*k*
    (b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω j : ℤ)
  have hm (j : Fin N) : (if j.val < i.val+1 then F j else 0) =
      (if j.val < i.val then F j else 0)+(if j=i then F j else 0) := by
    by_cases he : j=i
    · subst j; simp
    · have hn : j.val≠i.val := fun h => he (Fin.ext h)
      have hh : j.val < i.val+1 ↔ j.val < i.val := by omega
      simp [he,hh]
  have hh : b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k (i.val+1) =
      b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k i.val+F i := by
    unfold b643AllPrimeOffset434
    change (∑ j : Fin N,if j.val < i.val+1 then F j else 0)=_
    simp_rw [hm]
    rw [Finset.sum_add_distrib]
    simp [F]
  rw [hh]
  simp [F]

private theorem b643_fin_torus_anchor (N : ℕ)
    (C : Fin (N+1) → MemoryIndependentBIGTorus SP smallMod) (off : ℕ → ℤ)
    (hstep : ∀ i : Fin N, C i.succ = memoryIndBIGTorusTranslate SP smallMod
      (off (i.val+1)-off i.val) (C i.castSucc))
    (hz : off 0=0) :
    ∀ t : Fin (N+1), C t = memoryIndBIGTorusTranslate SP smallMod (off t.val) (C 0) := by
  intro t
  induction t using Fin.induction with
  | zero =>
    change C 0 = memoryIndBIGTorusTranslate SP smallMod (off 0) (C 0)
    rw [hz]
    exact (memory_ind_BIG_torus_translate_zero SP smallMod (C 0)).symm
  | succ i ih =>
    change C i.castSucc = memoryIndBIGTorusTranslate SP smallMod (off i.val) (C 0) at ih
    change C i.succ = memoryIndBIGTorusTranslate SP smallMod (off (i.val+1)) (C 0)
    rw [hstep i,ih,memory_ind_BIG_torus_translate_comp]
    congr 1
    omega

/-- Both complete source residue arrays are determined by the SAME
literal signed offsets and their single initial anchors. This includes
the missing SMALL transport, with every numerical coordinate retained. -/
theorem b643_all_prime_array_one_anchor434 {N : ℕ}
    (k : ℤ) (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (ht : ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns states frames k i) :
    let ω := b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames
    let off := b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k
    (∀ t : Fin (N+1),
      (fun g => Green64SmallHaar.residues (smallMod g) (J+ell) ((states t).1 g)) =
      memoryIndBIGTorusTranslate SP smallMod (off t.val)
        (fun g => Green64SmallHaar.residues (smallMod g) (J+ell) ((states 0).1 g))) ∧
    (∀ t : Fin (N+1),
      (fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states t).2 g)) =
      memoryIndBIGTorusTranslate BP bigMod (off t.val)
        (fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states 0).2 g))) := by
  let ω := b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames
  let off := b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k
  dsimp only
  constructor
  · apply b643_fin_torus_anchor SP smallMod N
      (fun t g => Green64SmallHaar.residues (smallMod g) (J+ell) ((states t).1 g)) off
    · intro i
      dsimp [off]
      rw [b643_offset_step]
      funext g
      exact (ht i).1 g
    · exact b643_offset_zero SP smallMod BP bigMod J ell m patterns ω k
  · apply b643_fin_torus_anchor BP bigMod N
      (fun t g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states t).2 g)) off
    · intro i
      dsimp [off]
      rw [b643_offset_step]
      funext g
      exact (ht i).2 g
    · exact b643_offset_zero SP smallMod BP bigMod J ell m patterns ω k

/-- All prescribed marks are actual zeros of the transported anchors. -/
def b643AllPrimeAnchorAllowed434 {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ)
    (c : B643AllPrimeAnchor434 SP smallMod BP bigMod) : Prop :=
  (∀ (t : Fin (N+1)) (g : SG) (j : Fin (J+ell)), c.1 g ((ω.1 t g).val j) +
    (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val :
      ZMod (smallMod g ((ω.1 t g).val j)))=0) ∧
  (∀ (t : Fin (N+1)) (g : BG) (j : Fin (J+ell)), c.2 g ((ω.2.1 t g).val j) +
    (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val :
      ZMod (bigMod g ((ω.2.1 t g).val j)))=0)

/-- Reconstruct ALL original states from marks/frames and both full initial
anchors. These are the actual dependent valid-zero-mark state carriers. -/
def b643AllPrimeAnchoredStates434 {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ)
    (c : B643AllPrimeAnchor434 SP smallMod BP bigMod)
    (ha : b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns ω k c) :
    Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell :=
  fun t =>
    (memoryIndependentBIGStateFrom SP smallMod (J+ell)
      (memoryIndBIGTorusTranslate SP smallMod
        (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val) c.1)
      (fun g => ⟨(ω.1 t g).val,(ω.1 t g).property,ha.1 t g⟩),
     memoryIndependentBIGStateFrom BP bigMod (J+ell)
      (memoryIndBIGTorusTranslate BP bigMod
        (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val) c.2)
      (fun g => ⟨(ω.2.1 t g).val,(ω.2.1 t g).property,ha.2 t g⟩))

private theorem b643_anchored_readout {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ)
    (c : B643AllPrimeAnchor434 SP smallMod BP bigMod)
    (ha : b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns ω k c) :
    b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns
      (b643AllPrimeAnchoredStates434 SP smallMod BP bigMod J ell m patterns ω k c ha) ω.2.2 = ω := rfl

theorem b643_anchored_transport {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ)
    (c : B643AllPrimeAnchor434 SP smallMod BP bigMod)
    (ha : b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns ω k c) (i : Fin N) :
    b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns
      (b643AllPrimeAnchoredStates434 SP smallMod BP bigMod J ell m patterns ω k c ha) ω.2.2 k i := by
  have hs := b643_offset_step SP smallMod BP bigMod J ell m patterns ω k i
  have ho : b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k (i.val+1) =
      b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k i.val+
      physicalAlternatingSign i.val*k*(b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℤ) := by omega
  constructor
  · intro g; funext p
    change c.1 g p+(b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k (i.val+1) : ZMod (smallMod g p)) =
      (c.1 g p+(b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k i.val : ZMod (smallMod g p)))+
      ((physicalAlternatingSign i.val*k*(b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℤ) : ℤ) : ZMod (smallMod g p))
    rw [ho,Int.cast_add,add_assoc]
  · intro g; funext p
    change c.2 g p+(b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k (i.val+1) : ZMod (bigMod g p)) =
      (c.2 g p+(b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k i.val : ZMod (bigMod g p)))+
      ((physicalAlternatingSign i.val*k*(b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℤ) : ℤ) : ZMod (bigMod g p))
    rw [ho,Int.cast_add,add_assoc]

private theorem b643_anchored_initial {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ)
    (c : B643AllPrimeAnchor434 SP smallMod BP bigMod)
    (ha : b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns ω k c) :
    ((fun g => Green64SmallHaar.residues (smallMod g) (J+ell)
        ((b643AllPrimeAnchoredStates434 SP smallMod BP bigMod J ell m patterns ω k c ha 0).1 g)),
     (fun g => Green64SmallHaar.residues (bigMod g) (J+ell)
        ((b643AllPrimeAnchoredStates434 SP smallMod BP bigMod J ell m patterns ω k c ha 0).2 g))) = c := by
  apply Prod.ext
  · funext g p
    change c.1 g p+(b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k 0 : ZMod (smallMod g p))=c.1 g p
    rw [b643_offset_zero,Int.cast_zero,add_zero]
  · funext g p
    change c.2 g p+(b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k 0 : ZMod (bigMod g p))=c.2 g p
    rw [b643_offset_zero,Int.cast_zero,add_zero]

theorem b643_transport_anchor_allowed {N : ℕ}
    (k : ℤ) (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (ht : ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns states frames k i) :
    b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns
      (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames) k
      ((fun g => Green64SmallHaar.residues (smallMod g) (J+ell) ((states 0).1 g)),
       (fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states 0).2 g))) := by
  have hc := b643_all_prime_array_one_anchor434 SP smallMod BP bigMod J ell m patterns k states frames ht
  constructor
  · intro t g j
    have he := congrArg (fun C : MemoryIndependentBIGTorus SP smallMod =>
      C g (Green64SmallHaar.marks (smallMod g) (J+ell) ((states t).1 g) j)) (hc.1 t)
    exact he.symm.trans (Green64SmallHaar.marked_zero (smallMod g) (J+ell) ((states t).1 g) j)
  · intro t g j
    have he := congrArg (fun C : MemoryIndependentBIGTorus BP bigMod =>
      C g (Green64SmallHaar.marks (bigMod g) (J+ell) ((states t).2 g) j)) (hc.2 t)
    exact he.symm.trans (Green64SmallHaar.marked_zero (bigMod g) (J+ell) ((states t).2 g) j)

private theorem b643_transport_reconstruct {N : ℕ}
    (k : ℤ) (states : Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (ht : ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns states frames k i) :
    b643AllPrimeAnchoredStates434 SP smallMod BP bigMod J ell m patterns
      (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames) k
      ((fun g => Green64SmallHaar.residues (smallMod g) (J+ell) ((states 0).1 g)),
       (fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states 0).2 g)))
      (b643_transport_anchor_allowed SP smallMod BP bigMod J ell m patterns k states frames ht) = states := by
  have hc := b643_all_prime_array_one_anchor434 SP smallMod BP bigMod J ell m patterns k states frames ht
  funext t
  apply Prod.ext
  · funext g
    apply Subtype.ext
    apply Prod.ext
    · exact (congrFun (hc.1 t) g).symm
    · rfl
  · funext g
    apply Subtype.ext
    apply Prod.ext
    · exact (congrFun (hc.2 t) g).symm
    · rfl

/-- Exact supported FULL-array bijection to marks/frames and one initial
anchor for every SMALL and BIG prime. Zero coefficients remain included;
no nonzero K, positivity, multiplicity or reconstruction premise is used. -/
def b643AllPrimeTransportEquiv434 (N : ℕ) (k : ℤ) :
    {sf : ((Fin (N+1) → MemoryIndependentState SP smallMod BP bigMod J ell) ×
      (Fin N → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)) //
      ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns sf.1 sf.2 k i} ≃
    {oc : (B643AllPrimePath434 SP BP J ell m patterns N × B643AllPrimeAnchor434 SP smallMod BP bigMod) //
      b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns oc.1 k oc.2} where
  toFun sf := ⟨(b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns sf.val.1 sf.val.2,
    ((fun g => Green64SmallHaar.residues (smallMod g) (J+ell) ((sf.val.1 0).1 g)),
     (fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((sf.val.1 0).2 g)))),
    b643_transport_anchor_allowed SP smallMod BP bigMod J ell m patterns k sf.val.1 sf.val.2 sf.property⟩
  invFun oc := ⟨(b643AllPrimeAnchoredStates434 SP smallMod BP bigMod J ell m patterns
    oc.val.1 k oc.val.2 oc.property,oc.val.1.2.2),
    b643_anchored_transport SP smallMod BP bigMod J ell m patterns oc.val.1 k oc.val.2 oc.property⟩
  left_inv sf := by
    apply Subtype.ext
    apply Prod.ext
    · exact b643_transport_reconstruct SP smallMod BP bigMod J ell m patterns k sf.val.1 sf.val.2 sf.property
    · rfl
  right_inv oc := by
    apply Subtype.ext
    apply Prod.ext
    · exact b643_anchored_readout SP smallMod BP bigMod J ell m patterns oc.val.1 k oc.val.2 oc.property
    · exact b643_anchored_initial SP smallMod BP bigMod J ell m patterns oc.val.1 k oc.val.2 oc.property
end Green64FullPhysicalE

end

end

