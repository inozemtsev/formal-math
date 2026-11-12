module

public import Green64.Library.Correlation.PhysicalArray

@[expose] public section

/-!
# Correlation / PhysicalReindex

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalReindex -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000
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


theorem b653_all_prime_offset_zero434 {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ) :
    b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k 0=0 := by
  simp [b643AllPrimeOffset434]

theorem b653_all_prime_offset_step434 {N : ℕ}
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) (k : ℤ) (i : Fin N) :
    b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k (i.val+1) =
      b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k i.val +
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
  unfold b643AllPrimeOffset434
  change (∑ j : Fin N,if j.val < i.val+1 then F j else 0)=_
  simp_rw [hm]
  rw [Finset.sum_add_distrib]
  simp [F]

/-- Exact positions of EVERY prefix, derived from the literal physical
steps, with no CRT averaging or uniqueness-of-primes assumption. -/
theorem b653_integer_array_positions434 (positions : Finset ℤ) {N : ℕ} (k : ℤ)
    (states : Fin (N+1) → B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (frames : Fin N → MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (hs : b653IntegerArraySteps434 SP smallMod BP bigMod J ell m patterns positions k states frames)
    (t : Fin (N+1)) :
    (states t).val.1.val = (states 0).val.1.val +
      b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns
        (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns (fun s => (states s).val.2) frames) k t.val := by
  let ω := b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns (fun s => (states s).val.2) frames
  induction t using Fin.induction with
  | zero =>
    change (states 0).val.1.val = (states 0).val.1.val +
      b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k 0
    rw [b653_all_prime_offset_zero434,add_zero]
  | succ i ih =>
    change (states i.castSucc).val.1.val = (states 0).val.1.val +
      b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k i.val at ih
    change (states i.succ).val.1.val = (states 0).val.1.val +
      b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k (i.val+1)
    rw [b653_all_prime_offset_step434]
    have hstep := hs i
    change (states i.succ).val.1.val = (states i.castSucc).val.1.val +
      physicalAlternatingSign i.val*k*(b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω i : ℤ) at hstep
    rw [hstep,ih,add_assoc]

/-- The endpoint positions return to n, but their marked lists are FREE. -/
def b653PhysicalArrayGuard434 (positions : Finset ℤ) {N : ℕ} (n k : ℤ)
    (sf : (Fin (N+1) → B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions) ×
      (Fin N → MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)) : Prop :=
  (sf.1 0).val.1.val=n ∧ (sf.1 (Fin.last N)).val.1.val=n ∧
  b653IntegerArraySteps434 SP smallMod BP bigMod J ell m patterns positions k sf.1 sf.2

/-- Window, exact signed return, and only the actual forced mark zeros. -/
def b653PhysicalPathGuard434 (positions : Finset ℤ) {N : ℕ} (n k : ℤ)
    (ω : B643AllPrimePath434 SP BP J ell m patterns N) : Prop :=
  (∀ t : Fin (N+1), n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val ∈ positions) ∧
  b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k N=0 ∧
  b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns ω k
    (b653IntegerAnchor434 SP smallMod BP bigMod n)

private theorem b653_physical_marks_allowed (positions : Finset ℤ) {N : ℕ} (n k : ℤ)
    (states : Fin (N+1) → B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (frames : Fin N → MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (hs : b653IntegerArraySteps434 SP smallMod BP bigMod J ell m patterns positions k states frames)
    (h0 : (states 0).val.1.val=n) :
    b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns
      (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns (fun t => (states t).val.2) frames) k
      (b653IntegerAnchor434 SP smallMod BP bigMod n) := by
  let ω := b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns (fun t => (states t).val.2) frames
  have hp (t : Fin (N+1)) : (states t).val.1.val = n+
      b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val := by
    simpa only [h0] using b653_integer_array_positions434 SP smallMod BP bigMod J ell m patterns positions k states frames hs t
  constructor
  · intro t g j
    change (n : ZMod (smallMod g ((ω.1 t g).val j))) +
      (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val :
        ZMod (smallMod g ((ω.1 t g).val j)))=0
    rw [← Int.cast_add,← hp t,← (states t).property.1 g ((ω.1 t g).val j)]
    exact Green64SmallHaar.marked_zero (smallMod g) (J+ell) ((states t).val.2.1 g) j
  · intro t g j
    change (n : ZMod (bigMod g ((ω.2.1 t g).val j))) +
      (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val :
        ZMod (bigMod g ((ω.2.1 t g).val j)))=0
    rw [← Int.cast_add,← hp t,← (states t).property.2 g ((ω.2.1 t g).val j)]
    exact Green64SmallHaar.marked_zero (bigMod g) (J+ell) ((states t).val.2.2 g) j

/-- Reconstruct the actual integer states at their signed prefix positions. -/
def b653IntegerStatesFrom434 (positions : Finset ℤ) {N : ℕ} (n k : ℤ)
    (ω : B643AllPrimePath434 SP BP J ell m patterns N)
    (hw : ∀ t : Fin (N+1), n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val ∈ positions)
    (ha : b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns ω k
      (b653IntegerAnchor434 SP smallMod BP bigMod n)) :
    Fin (N+1) → B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions :=
  fun t => ⟨(⟨n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val,hw t⟩,
    b643AllPrimeAnchoredStates434 SP smallMod BP bigMod J ell m patterns ω k
      (b653IntegerAnchor434 SP smallMod BP bigMod n) ha t),by
    constructor
    · intro g p
      change (n : ZMod (smallMod g p)) +
        (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val : ZMod (smallMod g p)) =
        ((n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val : ℤ) : ZMod (smallMod g p))
      rw [Int.cast_add]
    · intro g p
      change (n : ZMod (bigMod g p)) +
        (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val : ZMod (bigMod g p)) =
        ((n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val : ℤ) : ZMod (bigMod g p))
      rw [Int.cast_add]⟩

/-- Exact finite bijection: all source physical arrays that return to n
correspond to all complete-prime paths with their actual window/return
conditions. Final marks stay independent of the initial marks. -/
def b653PhysicalReturnEquiv434 (positions : Finset ℤ) (N : ℕ) (n k : ℤ) :
    {sf : ((Fin (N+1) → B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions) ×
      (Fin N → MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)) //
      b653PhysicalArrayGuard434 SP smallMod BP bigMod J ell m patterns positions n k sf} ≃
    {ω : B643AllPrimePath434 SP BP J ell m patterns N //
      b653PhysicalPathGuard434 SP smallMod BP bigMod J ell m patterns positions n k ω} where
  toFun sf := ⟨b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns
    (fun t => (sf.val.1 t).val.2) sf.val.2,by
    have hp (t : Fin (N+1)) := b653_integer_array_positions434 SP smallMod BP bigMod J ell m patterns
      positions k sf.val.1 sf.val.2 sf.property.2.2 t
    refine ⟨?_,?_,?_⟩
    · intro t
      rw [sf.property.1] at hp
      rw [← hp t]
      exact (sf.val.1 t).val.1.property
    · have hh := hp (Fin.last N)
      rw [sf.property.1,sf.property.2.1] at hh
      change n=n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns
        (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns (fun t => (sf.val.1 t).val.2) sf.val.2) k N at hh
      omega
    · exact b653_physical_marks_allowed SP smallMod BP bigMod J ell m patterns positions n k
        sf.val.1 sf.val.2 sf.property.2.2 sf.property.1⟩
  invFun ω := ⟨(b653IntegerStatesFrom434 SP smallMod BP bigMod J ell m patterns positions n k
    ω.val ω.property.1 ω.property.2.2,ω.val.2.2),by
    refine ⟨?_,?_,?_⟩
    · change n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω.val k 0=n
      rw [b653_all_prime_offset_zero434,add_zero]
    · change n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω.val k N=n
      rw [ω.property.2.1,add_zero]
    · intro i
      change n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω.val k (i.val+1) =
        n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω.val k i.val +
        physicalAlternatingSign i.val*k*(b643AllPrimeD434 SP smallMod BP bigMod J ell m patterns ω.val i : ℤ)
      rw [b653_all_prime_offset_step434,add_assoc]⟩
  left_inv sf := by
    apply Subtype.ext
    apply Prod.ext
    · funext t
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        have hp := b653_integer_array_positions434 SP smallMod BP bigMod J ell m patterns
          positions k sf.val.1 sf.val.2 sf.property.2.2 t
        rw [sf.property.1] at hp
        exact hp.symm
      · apply Prod.ext
        · funext g
          apply Subtype.ext
          apply Prod.ext
          · funext p
            have hp := b653_integer_array_positions434 SP smallMod BP bigMod J ell m patterns
              positions k sf.val.1 sf.val.2 sf.property.2.2 t
            rw [sf.property.1] at hp
            change (n : ZMod (smallMod g p)) +
              (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns
                (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns (fun s => (sf.val.1 s).val.2) sf.val.2) k t.val : ZMod (smallMod g p)) =
              Green64SmallHaar.residues (smallMod g) (J+ell) ((sf.val.1 t).val.2.1 g) p
            rw [← Int.cast_add,← hp]
            exact ((sf.val.1 t).property.1 g p).symm
          · rfl
        · funext g
          apply Subtype.ext
          apply Prod.ext
          · funext p
            have hp := b653_integer_array_positions434 SP smallMod BP bigMod J ell m patterns
              positions k sf.val.1 sf.val.2 sf.property.2.2 t
            rw [sf.property.1] at hp
            change (n : ZMod (bigMod g p)) +
              (b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns
                (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns (fun s => (sf.val.1 s).val.2) sf.val.2) k t.val : ZMod (bigMod g p)) =
              Green64SmallHaar.residues (bigMod g) (J+ell) ((sf.val.1 t).val.2.2 g) p
            rw [← Int.cast_add,← hp]
            exact ((sf.val.1 t).property.2 g p).symm
          · rfl
    · rfl
  right_inv ω := by
    apply Subtype.ext
    rfl
end Green64FullPhysicalE

end

end

