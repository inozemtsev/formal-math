module

public import Green64.Library.Weights.Part009
public import Green64.Library.Weights.Part002

@[expose] public section

/-!
# Correlation / PhysicalPermutationLegalCounterexample

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalPermutationLegalCounterexample -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

namespace PermutationCounterexample

def primeMod (p : Fin 2) : ℕ :=
  if p = 0 then 2 else 3

instance (p : Fin 2) : NeZero (primeMod p) := by
  unfold primeMod
  split_ifs <;> infer_instance

def vacuumBig :
    BigState primeMod 2 0 :=
  (fun i => i, Green64Fock.vacuumState
    (Green64Fock.Atom (Fin 2) primeMod) 0)

def emptyBigChoice :
    BigEdgeChoice primeMod 2 0 vacuumBig :=
  (∅, ⟨∅, ⟨
    (fun i => by cases i with | mk val h => simp at h),
    (by intro a b h; cases a with | mk val ha => simp at ha)
  ⟩⟩)

end PermutationCounterexample

open PermutationCounterexample

/-- The actual BIG physical E branch accepts the vacuum-to-vacuum
transition whose shared label fails the oriented source comparison.
The two numerical labels are distinct primes 2 and 3. -/
theorem physical_big_edge_legal_but_not_oriented :
    PhysicalEdgeLegal primeMod 2 0 vacuumBig (fun i => i)
      {0} (Equiv.swap 0 1) (Equiv.refl _) 2 2
      emptyBigChoice ∧
    ¬ orientedBigSharedCopy vacuumBig.1 (fun i => i)
      {0} (Equiv.swap 0 1) (Equiv.refl _) := by
  constructor
  · constructor
    · intro i hi; rfl
    · simp [emptyBigChoice]
    · simp [emptyBigChoice]
    · intro ⟨val, h⟩
      change val ∈ (∅ : Finset (Fin 2)) at h
      simp at h
    · intro ⟨val, h⟩
      change val ∈ (∅ : Finset (Fin 2)) at h
      simp at h
    · intro ⟨val, h⟩
      change val ∈ (∅ : Finset (Fin 2)) at h
      simp at h
    · intro i hi; simp [emptyBigChoice] at hi
    · simp [pending_output_length, vacuumBig, emptyBigChoice]
  · simp [orientedBigSharedCopy, vacuumBig]

end Green64FullPhysicalE

end

