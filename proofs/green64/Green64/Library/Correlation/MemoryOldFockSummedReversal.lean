module

public import Green64.Library.Correlation.MemoryOldFockAnchored

@[expose] public section

/-!
# Correlation / MemoryOldFockSummedReversal

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryOldFockSummedReversal -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

def sourceOriginalMemoryStoredMultiset434 (M : ℕ) (active : Fin M → P)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ) (stores : Finset (Fin M)) :
    Multiset (Green64Fock.Atom P modulus) :=
  stores.val.map (fun i => ⟨active (sigma i),(step:ZMod (modulus (active (sigma i))))⟩)

theorem source_original_memory_anchor_stored_multiset434
    (M : ℕ) (target : Fin M → P) (tau : Equiv.Perm (Fin M))
    (step : ℤ) (promote : Finset (Fin M)) :
    sourceOriginalMemoryTupleMultiset434
      (sourceOriginalMemoryPromotedAnchor434 modulus step
        (fun a : ↥promote => target (tau a.val))) =
    sourceOriginalMemoryStoredMultiset434 modulus M target tau (-step) promote := by
  classical
  have hh := Finset.univ_val_map_subtype_restrict
    (fun i : Fin M => (⟨target (tau i),((-step:ℤ):ZMod (modulus (target (tau i))))⟩ :
      Green64Fock.Atom P modulus)) (fun i => i ∈ promote)
  simp only [Subtype.restrict_def,Function.comp_def,Finset.filter_univ_mem] at hh
  convert hh using 1 <;> congr <;> exact Subsingleton.elim _ _

/-- Literal OLD-sector joint sum, including every actual retrieval
injection and the source 1/j! Fock measure. -/
def sourceOriginalMemoryPhysicalOldJoint434
    (M B j : ℕ) (hj : j ≤ B) (active target : Fin M → P)
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (stores promote : Finset (Fin M)) (mu : P → ℝ)
    (F : Multiset (Green64Fock.Atom P modulus) → Multiset (Green64Fock.Atom P modulus) → ℝ) : ℝ :=
  ∑ old : Fin j → Green64Fock.Atom P modulus,
    ∑ f : ↥promote ↪ Fin j,
    Green64Fock.fockMass (fun z : Green64Fock.Atom P modulus => mu z.1)
      (⟨⟨j,Nat.lt_succ_iff.mpr hj⟩,old⟩ : Green64Fock.FockState _ B) *
    (if (∀ a : ↥promote,target (tau a.val)=(old (f a)).1) ∧
        (∀ a : ↥promote,(old (f a)).2+(step:ZMod (modulus (old (f a)).1))=0) then
      F (Green64Fock.fockMultiset (⟨⟨j,Nat.lt_succ_iff.mpr hj⟩,old⟩ :
        Green64Fock.FockState _ B))
        (physicalPendingMultiset modulus M B
          (active,⟨⟨j,Nat.lt_succ_iff.mpr hj⟩,old⟩) sigma step ⟨stores,promote,f⟩)
      else 0)

theorem source_original_memory_PHYSICAL_OLD_joint_core434
    (M B n : ℕ) (active target : Fin M → P)
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (stores promote : Finset (Fin M)) (hj : n+promote.card ≤ B)
    (mu : P → ℝ)
    (F : Multiset (Green64Fock.Atom P modulus) → Multiset (Green64Fock.Atom P modulus) → ℝ) :
    sourceOriginalMemoryPhysicalOldJoint434 modulus M B (n+promote.card) hj
      active target sigma tau step stores promote mu F =
    ((∏ a : ↥promote,mu (target (tau a.val)))/(n.factorial:ℝ))*
      ∑ u : Fin n → Green64Fock.Atom P modulus,(∏ i : Fin n,mu (u i).1)*
        F (sourceOriginalMemoryTupleMultiset434 u+
            sourceOriginalMemoryStoredMultiset434 modulus M target tau (-step) promote)
          ((sourceOriginalMemoryTupleMultiset434 u).map (translateAtom step)+
            sourceOriginalMemoryStoredMultiset434 modulus M active sigma step stores) := by
  have hh := source_original_memory_PHYSICAL_OLD_FOCK_joint_disintegration434
    modulus M B (n+promote.card) hj active target sigma tau step stores promote (by omega) mu F
  let T (r : ℕ) : ℝ :=
    ∑ u : Fin r → Green64Fock.Atom P modulus,(∏ i : Fin r,mu (u i).1)*
      F (sourceOriginalMemoryTupleMultiset434 u+
          sourceOriginalMemoryStoredMultiset434 modulus M target tau (-step) promote)
        ((sourceOriginalMemoryTupleMultiset434 u).map (translateAtom step)+
          sourceOriginalMemoryStoredMultiset434 modulus M active sigma step stores)
  rw [source_original_memory_anchor_stored_multiset434] at hh
  change _ = ((∏ a : ↥promote,mu (target (tau a.val)))/
    ((n+promote.card-promote.card).factorial:ℝ))*T (n+promote.card-promote.card) at hh
  rw [Nat.add_sub_cancel_right] at hh
  exact hh

private def atomShiftEquiv (step : ℤ) : Green64Fock.Atom P modulus ≃ Green64Fock.Atom P modulus where
  toFun := translateAtom step
  invFun := translateAtom (-step)
  left_inv := translateAtom_back step
  right_inv := by intro z;simpa only [neg_neg] using translateAtom_back (-step) z

private theorem tuple_shift (n : ℕ) (step : ℤ)
    (u : Fin n → Green64Fock.Atom P modulus) :
    sourceOriginalMemoryTupleMultiset434 (fun i => translateAtom step (u i)) =
      (sourceOriginalMemoryTupleMultiset434 u).map (translateAtom step) := by
  simp only [sourceOriginalMemoryTupleMultiset434,Multiset.map_map,Function.comp_def]

private theorem multiset_shift_back (step : ℤ) (u : Multiset (Green64Fock.Atom P modulus)) :
    (u.map (translateAtom step)).map (translateAtom (-step))=u := by
  simp only [Multiset.map_map,Function.comp_def,translateAtom_back,Multiset.map_id']

/-- Actual summed OLD/Fock detailed balance for a fixed physical
active/permutation/store/promote frame. This is an equality of the
complete OLD and injection sums, not merely a joint-integrand ratio.
The reverse output is compared as a multiset, with all factorial and
equal-atom multiplicities already accounted for. -/
theorem source_original_memory_PHYSICAL_OLD_FOCK_summed_reversal434
    (M B n : ℕ) (active target : Fin M → P)
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (stores promote : Finset (Fin M))
    (hj : n+promote.card ≤ B) (hj' : n+stores.card ≤ B)
    (mu : P → ℝ)
    (F : Multiset (Green64Fock.Atom P modulus) → Multiset (Green64Fock.Atom P modulus) → ℝ) :
    sourceOriginalMemoryPhysicalOldJoint434 modulus M B (n+promote.card) hj
      active target sigma tau step stores promote mu F *
      (∏ a : ↥stores,mu (active (sigma a.val))) =
    sourceOriginalMemoryPhysicalOldJoint434 modulus M B (n+stores.card) hj'
      target active tau sigma (-step) promote stores mu (fun y x => F x y) *
      (∏ a : ↥promote,mu (target (tau a.val))) := by
  classical
  rw [source_original_memory_PHYSICAL_OLD_joint_core434,
    source_original_memory_PHYSICAL_OLD_joint_core434]
  simp only [neg_neg]
  have he :
      (∑ u : Fin n → Green64Fock.Atom P modulus,(∏ i : Fin n,mu (u i).1)*
        F (sourceOriginalMemoryTupleMultiset434 u+
            sourceOriginalMemoryStoredMultiset434 modulus M target tau (-step) promote)
          ((sourceOriginalMemoryTupleMultiset434 u).map (translateAtom step)+
            sourceOriginalMemoryStoredMultiset434 modulus M active sigma step stores)) =
      (∑ v : Fin n → Green64Fock.Atom P modulus,(∏ i : Fin n,mu (v i).1)*
        F ((sourceOriginalMemoryTupleMultiset434 v).map (translateAtom (-step))+
            sourceOriginalMemoryStoredMultiset434 modulus M target tau (-step) promote)
          (sourceOriginalMemoryTupleMultiset434 v+
            sourceOriginalMemoryStoredMultiset434 modulus M active sigma step stores)) := by
    let e := Equiv.arrowCongr (Equiv.refl (Fin n)) (atomShiftEquiv modulus step)
    apply Fintype.sum_equiv e
    intro u
    change (∏ i : Fin n,mu (u i).1)*_ =
      (∏ i : Fin n,mu (translateAtom step (u i)).1)*
        F ((sourceOriginalMemoryTupleMultiset434 (fun i => translateAtom step (u i))).map
            (translateAtom (-step))+_)
          (sourceOriginalMemoryTupleMultiset434 (fun i => translateAtom step (u i))+_)
    rw [tuple_shift,multiset_shift_back]
    rfl
  rw [he]
  ring
end Green64Analytic.CorrelationSquare

end

end

