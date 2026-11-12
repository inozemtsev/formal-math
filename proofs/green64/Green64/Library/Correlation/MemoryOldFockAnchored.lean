module

public import Green64.Library.Correlation.MemoryOldFockDisintegration

@[expose] public section

/-!
# Correlation / MemoryOldFockAnchored

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryOldFockAnchored -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

def sourceOriginalMemoryTupleMultiset434
    {A U : Type} [Fintype A] (x : A → U) : Multiset U :=
  Finset.univ.val.map x

theorem source_original_memory_tuple_multiset_ofFn434
    {U : Type} (j : ℕ) (x : Fin j → U) :
    (List.ofFn x : Multiset U)=sourceOriginalMemoryTupleMultiset434 x := by
  simp only [sourceOriginalMemoryTupleMultiset434,List.ofFn_eq_map,
    Finset.val_univ_fin,Multiset.map_coe]

/-- The original input multiset is reconstructed exactly, including all
repeated values, from survivors and the ordered promoted vector. -/
theorem source_original_memory_OLD_input_reconstruction434
    {A U : Type} [Fintype A] (j : ℕ) (f : A ↪ Fin j) (x : Fin j → U) :
    sourceOriginalMemoryTupleMultiset434 x =
      sourceOriginalMemoryRemainder434 j f x +
      sourceOriginalMemoryTupleMultiset434 (fun a => x (f a)) := by
  classical
  let s : Finset (Fin j) := Finset.univ.image f
  have hs : (Finset.univ \ s).val+s.val=(Finset.univ : Finset (Fin j)).val := by
    rw [Finset.sdiff_val]
    exact Multiset.sub_add_cancel (Finset.val_le_iff.mpr (Finset.subset_univ _))
  have hh := congrArg (Multiset.map x) hs
  rw [Multiset.map_add] at hh
  have hsel : s.val.map x =
      sourceOriginalMemoryTupleMultiset434 (fun a => x (f a)) := by
    dsimp only [s,sourceOriginalMemoryTupleMultiset434]
    rw [← Finset.map_eq_image,Finset.map_val,Multiset.map_map]
    rfl
  rw [hsel] at hh
  exact hh.symm

/-- The exact OLD/Fock integral after imposing the literal promoted atom
vector. Arbitrary joint input/output tests are retained in F. -/
theorem source_original_memory_OLD_FOCK_anchored_disintegration434
    {A U : Type} [Fintype A] [Fintype U] (j : ℕ) (ha : Fintype.card A ≤ j)
    (mu : U → ℝ) (v0 : A → U) (F : Multiset U → Multiset U → ℝ) :
    (∑ x : Fin j → U,∑ f : A ↪ Fin j,
      ((∏ i : Fin j,mu (x i))/(j.factorial:ℝ))*
      (if (fun a => x (f a))=v0 then
        F (sourceOriginalMemoryTupleMultiset434 x)
          (sourceOriginalMemoryRemainder434 j f x) else 0)) =
    ((∏ a : A,mu (v0 a))/((j-Fintype.card A).factorial:ℝ))*
      ∑ u : Fin (j-Fintype.card A) → U,
        (∏ i : Fin (j-Fintype.card A),mu (u i))*
        F (sourceOriginalMemoryTupleMultiset434 u+sourceOriginalMemoryTupleMultiset434 v0)
          (sourceOriginalMemoryTupleMultiset434 u) := by
  classical
  have hh := source_original_memory_OLD_FOCK_injection_disintegration434 j ha mu
    (fun rem v => if v=v0 then
      F (rem+sourceOriginalMemoryTupleMultiset434 v) rem else 0)
  have hleft :
      (∑ x : Fin j → U,∑ f : A ↪ Fin j,
        ((∏ i : Fin j,mu (x i))/(j.factorial:ℝ))*
        (if (fun a => x (f a))=v0 then
          F (sourceOriginalMemoryTupleMultiset434 x)
            (sourceOriginalMemoryRemainder434 j f x) else 0)) =
      (∑ x : Fin j → U,∑ f : A ↪ Fin j,
        ((∏ i : Fin j,mu (x i))/(j.factorial:ℝ))*
        (if (fun a => x (f a))=v0 then
          F (sourceOriginalMemoryRemainder434 j f x+
            sourceOriginalMemoryTupleMultiset434 (fun a => x (f a)))
            (sourceOriginalMemoryRemainder434 j f x) else 0)) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro f hf
    rw [source_original_memory_OLD_input_reconstruction434 j f x]
  rw [hleft,hh]
  simp only [mul_ite,mul_zero,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  simp only [sourceOriginalMemoryTupleMultiset434,mul_assoc]
  rw [← Finset.mul_sum]
  ring

def sourceOriginalMemoryPromotedAnchor434
    {A P : Type} (modulus : P → ℕ) (step : ℤ) (target : A → P) :
    A → Green64Fock.Atom P modulus :=
  fun a => ⟨target a,((-step:ℤ):ZMod (modulus (target a)))⟩

/-- The anchor equality is precisely the original OLD prime matching
AND zero after translation, not an auxiliary replacement condition. -/
theorem source_original_memory_promoted_tests_iff_anchor434
    {A P : Type} (modulus : P → ℕ) (step : ℤ)
    (target : A → P) (v : A → Green64Fock.Atom P modulus) :
    ((∀ a,target a=(v a).1) ∧
      (∀ a,(v a).2+(step:ZMod (modulus (v a).1))=0)) ↔
      v=sourceOriginalMemoryPromotedAnchor434 modulus step target := by
  classical
  constructor
  · rintro ⟨hp,hz⟩
    funext a
    have hp' := hp a
    have hz' := hz a
    cases he : v a with
    | mk p r =>
      rw [he] at hp' hz'
      dsimp only at hp' hz'
      dsimp only [sourceOriginalMemoryPromotedAnchor434]
      rw [hp']
      have hr : r=((-step:ℤ):ZMod (modulus p)) := by
        simpa only [Int.cast_neg] using (eq_neg_of_add_eq_zero_left hz')
      exact congrArg (fun r : ZMod (modulus p) => (⟨p,r⟩ : Green64Fock.Atom P modulus)) hr
  · intro h
    subst v
    constructor
    · intro a;rfl
    · intro a
      dsimp only [sourceOriginalMemoryPromotedAnchor434]
      rw [Int.cast_neg]
      exact neg_add_cancel _

/-- A concrete original BIG OLD-sector sum: actual Fock mass, actual
survivor-plus-store output and the two literal promotion tests. All OLD
injections are eliminated with exactly 1/(j-a)! and the genuine promoted
prime product. The remaining legality/active factors may be retained
inside the arbitrary joint multiset test or supplied separately. -/
theorem source_original_memory_PHYSICAL_OLD_FOCK_joint_disintegration434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (M B j : ℕ) (hj : j ≤ B) (active target : Fin M → P)
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (stores promote : Finset (Fin M)) (ha : promote.card ≤ j)
    (mu : P → ℝ) (F : Multiset (Green64Fock.Atom P modulus) →
      Multiset (Green64Fock.Atom P modulus) → ℝ) :
    (∑ old : Fin j → Green64Fock.Atom P modulus,
      ∑ f : ↥promote ↪ Fin j,
      (Green64Fock.fockMass (fun z : Green64Fock.Atom P modulus => mu z.1)
        (⟨⟨j,Nat.lt_succ_iff.mpr hj⟩,old⟩ : Green64Fock.FockState _ B)) *
      (if (∀ a : ↥promote,target (tau a.val)=(old (f a)).1) ∧
          (∀ a : ↥promote,(old (f a)).2+
            (step:ZMod (modulus (old (f a)).1))=0) then
        F (Green64Fock.fockMultiset (⟨⟨j,Nat.lt_succ_iff.mpr hj⟩,old⟩ :
          Green64Fock.FockState _ B))
          (physicalPendingMultiset modulus M B
            (active,⟨⟨j,Nat.lt_succ_iff.mpr hj⟩,old⟩) sigma step ⟨stores,promote,f⟩)
        else 0)) =
    ((∏ a : ↥promote,mu (target (tau a.val)))/((j-promote.card).factorial:ℝ))*
      ∑ u : Fin (j-promote.card) → Green64Fock.Atom P modulus,
        (∏ i : Fin (j-promote.card),mu (u i).1)*
        F (sourceOriginalMemoryTupleMultiset434 u+
            sourceOriginalMemoryTupleMultiset434
              (sourceOriginalMemoryPromotedAnchor434 modulus step
                (fun a : ↥promote => target (tau a.val))))
          ((sourceOriginalMemoryTupleMultiset434 u).map
              (Green64PhysicalEdge.translateAtom step)+
            stores.val.map (fun i => (⟨active (sigma i),
              (step:ZMod (modulus (active (sigma i))))⟩ : Green64Fock.Atom P modulus))) := by
  classical
  have ha' : Fintype.card ↥promote ≤ j := by simpa using ha
  have hh := source_original_memory_OLD_FOCK_anchored_disintegration434 j ha'
    (fun z : Green64Fock.Atom P modulus => mu z.1)
    (sourceOriginalMemoryPromotedAnchor434 modulus step
      (fun a : ↥promote => target (tau a.val)))
    (fun old rem => F old (rem.map (Green64PhysicalEdge.translateAtom step)+
      stores.val.map (fun i => (⟨active (sigma i),
        (step:ZMod (modulus (active (sigma i))))⟩ : Green64Fock.Atom P modulus))))
  let T (r : ℕ) : ℝ := ∑ u : Fin r → Green64Fock.Atom P modulus,
    (∏ i : Fin r,mu (u i).1)*
      F (sourceOriginalMemoryTupleMultiset434 u+
          sourceOriginalMemoryTupleMultiset434
            (sourceOriginalMemoryPromotedAnchor434 modulus step
              (fun a : ↥promote => target (tau a.val))))
        ((sourceOriginalMemoryTupleMultiset434 u).map (Green64PhysicalEdge.translateAtom step)+
          stores.val.map (fun i => (⟨active (sigma i),
            (step:ZMod (modulus (active (sigma i))))⟩ : Green64Fock.Atom P modulus)))
  change _ = ((∏ a : ↥promote,mu (target (tau a.val)))/
    ((j-Fintype.card ↥promote).factorial:ℝ))*T (j-Fintype.card ↥promote) at hh
  rw [Fintype.card_coe] at hh
  dsimp only [T] at hh
  simp only [Green64Fock.fockMass,Green64Fock.fockMultiset,
    source_original_memory_tuple_multiset_ofFn434,
    source_original_memory_actual_output_remainder434,
    source_original_memory_promoted_tests_iff_anchor434,
    sourceOriginalMemoryPromotedAnchor434] at hh ⊢
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro old hold
    apply Finset.sum_congr rfl
    intro f hf
    split_ifs <;> rfl
end Green64Analytic.CorrelationSquare

end

end

