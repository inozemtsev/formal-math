module

public import Green64.Library.Correlation.PhysicalENeverActive
public import Green64.Library.Correlation.Part006

@[expose] public section

/-!
# Correlation / PhysicalEInventory

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalEInventory -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Numerical inventory with every active and pending multiplicity. -/
def sourceOriginalBigInventory434 {P : Type} (modulus : P → ℕ)
    (M : ℕ) (active : Fin M → P) (pending : Multiset (Atom P modulus)) :
    Multiset ℕ :=
  (∑ j : Fin M, ({modulus (active j)} : Multiset ℕ)) +
    pending.map (fun z => modulus z.1)

theorem source_original_inventory_ofFn_bag434 {U : Type} (n : ℕ) (f : Fin n → U) :
    (List.ofFn f : Multiset U) = ∑ j : Fin n, ({f j} : Multiset U) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ,Fin.sum_univ_succ,←ih]
      rfl

private theorem indexed_bag {I U : Type} [DecidableEq I]
    (s : Finset I) (f : I → U) :
    (s.toList.map f : Multiset U) = ∑ j ∈ s, ({f j} : Multiset U) := by
  exact (memory_bag_map_index_list s.toList (Finset.nodup_toList _) f).trans
    (by rw [Finset.toList_toFinset])

/-- Literal E cannot duplicate source inventory: all output labels are
source labels or true fresh targets. This holds on the entire original
carrier, including repeated atoms, before any distinctness assumption. -/
theorem source_original_PHYSICAL_E_inventory_le434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x)
    (hc : OrientedBigEdgeLegal modulus M B x target shared sigma tau D step c) :
    sourceOriginalBigInventory434 modulus M target
        (physicalPendingMultiset modulus M B x sigma step c) ≤
      sourceOriginalBigInventory434 modulus M x.1 (fockMultiset x.2) +
        ∑ j ∈ orientedFresh M shared c.2.1,
          ({modulus (target (tau j))} : Multiset ℕ) := by
  let a : Fin M → Multiset ℕ := fun j => {modulus (x.1 (sigma j))}
  let t : Fin M → Multiset ℕ := fun j => {modulus (target (tau j))}
  let o : Fin x.2.1.val → Multiset ℕ := fun j => {modulus (x.2.2 j).1}
  have hpart :
      (∑ j ∈ orientedFresh M shared c.2.1,t j) +
        (∑ j ∈ c.2.1,t j) + (∑ j ∈ shared,t j) = ∑ j,t j := by
    rw [orientedFresh,Finset.sum_sdiff hc.promotes_unshared]
    exact Finset.sum_sdiff (Finset.subset_univ shared)
  have hprom : (∑ j ∈ c.2.1,t j) = ∑ j ∈ selectedOld modulus M B x c,o j := by
    rw [selectedOld,Finset.sum_image (fun i hi j hj h => c.2.2.injective h)]
    rw [←Finset.sum_attach c.2.1]
    change (∑ j : ↥c.2.1,t j.val) = ∑ j : ↥c.2.1,o (c.2.2 j)
    apply Finset.sum_congr rfl
    intro j hj
    simp only [t,o,hc.promoted_matches j]
  have hshared : (∑ j ∈ shared,t j) = ∑ j ∈ shared,a j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [t,a,←hc.shared_copy j hj]
  have hold : (fockMultiset x.2).map (fun z => modulus z.1) = ∑ j,o j := by
    unfold fockMultiset
    rw [Multiset.map_coe,List.map_ofFn,source_original_inventory_ofFn_bag434]
    rfl
  have hpend :
      (physicalPendingMultiset modulus M B x sigma step c).map
          (fun z => modulus z.1) =
        (∑ j ∈ survivorIndices modulus M B x c,o j) +
        (∑ j ∈ c.1,a j) := by
    simp only [physicalPendingMultiset,physicalPendingOutput,←Multiset.coe_add,
      Multiset.map_add,survivors,newlyStored,Multiset.map_coe,List.map_map,
      Function.comp_def,translateAtom]
    rw [indexed_bag,indexed_bag]
  have hsurv : (∑ j ∈ survivorIndices modulus M B x c,o j) +
      (∑ j ∈ selectedOld modulus M B x c,o j) = ∑ j,o j :=
    Finset.sum_sdiff (Finset.subset_univ _)
  have hd : Disjoint shared c.1 := by
    apply Finset.disjoint_left.mpr
    intro j hj hjc
    exact (Finset.mem_sdiff.mp (hc.stores_unshared hjc)).2 hj
  have ha : (∑ j ∈ shared,a j) + (∑ j ∈ c.1,a j) ≤ ∑ j,a j := by
    rw [←Finset.sum_union hd]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hta : (∑ j : Fin M,({modulus (target j)}:Multiset ℕ)) = ∑ j,t j :=
    (Equiv.sum_comp tau (fun j => ({modulus (target j)}:Multiset ℕ))).symm
  have haa : (∑ j : Fin M,({modulus (x.1 j)}:Multiset ℕ)) = ∑ j,a j :=
    (Equiv.sum_comp sigma (fun j => ({modulus (x.1 j)}:Multiset ℕ))).symm
  unfold sourceOriginalBigInventory434
  rw [hpend,hold,hta,haa,←hpart,hprom,hshared]
  calc
    _ = ((∑ j ∈ shared,a j)+(∑ j ∈ c.1,a j)) +
          ((∑ j ∈ survivorIndices modulus M B x c,o j)+
           (∑ j ∈ selectedOld modulus M B x c,o j)) +
          (∑ j ∈ orientedFresh M shared c.2.1,t j) := by ac_rfl
    _ ≤ (∑ j,a j) + (∑ j,o j) +
          (∑ j ∈ orientedFresh M shared c.2.1,t j) := by
      rw [hsurv]
      exact add_le_add (add_le_add ha le_rfl) le_rfl
end Green64Analytic.CorrelationSquare

end

end

