module

public import Green64.Library.Weights.Part002
public import Green64.Library.Weights.Part024

@[expose] public section

/-!
# Correlation / PhysicalENeverActive

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalENeverActive -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

private theorem filtered_indexed_bag
    {I U : Type} [DecidableEq I] [DecidableEq U]
    (s : Finset I) (f : I → U) (P : U → Prop) [DecidablePred P] :
    ((s.toList.map f : Multiset U).filter P) =
      ∑ i ∈ s,if P (f i) then ({f i}:Multiset U) else 0 := by
  rw [memory_bag_map_index_list s.toList (Finset.nodup_toList _) f]
  rw [Finset.toList_toFinset]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi,Multiset.filter_add,ih,Finset.sum_insert hi]
      simp [Multiset.filter_singleton]

/-- Every prime absent from BOTH active endpoints survives the original
E edge solely by the one physical translation. OLD promotion indices and
source stores are handled literally; repeated OLD atoms are allowed. -/
theorem source_original_PHYSICAL_E_never_active_translation434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x)
    (hc : OrientedBigEdgeLegal modulus M B x target shared sigma tau D step c)
    (background : Finset P)
    (hsource : ∀ j,x.1 j ∉ background) (htarget : ∀ j,target j ∉ background) :
    (physicalPendingMultiset modulus M B x sigma step c).filter
        (fun z => z.1 ∈ background) =
    ((fockMultiset x.2).map (translateAtom (modulus := modulus) step)).filter
        (fun z => z.1 ∈ background) := by
  classical
  have hselected (j : Fin x.2.1.val)
      (hj : j ∈ selectedOld modulus M B x c) : (x.2.2 j).1 ∉ background := by
    obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp hj
    rw [←hij,←hc.promoted_matches i]
    exact htarget (tau i)
  have hstore :
      ((newlyStored modulus M B x sigma step c : List (Atom P modulus)) : Multiset (Atom P modulus)).filter
        (fun z => z.1 ∈ background) = 0 := by
    unfold newlyStored
    rw [filtered_indexed_bag]
    apply Finset.sum_eq_zero
    intro j hj
    exact if_neg (hsource (sigma j))
  have hsurv :
      ((survivors modulus M B x step c : List (Atom P modulus)) : Multiset (Atom P modulus)).filter
        (fun z => z.1 ∈ background) =
      ∑ j : Fin x.2.1.val,
        if (x.2.2 j).1 ∈ background then
          ({translateAtom step (x.2.2 j)} : Multiset (Atom P modulus)) else 0 := by
    unfold survivors
    rw [filtered_indexed_bag]
    change (∑ j ∈ survivorIndices modulus M B x c,
      if (x.2.2 j).1 ∈ background then ({translateAtom step (x.2.2 j)}:Multiset (Atom P modulus)) else 0)=_
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hnot
    have hsel : j ∈ selectedOld modulus M B x c := by
      simpa [survivorIndices] using hnot
    exact if_neg (hselected j hsel)
  have hfull :
      ((fockMultiset x.2).map (translateAtom (modulus := modulus) step)).filter
          (fun z => z.1 ∈ background) =
      ∑ j : Fin x.2.1.val,
        if (x.2.2 j).1 ∈ background then
          ({translateAtom step (x.2.2 j)} : Multiset (Atom P modulus)) else 0 := by
    have hb := memory_clean_full_indexed_bag modulus x.2.2
      (translateAtom (modulus := modulus) step)
    have hb' : ((Finset.univ : Finset (Fin x.2.1.val)).toList.map
        (fun j => translateAtom step (x.2.2 j)) : Multiset (Atom P modulus)) =
        (fockMultiset x.2).map (translateAtom (modulus := modulus) step) := hb
    rw [←hb',filtered_indexed_bag]
    rfl
  unfold physicalPendingMultiset physicalPendingOutput
  rw [←Multiset.coe_add,Multiset.filter_add,hstore,add_zero,hsurv,hfull]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Literal source-oriented E output, with its actual auxiliary-D step.
The endpoint permutations, signs, source shift and complete witness are
retained. This is a structural background identity, not an operator norm. -/
theorem source_original_SOURCE_ORIENTED_E_background_translation434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hz : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z)
    (background : (g : BG) → Finset (BP g))
    (hsource : ∀ g j,(x.2 g).1 j ∉ background g)
    (htarget : ∀ g j,(z.2.2.1.bigChoice g).1 j ∉ background g) (g : BG) :
    (((sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z).2 g).2).filter
        (fun a => a.1 ∈ background g) =
    ((fockMultiset ((x.2 g).2)).map
      (translateAtom (modulus := bm g)
        (sourceOrientedStep SP sm BP bm J ell m cap (patterns z.1) z.2.1 x
          z.2.2.1.sigmaBig z.2.2.2.1 o k))).filter
        (fun a => a.1 ∈ background g) := by
  simpa only [sourceOrientedPhysicalOutput,fullPhysicalBranchOutput,
    bigGroupBranchOutput,physicalBranchOutput] using
    source_original_PHYSICAL_E_never_active_translation434 (bm g) (J+ell) (cap g)
      (x.2 g) (z.2.2.1.bigChoice g).1 (sourceBigShared J ell m (patterns z.1) g)
      (z.2.2.1.sigmaBig g) (z.2.2.1.tauBig g)
      (sourceOrientedPhysicalD SP sm BP bm J ell m cap (patterns z.1) z.2.1 x
        z.2.2.1.sigmaBig z.2.2.2.1)
      (sourceOrientedStep SP sm BP bm J ell m cap (patterns z.1) z.2.1 x
        z.2.2.1.sigmaBig z.2.2.2.1 o k)
      (z.2.2.1.bigChoice g).2 (hz.2.2.2.1 g) (background g) (hsource g) (htarget g)
end Green64Analytic.CorrelationSquare

end

end

