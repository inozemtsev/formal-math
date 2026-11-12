module

public import Green64.Library.Correlation.PhysicalEInventory
public import Green64.Library.Correlation.PhysicalGhostSaturated
public import Green64.Library.Correlation.Part008
public import Green64.Library.Correlation.B26FrozenCleanPhysicalFourier

@[expose] public section

/-!
# Correlation / Part028

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalReachable -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 18000000

theorem source_original_inventory_indexed_bag434 {I U : Type} [DecidableEq I]
    (s : Finset I) (f : I → U) :
    (s.toList.map f : Multiset U) = ∑ j ∈ s, ({f j} : Multiset U) :=
  (memory_bag_map_index_list s.toList (Finset.nodup_toList _) f).trans
    (by rw [Finset.toList_toFinset])

theorem source_original_inventory_flatMap_bag434
    {I U : Type} [Fintype I] [DecidableEq I] (f : I → List U) :
    ((Finset.univ : Finset I).toList.flatMap f : Multiset U) =
      ∑ i, (f i : Multiset U) := by
  have h (l : List I) : (l.flatMap f : Multiset U) =
      (l.map (fun i => (f i : Multiset U))).sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.flatMap_cons,←Multiset.coe_add,
        List.map_cons,List.sum_cons,ih]
  rw [h,←List.sum_toFinset _ (Finset.nodup_toList _),Finset.toList_toFinset]

/-- A genuine numerical no-repeat/seen sector; all ambient repeated-atom
Fock states remain in the underlying carrier. -/
def sourceOriginalInventoryValid434 (inventory : Multiset ℕ) (seen : Finset ℕ) : Prop :=
  inventory.Nodup ∧ ∀ p ∈ inventory,p ∈ seen

theorem source_original_inventory_fresh_preserves434
    (a b : Multiset ℕ) (seen : Finset ℕ) (births : List ℕ)
    (h : sourceOriginalInventoryValid434 a seen)
    (hn : births.Nodup) (hd : Disjoint seen births.toFinset)
    (hle : b ≤ a + (births : Multiset ℕ)) :
    sourceOriginalInventoryValid434 b (seen ∪ births.toFinset) := by
  have hadd : (a + (births : Multiset ℕ)).Nodup := by
    apply Multiset.nodup_add.mpr
    refine ⟨h.1,hn,Multiset.disjoint_left.mpr ?_⟩
    intro p hp hb
    exact (Finset.disjoint_left.mp hd (h.2 p hp)) (List.mem_toFinset.mpr hb)
  refine ⟨Multiset.nodup_of_le hle hadd,?_⟩
  intro p hp
  rcases Multiset.mem_add.mp (Multiset.mem_of_le hle hp) with ha|hb
  · exact Finset.mem_union_left _ (h.2 p ha)
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hb)

theorem source_original_afterGhost_inventory_le434
    {U : Type} (old : List U) (A : Finset (Fin old.length))
    {b : ℕ} (fresh : Fin b → U) :
    (afterGhost old A fresh : Multiset U) ≤
      (old : Multiset U) + (List.ofFn fresh : Multiset U) := by
  unfold afterGhost
  rw [←Multiset.coe_add]
  apply add_le_add _ le_rfl
  apply Multiset.coe_le.mpr
  have h := (List.filter_sublist (l := List.finRange old.length)
    (p := fun j => decide (j ∉ A))).map old.get
  rw [List.map_get_finRange] at h
  exact h.subperm

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

def sourceOriginalPhysicalInventory434
    (y : FullPhysicalOutput SP sm BP bm M) : Multiset ℕ :=
  ∑ g,sourceOriginalBigInventory434 (bm g) M (y.2 g).1 (y.2 g).2

def sourceOriginalPhysicalReachable434
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ) : Prop :=
  sourceOriginalInventoryValid434 (sourceOriginalPhysicalInventory434 SP sm BP bm M y) seen

/-- Global numerical inventory control for every actual nonzero G witness,
retaining simultaneous births across all groups. -/
theorem source_original_PHYSICAL_G_inventory_le434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (ht : physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c ≠ 0) :
    sourceOriginalPhysicalInventory434 SP sm BP bm M
        (physicalFockProjection SP sm BP bm M cap y) ≤
      sourceOriginalPhysicalInventory434 SP sm BP bm M
        (physicalFockProjection SP sm BP bm M cap x) +
      (physicalGhostFreshBirths SP sm BP bm M cap x c : Multiset ℕ) := by
  obtain ⟨hactive,hout⟩ := physical_nonzero_ghost_witness_is_operational
    SP sm BP bm M cap q rho N i V mu x y c ht
  rw [physicalGhostFreshBirths,source_original_inventory_flatMap_bag434]
  unfold sourceOriginalPhysicalInventory434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g hg
  change sourceOriginalBigInventory434 (bm g) M (y.2 g).1 (fockMultiset (y.2 g).2) ≤
    sourceOriginalBigInventory434 (bm g) M (x.2 g).1 (fockMultiset (x.2 g).2) +
    (((List.ofFn (c g).2.2).map (fun z => bm g z.1) : List ℕ) : Multiset ℕ)
  unfold sourceOriginalBigInventory434
  rw [←hactive.2 g]
  have hm := Multiset.map_le_map (f := fun z : Atom (BP g) (bm g) => bm g z.1)
    (source_original_afterGhost_inventory_le434
      (fockToList (x.2 g).2) (c g).1.1 (c g).2.2)
  rw [hout g,Multiset.map_add,Multiset.map_coe] at hm
  change (fockMultiset (y.2 g).2).map (fun z => bm g z.1) ≤
    (fockMultiset (x.2 g).2).map (fun z => bm g z.1) +
    ((List.ofFn (c g).2.2).map (fun z => bm g z.1) : Multiset ℕ) at hm
  simpa only [add_assoc] using add_le_add (le_refl
    (∑ j : Fin M,({bm g ((x.2 g).1 j)} : Multiset ℕ))) hm

theorem source_original_PHYSICAL_G_reachable434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen)
    (he : physicalGhostBatchEligible SP sm BP bm M cap x seen c)
    (ht : physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c ≠ 0) :
    sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap y)
      (seen ∪ (physicalGhostFreshBirths SP sm BP bm M cap x c).toFinset) :=
  source_original_inventory_fresh_preserves434 _ _ seen _ hx he.1 he.2
    (source_original_PHYSICAL_G_inventory_le434 SP sm BP bm M cap q rho N i V mu x y c ht)

variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Actual source E, with both endpoint permutations, has one global
inventory inclusion. No cardinality or branch-count factor is introduced. -/
theorem source_original_SOURCE_ORIENTED_E_inventory_le434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hz : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z) :
    sourceOriginalPhysicalInventory434 SP sm BP bm (J+ell)
      (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z) ≤
    sourceOriginalPhysicalInventory434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) +
      (orientedEFreshBirths SP sm BP bm J ell m cap patterns z : Multiset ℕ) := by
  rw [orientedEFreshBirths,source_original_inventory_flatMap_bag434]
  simp_rw [source_original_inventory_indexed_bag434]
  unfold sourceOriginalPhysicalInventory434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g hg
  exact source_original_PHYSICAL_E_inventory_le434 (bm g) (J+ell) (cap g)
    (x.2 g) (z.2.2.1.bigChoice g).1
    (sourceBigShared J ell m (patterns z.1) g)
    (z.2.2.1.sigmaBig g) (z.2.2.1.tauBig g)
    (sourceOrientedPhysicalD SP sm BP bm J ell m cap
      (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1)
    (sourceOrientedStep SP sm BP bm J ell m cap
      (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1 o k)
    (z.2.2.1.bigChoice g).2 (hz.2.2.2.1 g)

theorem source_original_SOURCE_ORIENTED_E_reachable434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (hz : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z)
    (he : orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z) :
    sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
      (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset) :=
  source_original_inventory_fresh_preserves434 _ _ seen _ hx he.1 he.2
    (source_original_SOURCE_ORIENTED_E_inventory_le434 SP sm BP bm cap J ell m patterns x o k z hz)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalEReindex -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)

def sourceOriginalEReindexState434
    (x : BigState modulus M B) (e : Equiv.Perm (Fin x.2.1.val)) : BigState modulus M B :=
  (x.1,⟨x.2.1,fun j => x.2.2 (e j)⟩)

/-- The genuine OLD injection is transported, while stores and target
promotion slots are unchanged. This is an equivalence of all choices,
also on repeated-atom sectors. -/
def sourceOriginalEChoiceReindex434
    (x : BigState modulus M B) (e : Equiv.Perm (Fin x.2.1.val)) :
    BigEdgeChoice modulus M B x ≃
      BigEdgeChoice modulus M B (sourceOriginalEReindexState434 modulus M B x e) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.sigmaCongrRight
    (fun _ => Equiv.embeddingCongr (Equiv.refl _) e.symm))

theorem source_original_E_reindex_selected434
    (x : BigState modulus M B) (e : Equiv.Perm (Fin x.2.1.val))
    (c : BigEdgeChoice modulus M B x) (j : Fin x.2.1.val) :
    j ∈ selectedOld modulus M B (sourceOriginalEReindexState434 modulus M B x e)
      (sourceOriginalEChoiceReindex434 modulus M B x e c) ↔
    e j ∈ selectedOld modulus M B x c := by
  constructor
  · intro h
    obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp h
    apply Finset.mem_image.mpr
    refine ⟨i,hi,?_⟩
    change e.symm (c.2.2 i)=j at hij
    simpa only [Equiv.apply_symm_apply] using congrArg e hij
  · intro h
    obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp h
    apply Finset.mem_image.mpr
    refine ⟨i,hi,?_⟩
    change e.symm (c.2.2 i)=j
    simpa only [Equiv.symm_apply_apply] using congrArg e.symm hij

theorem source_original_E_reindex_pending434
    (x : BigState modulus M B) (e : Equiv.Perm (Fin x.2.1.val))
    (sigma : Equiv.Perm (Fin M)) (step : ℤ) (c : BigEdgeChoice modulus M B x) :
    physicalPendingMultiset modulus M B (sourceOriginalEReindexState434 modulus M B x e)
      sigma step (sourceOriginalEChoiceReindex434 modulus M B x e c) =
    physicalPendingMultiset modulus M B x sigma step c := by
  unfold physicalPendingMultiset physicalPendingOutput
  rw [←Multiset.coe_add,←Multiset.coe_add]
  congr 1
  unfold survivors
  rw [source_original_inventory_indexed_bag434,source_original_inventory_indexed_bag434]
  apply Finset.sum_equiv e
  · intro j
    constructor
    · intro hj
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hs =>
        (Finset.mem_sdiff.mp hj).2
          ((source_original_E_reindex_selected434 modulus M B x e c j).mpr hs)⟩
    · intro hj
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hs =>
        (Finset.mem_sdiff.mp hj).2
          ((source_original_E_reindex_selected434 modulus M B x e c j).mp hs)⟩
  · intro j hj
    rfl

theorem source_original_E_reindex_fock434
    (x : BigState modulus M B) (e : Equiv.Perm (Fin x.2.1.val)) :
    fockMultiset (sourceOriginalEReindexState434 modulus M B x e).2 =
      fockMultiset x.2 := by
  exact Multiset.coe_eq_coe.mpr (e.ofFn_comp_perm x.2.2)

theorem source_original_E_reindex_legal434
    (x : BigState modulus M B) (e : Equiv.Perm (Fin x.2.1.val))
    (target : Fin M → P) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) :
    OrientedBigEdgeLegal modulus M B
      (sourceOriginalEReindexState434 modulus M B x e)
      target shared sigma tau D step
      (sourceOriginalEChoiceReindex434 modulus M B x e c) ↔
    OrientedBigEdgeLegal modulus M B x target shared sigma tau D step c := by
  have hp := source_original_E_reindex_pending434 modulus M B x e sigma step c
  have hlen := (Multiset.coe_eq_coe.mp hp).length_eq
  constructor
  · intro h
    refine ⟨h.shared_copy,h.stores_unshared,h.promotes_unshared,?_,?_,?_,
      h.stored_not_dividing,?_⟩
    · intro j
      have hh := h.promoted_matches j
      change target (tau j.val) = (x.2.2 (e (e.symm (c.2.2 j)))).1 at hh
      simpa only [Equiv.apply_symm_apply] using hh
    · intro j
      have hh := h.promoted_zero j
      change (x.2.2 (e (e.symm (c.2.2 j)))).2 +
        (step : ZMod (modulus (x.2.2 (e (e.symm (c.2.2 j)))).1)) = 0 at hh
      exact Eq.mp (congrArg (fun a : Fin x.2.1.val =>
        (x.2.2 a).2 + (step : ZMod (modulus (x.2.2 a).1)) = 0)
        (e.apply_symm_apply (c.2.2 j))) hh
    · intro j
      have hh := h.promoted_not_dividing j
      change ¬modulus (x.2.2 (e (e.symm (c.2.2 j)))).1 ∣ D at hh
      simpa only [Equiv.apply_symm_apply] using hh
    · exact hlen ▸ h.output_within_cutoff
  · intro h
    refine ⟨h.shared_copy,h.stores_unshared,h.promotes_unshared,?_,?_,?_,
      h.stored_not_dividing,?_⟩
    · intro j
      change target (tau j.val) = (x.2.2 (e (e.symm (c.2.2 j)))).1
      simpa only [Equiv.apply_symm_apply] using h.promoted_matches j
    · intro j
      change (x.2.2 (e (e.symm (c.2.2 j)))).2 +
        (step : ZMod (modulus (x.2.2 (e (e.symm (c.2.2 j)))).1)) = 0
      exact Eq.mpr (congrArg (fun a : Fin x.2.1.val =>
        (x.2.2 a).2 + (step : ZMod (modulus (x.2.2 a).1)) = 0)
        (e.apply_symm_apply (c.2.2 j))) (h.promoted_zero j)
    · intro j
      change ¬modulus (x.2.2 (e (e.symm (c.2.2 j)))).1 ∣ D
      simpa only [Equiv.apply_symm_apply] using h.promoted_not_dividing j
    · exact hlen.symm ▸ h.output_within_cutoff

theorem source_original_E_reindex_oldZero434
    (x : BigState modulus M B) (e : Equiv.Perm (Fin x.2.1.val)) :
    oldZeroCount (sourceOriginalEReindexState434 modulus M B x e).2 =
      oldZeroCount x.2 := by
  unfold oldZeroCount
  rw [Finset.card_filter,Finset.card_filter]
  exact Equiv.sum_comp e (fun j => if (x.2.2 j).2=0 then 1 else 0)

theorem source_original_E_reindex_coefficient434
    (x : BigState modulus M B) (e : Equiv.Perm (Fin x.2.1.val))
    (mu : P → ℝ) (V rho : ℝ) (target : Fin M → P)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M))
    (step : ℤ) (c : BigEdgeChoice modulus M B x) :
    orientedBigBranchCoefficient modulus M B mu V rho
      (sourceOriginalEReindexState434 modulus M B x e) target shared sigma tau step
      (sourceOriginalEChoiceReindex434 modulus M B x e c) =
    orientedBigBranchCoefficient modulus M B mu V rho x target shared sigma tau step c := by
  have ho := source_original_E_reindex_oldZero434 modulus M B x e
  have hp := source_original_E_reindex_pending434 modulus M B x e sigma step c
  have hz := (Multiset.coe_eq_coe.mp hp).countP_eq (fun z => decide (z.2=0))
  unfold orientedBigBranchCoefficient
  rw [ho]
  change (↑rho : ℂ) ^ (oldZeroCount x.2 +
      outputZeroCount modulus M B (sourceOriginalEReindexState434 modulus M B x e)
        sigma step (sourceOriginalEChoiceReindex434 modulus M B x e c)) *
      (1/(↑V : ℂ)^c.2.1.card) *
      (∏ j ∈ orientedFresh M shared c.2.1,(mu (target (tau j)) : ℂ)) = _
  change (↑rho : ℂ) ^ (oldZeroCount x.2 + _) * _ * _ = _
  unfold outputZeroCount
  rw [hz]
end Green64Analytic.CorrelationSquare

end

end

/-! ## B26AuxCollisionExact -/

section

open Classical
open scoped BigOperators
noncomputable section

namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

local notation "Active" => SourceOriginalB26Active434 BP J ell
local notation "Frame" => SourceOriginalB26FrozenFrame434 BP J ell m patterns

/-- The frozen B26 coefficient after removing only the auxiliary/active ban.
Every other piece of the literal source coefficient is unchanged: auxiliary
mass, both endpoint permutation masses, shared-copy/fresh law, dependent D,
joint complex K, Mellin phase and orientation. -/
def sourceOriginalB26FrozenUnbannedBigWeight434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (h : Frame) (b : Active) : ℂ :=
  let pat := patterns h.1
  let aux := h.2.1
  let sigma := h.2.2.1
  let tau := h.2.2.2
  let D := sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall pat aux a sigma
  if (o = 1 ∨ o = -1) ∧ k ≠ 0 then
    (sourceAuxMass BP bigMod J m V pat aux : ℂ) *
      (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau *
      originalEdgeScalar
        (K h.1 aux (fun g i => a g (sigma g i)) (fun g i => b g (tau g i)))
        zeta theta D o k
  else 0

/-- The genuine B26 auxiliary/active collision contribution.  This is not an
assumed error term: it is the same literal coefficient, restricted to the
complement of the source auxiliary/active ban. -/
def sourceOriginalB26FrozenAuxCollisionWeight434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (h : Frame) (b : Active) : ℂ :=
  let pat := patterns h.1
  let aux := h.2.1
  let sigma := h.2.2.1
  let tau := h.2.2.2
  let D := sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall pat aux a sigma
  if (o = 1 ∨ o = -1) ∧ k ≠ 0 ∧
      ¬ sourceOriginalB26FrozenAuxBan434 BP J ell m pat aux a b then
    (sourceAuxMass BP bigMod J m V pat aux : ℂ) *
      (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau *
      originalEdgeScalar
        (K h.1 aux (fun g i => a g (sigma g i)) (fun g i => b g (tau g i)))
        zeta theta D o k
  else 0

/-- Exact inclusion-exclusion at one physical B26 coefficient.  Thus the
auxiliary collision is paid exactly once, before any norm or Fourier bound. -/
theorem source_original_B26_FROZEN_unbanned_eq_clean_PLUS_collision434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (h : Frame) (b : Active) :
    sourceOriginalB26FrozenUnbannedBigWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b =
    sourceOriginalB26FrozenBigWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b +
    sourceOriginalB26FrozenAuxCollisionWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b := by
  unfold sourceOriginalB26FrozenUnbannedBigWeight434
    sourceOriginalB26FrozenBigWeight434
    sourceOriginalB26FrozenAuxCollisionWeight434
  dsimp only
  by_cases ho : o = 1 ∨ o = -1 <;>
    by_cases hk : k ≠ 0 <;>
      by_cases hb : sourceOriginalB26FrozenAuxBan434 BP J ell m
        (patterns h.1) h.2.1 a b <;>
        simp [ho, hk, hb]

/-- Consumer orientation of the same identity: the literal CLEAN coefficient
is the unbanned comparison coefficient minus the unique collision piece. -/
theorem source_original_B26_FROZEN_clean_eq_unbanned_MINUS_collision434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (h : Frame) (b : Active) :
    sourceOriginalB26FrozenBigWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b =
    sourceOriginalB26FrozenUnbannedBigWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b -
    sourceOriginalB26FrozenAuxCollisionWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b := by
  rw [source_original_B26_FROZEN_unbanned_eq_clean_PLUS_collision434]
  ring

/-- Any nonzero correction is a real source collision and has a legal source
orientation and nonzero shift. -/
theorem source_original_B26_FROZEN_collision_support434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (h : Frame) (b : Active)
    (hn : sourceOriginalB26FrozenAuxCollisionWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b ≠ 0) :
    (o = 1 ∨ o = -1) ∧ k ≠ 0 ∧
      ¬ sourceOriginalB26FrozenAuxBan434 BP J ell m (patterns h.1) h.2.1 a b := by
  by_cases hs : (o = 1 ∨ o = -1) ∧ k ≠ 0 ∧
      ¬ sourceOriginalB26FrozenAuxBan434 BP J ell m (patterns h.1) h.2.1 a b
  · exact hs
  · exfalso
    apply hn
    unfold sourceOriginalB26FrozenAuxCollisionWeight434
    dsimp only
    simp [hs]

/-- The B26 collision event is exactly one auxiliary prime hitting one source
or target active slot.  This is the finite union used by the quantitative
collision estimate; no larger bad event is substituted. -/
theorem source_original_B26_FROZEN_not_auxBan_iff434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (a b : Active) :
    (¬ sourceOriginalB26FrozenAuxBan434 BP J ell m pat aux a b) ↔
      ∃ (g : BG) (j : ↥(pat.free g)) (i : Fin (J+ell)),
        aux g j = a g i ∨ aux g j = b g i := by
  unfold sourceOriginalB26FrozenAuxBan434
  constructor
  · intro h
    by_contra hex
    apply h
    intro g j i
    constructor
    · intro ha
      apply hex
      exact ⟨g,j,i,Or.inl ha⟩
    · intro hb
      apply hex
      exact ⟨g,j,i,Or.inr hb⟩
  · rintro ⟨g,j,i,ha | hb⟩ hall
    · exact (hall g j i).1 ha
    · exact (hall g j i).2 hb

/-- A nonzero collision coefficient therefore supplies a literal colliding
group, auxiliary slot and active endpoint slot. -/
theorem source_original_B26_FROZEN_collision_witness434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (h : Frame) (b : Active)
    (hn : sourceOriginalB26FrozenAuxCollisionWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b ≠ 0) :
    ∃ (g : BG) (j : ↥((patterns h.1).free g)) (i : Fin (J+ell)),
      h.2.1 g j = a g i ∨ h.2.1 g j = b g i := by
  apply (source_original_B26_FROZEN_not_auxBan_iff434 BP J ell m
    (patterns h.1) h.2.1 a b).mp
  exact (source_original_B26_FROZEN_collision_support434 BP bigMod J ell m
    patterns mu V K dsmall zeta theta o k a h b hn).2.2

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable (cap sizes : BG → ℕ) (hsizes : ∀ g, sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)

local notation "Torus" =>
  memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime

/-- Physical (pre-Fourier) B26 coefficient with only the auxiliary/active ban
removed.  OLD residues, dependent translation and the original oriented BIG
coefficient are unchanged. -/
def sourceOriginalB26FrozenUnbannedPhysicalWeight434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (r : Torus) (h : Frame) (b : Active) : ℂ :=
  let pat := patterns h.1
  let aux := h.2.1
  let sigma := h.2.2.1
  let tau := h.2.2.2
  let D := sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall pat aux a sigma
  let step := o*k*(D : ℤ)
  if (o = 1 ∨ o = -1) ∧ k ≠ 0 then
    (sourceAuxMass BP bigMod J m V pat aux : ℂ) *
      (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
      sourceOriginalB26FrozenPhysicalCoefficient434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime mu V pat a b sigma tau D step r *
      originalEdgeScalar
        (K h.1 aux (fun g i => a g (sigma g i)) (fun g i => b g (tau g i)))
        zeta theta D o k
  else 0

/-- The physical collision piece, before the exact harmonic OLD/Fourier
pushforward. -/
def sourceOriginalB26FrozenAuxCollisionPhysicalWeight434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (r : Torus) (h : Frame) (b : Active) : ℂ :=
  let pat := patterns h.1
  let aux := h.2.1
  let sigma := h.2.2.1
  let tau := h.2.2.2
  let D := sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall pat aux a sigma
  let step := o*k*(D : ℤ)
  if (o = 1 ∨ o = -1) ∧ k ≠ 0 ∧
      ¬ sourceOriginalB26FrozenAuxBan434 BP J ell m pat aux a b then
    (sourceAuxMass BP bigMod J m V pat aux : ℂ) *
      (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
      sourceOriginalB26FrozenPhysicalCoefficient434 SP smallMod BP bigMod
        J ell m cap sizes hsizes prime mu V pat a b sigma tau D step r *
      originalEdgeScalar
        (K h.1 aux (fun g i => a g (sigma g i)) (fun g i => b g (tau g i)))
        zeta theta D o k
  else 0

/-- Exact physical correction, before squaring and before Fourier
diagonalization. -/
theorem source_original_B26_FROZEN_physical_clean_eq_unbanned_MINUS_collision434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (a : Active) (r : Torus) (h : Frame) (b : Active) :
    sourceOriginalB26FrozenPhysicalWeight434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime patterns mu V K dsmall zeta theta o k a r h b =
    sourceOriginalB26FrozenUnbannedPhysicalWeight434 BP bigMod J ell m patterns SP smallMod cap sizes hsizes prime mu V K dsmall zeta theta o k a r h b -
    sourceOriginalB26FrozenAuxCollisionPhysicalWeight434 BP bigMod J ell m patterns SP smallMod cap sizes hsizes prime mu V K dsmall zeta theta o k a r h b := by
  unfold sourceOriginalB26FrozenPhysicalWeight434
    sourceOriginalB26FrozenUnbannedPhysicalWeight434
    sourceOriginalB26FrozenAuxCollisionPhysicalWeight434
  dsimp only
  by_cases ho : o = 1 ∨ o = -1 <;>
    by_cases hk : k ≠ 0 <;>
      by_cases hb : sourceOriginalB26FrozenAuxBan434 BP J ell m
        (patterns h.1) h.2.1 a b <;>
        simp [ho, hk, hb]

/-- Direct literal chronological CLEAN summand identity.  It is the existing
B26 source equality with the auxiliary collision removed exactly once; SMALL
Haar, moving D, both orientations, the joint K and OLD coordinates remain
literal. -/
theorem source_original_B26_FROZEN_ORIGINAL_CLEAN_SUMMAND_with_collision434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (xs ys : Green64SmallHaar.GroupState SP smallMod (J+ell))
    (a : Active) (r : Torus) (h : Frame) (b : Active)
    (ss tt : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)) :
    let x := (xs, sourceOriginalB26FrozenBigState434 BP bigMod J ell cap
      sizes hsizes prime a r.2)
    let z := sourceOriginalB26FrozenOriginalChoice434 SP smallMod BP bigMod
      J ell m cap sizes hsizes prime patterns xs ys a r h b ss tt
    let dsmall := sourceOriginalB26SmallSourceD434 SP smallMod J ell xs ss
    let D := sourceOriginalB26FrozenD434 BP bigMod J ell m dsmall
      (patterns h.1) h.2.1 a h.2.2.1
    (if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns x o k z
      then sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs V mu K zeta theta o k x z else 0) =
    (sourceOriginalB26FrozenUnbannedPhysicalWeight434 BP bigMod J ell m patterns SP smallMod cap sizes hsizes prime mu V K dsmall zeta theta o k a r h b -
      sourceOriginalB26FrozenAuxCollisionPhysicalWeight434 BP bigMod J ell m patterns SP smallMod cap sizes hsizes prime mu V K dsmall zeta theta o k a r h b) *
      (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
      Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell) q Vs
        (sourceSmallShared J ell) (o*k*(D : ℤ)) (fun _ _ => 1) ss tt xs ys := by
  dsimp only
  rw [source_original_B26_FROZEN_ORIGINAL_CLEAN_SUMMAND434 SP smallMod BP bigMod
    J ell m cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
    xs ys a r h b ss tt]
  rw [source_original_B26_FROZEN_physical_clean_eq_unbanned_MINUS_collision434]

/-- Coherent unbanned B26 block.  The full source sum over Nu, auxiliaries,
both endpoint permutations and targets remains inside the block. -/
def sourceOriginalB26FrozenUnbannedBigBlock434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (f : Active → ℂ) (a : Active) : ℂ :=
  ∑ h : Frame, ∑ b : Active,
    sourceOriginalB26FrozenUnbannedBigWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b * f b

/-- Coherent collision block with exactly the same joint source indexing. -/
def sourceOriginalB26FrozenAuxCollisionBlock434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (f : Active → ℂ) (a : Active) : ℂ :=
  ∑ h : Frame, ∑ b : Active,
    sourceOriginalB26FrozenAuxCollisionWeight434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k a h b * f b

/-- Exact coherent block correction.  In particular, neither the number of
patterns nor the number of pinned fibres is paid by a triangle inequality at
this stage. -/
theorem source_original_B26_FROZEN_big_block_eq_unbanned_MINUS_collision434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (f : Active → ℂ) (a : Active) :
    sourceOriginalB26FrozenBigBlock434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k f a =
    sourceOriginalB26FrozenUnbannedBigBlock434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k f a -
    sourceOriginalB26FrozenAuxCollisionBlock434 BP bigMod J ell m patterns
      mu V K dsmall zeta theta o k f a := by
  unfold sourceOriginalB26FrozenBigBlock434
    sourceOriginalB26FrozenUnbannedBigBlock434
    sourceOriginalB26FrozenAuxCollisionBlock434
  simp_rw [source_original_B26_FROZEN_clean_eq_unbanned_MINUS_collision434]
  simp only [sub_mul, Finset.sum_sub_distrib]

end Green64FullPhysicalE

end

end

