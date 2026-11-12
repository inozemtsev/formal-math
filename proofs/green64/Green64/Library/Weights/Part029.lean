module

public import Green64.Library.Weights.Part028
public import Green64.Library.Weights.SourceEFrameRow

@[expose] public section

/-!
# Weights / Part029

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalSourceEUncutCapacity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

def sourceOriginalSourceEPrelegal434
    (x : FullPhysicalState SP sm BP bm (J + ell) cap)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm
      J ell m cap patterns x) : Prop :=
  let pat := patterns z.1
  let aux := z.2.1
  let b := z.2.2.1
  let ss := z.2.2.2.1
  let tt := z.2.2.2.2
  let D := sourceOrientedPhysicalD SP sm BP bm
    J ell m cap pat aux x b.sigmaBig ss
  let step := sourceOrientedStep SP sm BP bm
    J ell m cap pat aux x b.sigmaBig ss orientation k
  (orientation = 1 ∨ orientation = -1) ∧ k ≠ 0 ∧
  sourceAuxAvoidsEndpoints SP sm BP bm
    J ell m cap pat aux x b ∧
  (∀ g : BG, SourceOriginalOrientedBigPrelegal434 (bm g) (J + ell)
    (cap g) (x.2 g) (b.bigChoice g).1
    (sourceBigShared J ell m pat g)
    (b.sigmaBig g) (b.tauBig g) D step (b.bigChoice g).2) ∧
  Green64SmallHaar.groupEdgeAllowedPerm
    SP sm (J + ell)
    (sourceSmallShared J ell) step ss tt x.1 b.smallTarget


theorem source_original_SOURCE_E_prelegal_inventory_le434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hz : sourceOriginalSourceEPrelegal434 SP sm BP bm J ell m cap patterns x o k z) :
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
  exact source_original_PHYSICAL_E_prelegal_inventory_le434 (bm g) (J+ell) (cap g)
    (x.2 g) (z.2.2.1.bigChoice g).1
    (sourceBigShared J ell m (patterns z.1) g)
    (z.2.2.1.sigmaBig g) (z.2.2.1.tauBig g)
    (sourceOrientedPhysicalD SP sm BP bm J ell m cap
      (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1)
    (sourceOrientedStep SP sm BP bm J ell m cap
      (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1 o k)
    (z.2.2.1.bigChoice g).2 (hz.2.2.2.1 g)

theorem source_original_SOURCE_E_prelegal_reachable434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (hz : sourceOriginalSourceEPrelegal434 SP sm BP bm J ell m cap patterns x o k z)
    (he : orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z) :
    sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
      (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset) :=
  source_original_inventory_fresh_preserves434 _ _ seen _ hx he.1 he.2
    (source_original_SOURCE_E_prelegal_inventory_le434 SP sm BP bm J ell m cap patterns x o k z hz)


/-- The source global numeric birth gate and reachable inventory make
the original E output-capacity tests automatic at saturated caps. -/
theorem source_original_SOURCE_E_prelegal_implies_legal434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (hz : sourceOriginalSourceEPrelegal434 SP sm BP bm J ell m cap patterns x o k z)
    (he : orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z) :
    sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z := by
  have hy := source_original_SOURCE_E_prelegal_reachable434
    SP sm BP bm J ell m cap patterns x seen o k z hx hz he
  refine ⟨hz.1,hz.2.1,hz.2.2.1,?_,hz.2.2.2.2⟩
  intro g
  have hp := hz.2.2.2.1 g
  refine ⟨hp.shared_copy,hp.stores_unshared,hp.promotes_unshared,hp.promoted_matches,
    hp.promoted_zero,hp.promoted_not_dividing,hp.stored_not_dividing,?_⟩
  have hh := source_original_REACHABLE_pending_card434 SP sm BP bm (J+ell)
    (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
    (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset) hy g
  change (((sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z).2 g).2).card ≤ cap g
  exact hh.trans (hcap g)

theorem source_original_SOURCE_E_legal_implies_prelegal434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hz : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z) :
    sourceOriginalSourceEPrelegal434 SP sm BP bm J ell m cap patterns x o k z := by
  refine ⟨hz.1,hz.2.1,hz.2.2.1,?_,hz.2.2.2.2⟩
  intro g
  have h := hz.2.2.2.1 g
  exact ⟨h.shared_copy,h.stores_unshared,h.promotes_unshared,h.promoted_matches,
    h.promoted_zero,h.promoted_not_dividing,h.stored_not_dividing⟩

/-- Literal marked E admissibility, with output capacity eliminated
using the actual global numeric birth gate rather than a new local filter. -/
theorem source_original_SOURCE_E_marked_prelegal_iff434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ) (o k : ℤ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g) :
    (sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z ∧
      orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z) ↔
    (sourceOriginalSourceEPrelegal434 SP sm BP bm J ell m cap patterns x o k z ∧
      orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z) := by
  constructor
  · rintro ⟨hz,he⟩
    exact ⟨source_original_SOURCE_E_legal_implies_prelegal434
      SP sm BP bm J ell m cap patterns x o k z hz,he⟩
  · rintro ⟨hz,he⟩
    exact ⟨source_original_SOURCE_E_prelegal_implies_legal434
      SP sm BP bm J ell m cap patterns x seen o k z hx hcap hz he,he⟩

/-- Applied to the newly extracted source E frame. No capacity test
remains on the right; all original residue/divisibility and birth tests do. -/
theorem source_original_SOURCE_E_frame_admissible_without_capacity434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ) (o k : ℤ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r) :
    sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f ↔
    (sourceOriginalSourceEPrelegal434 SP sm BP bm J ell m cap patterns x o k
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f) ∧
    orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f)) :=
  source_original_SOURCE_E_marked_prelegal_iff434 SP sm BP bm J ell m cap patterns x seen o k
    (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f) hx hcap
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalEPrelegalOldRestriction -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B B' : ℕ)
variable (x : BigState modulus M B) (y : BigState modulus M B')
variable (e : Fin y.2.1.val ↪ Fin x.2.1.val)
variable (ha : y.1=x.1) (hold : ∀ j,y.2.2 j=x.2.2 (e j))
variable (target : Fin M → P) (shared : Finset (Fin M))
variable (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
variable (store promote : Finset (Fin M))

/- Every original E prelegality field is preserved when an OLD injection
is embedded into the original tuple through a tuple-preserving embedding.
The output-capacity test has already been discharged on the source sector. -/
include ha hold in
theorem source_original_ORIENTED_E_prelegal_OLD_embedding434
    (f : ↥promote ↪ Fin y.2.1.val) :
    SourceOriginalOrientedBigPrelegal434 modulus M B' y target shared sigma tau D step
      ⟨store,promote,f⟩ ↔
    SourceOriginalOrientedBigPrelegal434 modulus M B x target shared sigma tau D step
      ⟨store,promote,f.trans e⟩ := by
  constructor <;> intro h
  · refine ⟨?_,h.stores_unshared,h.promotes_unshared,?_,?_,?_,?_⟩
    · simpa only [ha] using h.shared_copy
    · simpa only [Function.Embedding.trans_apply,←hold] using h.promoted_matches
    · intro j
      have he := congrArg (fun a : Atom P modulus =>
        a.2 + (step : ZMod (modulus a.1))=0) (hold (f j))
      exact Eq.mp he (h.promoted_zero j)
    · simpa only [Function.Embedding.trans_apply,←hold] using h.promoted_not_dividing
    · simpa only [ha] using h.stored_not_dividing
  · refine ⟨?_,h.stores_unshared,h.promotes_unshared,?_,?_,?_,?_⟩
    · simpa only [ha] using h.shared_copy
    · simpa only [Function.Embedding.trans_apply,←hold] using h.promoted_matches
    · intro j
      have he := congrArg (fun a : Atom P modulus =>
        a.2 + (step : ZMod (modulus a.1))=0) (hold (f j))
      exact Eq.mpr he (h.promoted_zero j)
    · simpa only [Function.Embedding.trans_apply,←hold] using h.promoted_not_dividing
    · simpa only [ha] using h.stored_not_dividing

variable (background : Finset P)
variable (hcover : ∀ j : Fin x.2.1.val,(x.2.2 j).1 ∉ background → ∃ i,e i=j)
variable (htarget : ∀ j,target j ∉ background)

/- Every admissible original promotion lands outside the never-active
background, hence factors through the retained OLD tuple. -/
include ha hold hcover htarget in
theorem source_original_ORIENTED_E_prelegal_OLD_factor434
    (f : ↥promote ↪ Fin x.2.1.val)
    (hf : SourceOriginalOrientedBigPrelegal434 modulus M B x target shared sigma tau D step
      ⟨store,promote,f⟩) :
    ∃ g : ↥promote ↪ Fin y.2.1.val,
      g.trans e=f ∧
      SourceOriginalOrientedBigPrelegal434 modulus M B' y target shared sigma tau D step
        ⟨store,promote,g⟩ := by
  have hsupp (j : ↥promote) : ∃ i,e i=f j := by
    apply hcover (f j)
    rw [←hf.promoted_matches j]
    exact htarget (tau j.val)
  let g : ↥promote ↪ Fin y.2.1.val := {
    toFun := fun j => Classical.choose (hsupp j)
    inj' := by
      intro i j hij
      apply f.injective
      calc
        f i = e (Classical.choose (hsupp i)) := (Classical.choose_spec (hsupp i)).symm
        _ = e (Classical.choose (hsupp j)) := congrArg e hij
        _ = f j := Classical.choose_spec (hsupp j) }
  have hg : g.trans e=f := by
    apply Function.Embedding.ext
    intro j
    exact Classical.choose_spec (hsupp j)
  refine ⟨g,hg,?_⟩
  apply (source_original_ORIENTED_E_prelegal_OLD_embedding434
    modulus M B B' x y e ha hold target shared sigma tau D step store promote g).mpr
  simpa only [hg] using hf

/- Nonempty original E promotion fibres are unchanged by deleting a
never-active OLD background. The statement retains all original residue,
D-divisibility and store conditions, not just target matching. -/
include ha hold hcover htarget in
theorem source_original_ORIENTED_E_prelegal_OLD_restriction_iff434 :
    (∃ f : ↥promote ↪ Fin x.2.1.val,
      SourceOriginalOrientedBigPrelegal434 modulus M B x target shared sigma tau D step
        ⟨store,promote,f⟩) ↔
    (∃ f : ↥promote ↪ Fin y.2.1.val,
      SourceOriginalOrientedBigPrelegal434 modulus M B' y target shared sigma tau D step
        ⟨store,promote,f⟩) := by
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨g,hg,hlegal⟩ := source_original_ORIENTED_E_prelegal_OLD_factor434
      modulus M B B' x y e ha hold target shared sigma tau D step store promote
      background hcover htarget f hf
    exact ⟨g,hlegal⟩
  · rintro ⟨f,hf⟩
    exact ⟨f.trans e,(source_original_ORIENTED_E_prelegal_OLD_embedding434
      modulus M B B' x y e ha hold target shared sigma tau D step store promote f).mp hf⟩

/- Genuine equivalence of the entire legal OLD-injection fibres.
No cardinality, norm, independence or asymptotic assumption occurs. -/
def sourceOriginalEPrelegalOldRestrictionEquiv434 :
    {f : ↥promote ↪ Fin y.2.1.val //
      SourceOriginalOrientedBigPrelegal434 modulus M B' y target shared sigma tau D step
        ⟨store,promote,f⟩} ≃
    {f : ↥promote ↪ Fin x.2.1.val //
      SourceOriginalOrientedBigPrelegal434 modulus M B x target shared sigma tau D step
        ⟨store,promote,f⟩} :=
  Equiv.ofBijective
    (fun f => ⟨f.1.trans e,(source_original_ORIENTED_E_prelegal_OLD_embedding434
      modulus M B B' x y e ha hold target shared sigma tau D step store promote f.1).mp f.2⟩)
    ⟨by
      intro f g hfg
      apply Subtype.ext
      apply Function.Embedding.ext
      intro j
      apply e.injective
      exact congrArg (fun h => (h.1 : ↥promote ↪ Fin x.2.1.val) j) hfg,
     by
      intro f
      obtain ⟨g,hg,hlegal⟩ := source_original_ORIENTED_E_prelegal_OLD_factor434
        modulus M B B' x y e ha hold target shared sigma tau D step store promote
        background hcover htarget f.1 f.2
      exact ⟨⟨g,hlegal⟩,Subtype.ext hg⟩⟩


include ha hold hcover htarget in
theorem source_original_ORIENTED_E_prelegal_OLD_fibre_sum434
    (H : (↥promote ↪ Fin x.2.1.val) → ℂ) :
    (∑ f : {f : ↥promote ↪ Fin y.2.1.val //
      SourceOriginalOrientedBigPrelegal434 modulus M B' y target shared sigma tau D step
        ⟨store,promote,f⟩},H (f.1.trans e)) =
    ∑ f : {f : ↥promote ↪ Fin x.2.1.val //
      SourceOriginalOrientedBigPrelegal434 modulus M B x target shared sigma tau D step
        ⟨store,promote,f⟩},H f.1 := by
  apply Fintype.sum_equiv (sourceOriginalEPrelegalOldRestrictionEquiv434
    modulus M B B' x y e ha hold target shared sigma tau D step store promote
    background hcover htarget)
  intro f
  rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalFilteredPendingCanonical -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

section Tuple
variable {U : Type} {n m : ℕ} (a : Fin n → U) (b : Fin m → U)
variable (p : U → Prop) [DecidablePred p]
variable (ha : Function.Injective a) (hb : Function.Injective b)
variable (hm : (List.ofFn b : Multiset U) = (List.ofFn a : Multiset U).filter p)

include hm in
theorem source_original_FILTERED_tuple_mem434 (i : Fin m) :
    p (b i) ∧ ∃ j,a j=b i := by
  have h : b i ∈ (List.ofFn b : Multiset U) := by simp
  rw [hm] at h
  obtain ⟨hmem,hp⟩ := Multiset.mem_filter.mp h
  exact ⟨hp,by simpa only [Multiset.mem_coe,List.mem_ofFn] using hmem⟩

def sourceOriginalFilteredTupleEmbedding434 : Fin m ↪ Fin n where
  toFun i := Classical.choose (source_original_FILTERED_tuple_mem434 a b p hm i).2
  inj' := by
    intro i j hij
    apply hb
    exact (Classical.choose_spec (source_original_FILTERED_tuple_mem434 a b p hm i).2).symm.trans
      ((congrArg a hij).trans
        (Classical.choose_spec (source_original_FILTERED_tuple_mem434 a b p hm j).2))

theorem source_original_FILTERED_tuple_embedding_atoms434 (i : Fin m) :
    b i=a (sourceOriginalFilteredTupleEmbedding434 a b p hb hm i) :=
  (Classical.choose_spec (source_original_FILTERED_tuple_mem434 a b p hm i).2).symm

include ha in
theorem source_original_FILTERED_tuple_embedding_cover434 (j : Fin n) (hj : p (a j)) :
    ∃ i,sourceOriginalFilteredTupleEmbedding434 a b p hb hm i=j := by
  have h : a j ∈ (List.ofFn a : Multiset U).filter p :=
    Multiset.mem_filter.mpr ⟨by simp,hj⟩
  rw [←hm] at h
  obtain ⟨i,hi⟩ : ∃ i,b i=a j := by
    simpa only [Multiset.mem_coe,List.mem_ofFn] using h
  refine ⟨i,ha ?_⟩
  exact (source_original_FILTERED_tuple_embedding_atoms434 a b p hb hm i).symm.trans hi

include ha in
theorem source_original_FILTERED_tuple_embedding_range434 (j : Fin n) :
    (∃ i,sourceOriginalFilteredTupleEmbedding434 a b p hb hm i=j) ↔ p (a j) := by
  constructor
  · rintro ⟨i,rfl⟩
    rw [←source_original_FILTERED_tuple_embedding_atoms434 a b p hb hm i]
    exact (source_original_FILTERED_tuple_mem434 a b p hm i).1
  · exact source_original_FILTERED_tuple_embedding_cover434 a b p ha hb hm j
end Tuple

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- Delete only background OLD atoms from the actual physical output.
SMALL and all BIG active labels are retained literally. -/
def sourceOriginalRemovePendingBackground434
    (background : (g : BG) → Finset (BP g))
    (y : FullPhysicalOutput SP sm BP bm M) : FullPhysicalOutput SP sm BP bm M :=
  (y.1,fun g => ((y.2 g).1,(y.2 g).2.filter (fun a => a.1 ∉ background g)))

theorem source_original_BACKGROUND_filter_inventory_le434
    (background : (g : BG) → Finset (BP g))
    (y : FullPhysicalOutput SP sm BP bm M) :
    sourceOriginalPhysicalInventory434 SP sm BP bm M
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y) ≤
    sourceOriginalPhysicalInventory434 SP sm BP bm M y := by
  unfold sourceOriginalPhysicalInventory434
  apply Finset.sum_le_sum
  intro g hg
  change sourceOriginalBigInventory434 (bm g) M (y.2 g).1
    ((y.2 g).2.filter (fun a => a.1 ∉ background g)) ≤ _
  unfold sourceOriginalBigInventory434
  exact add_le_add le_rfl (Multiset.map_le_map (Multiset.filter_le _ _))

theorem source_original_BACKGROUND_filter_reachable434
    (background : (g : BG) → Finset (BP g))
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen) :
    sourceOriginalPhysicalReachable434 SP sm BP bm M
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y) seen := by
  have hl := source_original_BACKGROUND_filter_inventory_le434 SP sm BP bm M background y
  exact ⟨Multiset.nodup_of_le hl hy.1,fun p hp => hy.2 p (Multiset.mem_of_le hl hp)⟩

theorem source_original_BACKGROUND_canonical_pending434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (background : (g : BG) → Finset (BP g))
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen) (g : BG) :
    fockMultiset ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y)).2 g).2 =
    (fockMultiset ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y).2 g).2).filter
      (fun a => a.1 ∉ background g) := by
  have hp := source_original_REACHABLE_canonical_projection434 SP sm BP bm M cap
    hcap y seen hy
  have hq := source_original_REACHABLE_canonical_projection434 SP sm BP bm M cap
    hcap (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y) seen
    (source_original_BACKGROUND_filter_reachable434 SP sm BP bm M background y seen hy)
  have hp' := congrArg (fun z : FullPhysicalOutput SP sm BP bm M => (z.2 g).2) hp
  have hq' := congrArg (fun z : FullPhysicalOutput SP sm BP bm M => (z.2 g).2) hq
  change fockMultiset ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y).2 g).2 =
    (y.2 g).2 at hp'
  change fockMultiset ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap
    (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y)).2 g).2 =
    (y.2 g).2.filter (fun a => a.1 ∉ background g) at hq'
  rw [hq',hp']

theorem source_original_REACHABLE_canonical_atoms_injective434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen) (g : BG) :
    Function.Injective
      ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y).2 g).2.2 := by
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap
        (sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y)) seen := by
    rw [source_original_REACHABLE_canonical_projection434 SP sm BP bm M cap hcap y seen hy]
    exact hy
  have hi := source_original_PHYSICAL_reachable_OLD_injective434 SP sm BP bm M cap
    (sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y) seen hx g
  exact fun i j hij => hi (congrArg Sigma.fst hij)

def sourceOriginalCanonicalBackgroundEmbedding434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (background : (g : BG) → Finset (BP g))
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen) (g : BG) :
    Fin ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y)).2 g).2.1.val ↪
    Fin ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y).2 g).2.1.val :=
  sourceOriginalFilteredTupleEmbedding434
    ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y).2 g).2.2
    ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y)).2 g).2.2
    (fun a => a.1 ∉ background g)
    (source_original_REACHABLE_canonical_atoms_injective434 SP sm BP bm M cap hcap
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y) seen
      (source_original_BACKGROUND_filter_reachable434 SP sm BP bm M background y seen hy) g)
    (source_original_BACKGROUND_canonical_pending434 SP sm BP bm M cap hcap background y seen hy g)

theorem source_original_BACKGROUND_canonical_embedding_atoms434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (background : (g : BG) → Finset (BP g))
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen) (g : BG)
    (i : Fin ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y)).2 g).2.1.val) :
    ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y)).2 g).2.2 i =
    ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y).2 g).2.2
      (sourceOriginalCanonicalBackgroundEmbedding434 SP sm BP bm M cap hcap background y seen hy g i) := by
  exact source_original_FILTERED_tuple_embedding_atoms434
    ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y).2 g).2.2
    ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y)).2 g).2.2
    (fun a => a.1 ∉ background g)
    (source_original_REACHABLE_canonical_atoms_injective434 SP sm BP bm M cap hcap
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y) seen
      (source_original_BACKGROUND_filter_reachable434 SP sm BP bm M background y seen hy) g)
    (source_original_BACKGROUND_canonical_pending434 SP sm BP bm M cap hcap background y seen hy g) i

theorem source_original_BACKGROUND_canonical_embedding_range434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (background : (g : BG) → Finset (BP g))
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen) (g : BG)
    (j : Fin ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y).2 g).2.1.val) :
    (∃ i,sourceOriginalCanonicalBackgroundEmbedding434 SP sm BP bm M cap hcap background y seen hy g i=j) ↔
    (((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y).2 g).2.2 j).1 ∉ background g := by
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap
        (sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y)) seen := by
    rw [source_original_REACHABLE_canonical_projection434 SP sm BP bm M cap hcap y seen hy]
    exact hy
  have hi := source_original_PHYSICAL_reachable_OLD_injective434 SP sm BP bm M cap
    (sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y) seen hx g
  exact source_original_FILTERED_tuple_embedding_range434
    ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap y).2 g).2.2
    ((sourceOriginalCanonicalPhysical434 SP sm BP bm M cap
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y)).2 g).2.2
    (fun a => a.1 ∉ background g)
    (fun i j hij => hi (congrArg Sigma.fst hij))
    (source_original_REACHABLE_canonical_atoms_injective434 SP sm BP bm M cap hcap
      (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y) seen
      (source_original_BACKGROUND_filter_reachable434 SP sm BP bm M background y seen hy) g)
    (source_original_BACKGROUND_canonical_pending434 SP sm BP bm M cap hcap background y seen hy g) j
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalEPendingBackground -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)

theorem source_original_E_survivors_selected_partition434
    (x : BigState modulus M B) (step : ℤ) (c : BigEdgeChoice modulus M B x) :
    (survivors modulus M B x step c : Multiset (Atom P modulus)) +
      (∑ j ∈ selectedOld modulus M B x c,
        ({translateAtom step (x.2.2 j)} : Multiset (Atom P modulus))) =
    (fockMultiset x.2).map (translateAtom (modulus := modulus) step) := by
  unfold survivors
  rw [source_original_inventory_indexed_bag434]
  rw [show survivorIndices modulus M B x c =
    Finset.univ \ selectedOld modulus M B x c from rfl]
  rw [Finset.sum_sdiff (Finset.subset_univ _)]
  unfold fockMultiset
  rw [Multiset.map_coe,List.map_ofFn,source_original_inventory_ofFn_bag434]
  rfl

theorem source_original_E_selected_injection_bag434
    (x : BigState modulus M B) (step : ℤ) (c : BigEdgeChoice modulus M B x) :
    (∑ j ∈ selectedOld modulus M B x c,
      ({translateAtom step (x.2.2 j)} : Multiset (Atom P modulus))) =
    ∑ j : ↥c.2.1,({translateAtom step (x.2.2 (c.2.2 j))} : Multiset (Atom P modulus)) := by
  rw [selectedOld,Finset.sum_image (fun i hi j hj h => c.2.2.injective h)]

variable (B' : ℕ) (x : BigState modulus M B) (y : BigState modulus M B')
variable (e : Fin y.2.1.val ↪ Fin x.2.1.val)
variable (ha : y.1=x.1) (hold : ∀ j,y.2.2 j=x.2.2 (e j))
variable (background : Finset P)
variable (hm : fockMultiset y.2 =
  (fockMultiset x.2).filter (fun a => a.1 ∉ background))

/- The full OLD output is reconstructed from the retained OLD output
and the literal translation of the deleted background multiset.
This identity uses the actual promotion injection and preserves stores. -/
include ha hold hm in
theorem source_original_E_pending_background_reconstruction434
    (sigma : Equiv.Perm (Fin M)) (step : ℤ)
    (store promote : Finset (Fin M)) (f : ↥promote ↪ Fin y.2.1.val) :
    physicalPendingMultiset modulus M B x sigma step ⟨store,promote,f.trans e⟩ =
    physicalPendingMultiset modulus M B' y sigma step ⟨store,promote,f⟩ +
      ((fockMultiset x.2).filter (fun a => a.1 ∈ background)).map
        (translateAtom (modulus := modulus) step) := by
  let cx : BigEdgeChoice modulus M B x := ⟨store,promote,f.trans e⟩
  let cy : BigEdgeChoice modulus M B' y := ⟨store,promote,f⟩
  let A : Multiset (Atom P modulus) :=
    ((fockMultiset x.2).filter (fun a => a.1 ∈ background)).map
      (translateAtom (modulus := modulus) step)
  have hs :
      (∑ j ∈ selectedOld modulus M B x cx,
        ({translateAtom step (x.2.2 j)} : Multiset (Atom P modulus))) =
      ∑ j ∈ selectedOld modulus M B' y cy,
        ({translateAtom step (y.2.2 j)} : Multiset (Atom P modulus)) := by
    rw [source_original_E_selected_injection_bag434,
      source_original_E_selected_injection_bag434]
    apply Finset.sum_congr rfl
    intro j hj
    change ({translateAtom step (x.2.2 (e (f j)))} : Multiset (Atom P modulus)) =
      {translateAtom step (y.2.2 (f j))}
    rw [hold]
  have hfull :
      (fockMultiset x.2).map (translateAtom (modulus := modulus) step) =
      (fockMultiset y.2).map (translateAtom (modulus := modulus) step) + A := by
    rw [hm]
    change _ = _ +
      ((fockMultiset x.2).filter (fun a => a.1 ∈ background)).map
        (translateAtom (modulus := modulus) step)
    rw [←Multiset.map_add]
    congr 1
    symm
    simpa only [not_not] using
      (Multiset.filter_add_not (fun a : Atom P modulus => a.1 ∉ background)
        (fockMultiset x.2))
  have hp := source_original_E_survivors_selected_partition434 modulus M B x step cx
  have hq := source_original_E_survivors_selected_partition434 modulus M B' y step cy
  have hsurv : (survivors modulus M B x step cx : Multiset (Atom P modulus)) =
      (survivors modulus M B' y step cy : Multiset (Atom P modulus)) + A := by
    have he :
        (survivors modulus M B x step cx : Multiset (Atom P modulus)) +
          (∑ j ∈ selectedOld modulus M B x cx,({translateAtom step (x.2.2 j)} : Multiset (Atom P modulus))) =
        ((survivors modulus M B' y step cy : Multiset (Atom P modulus)) + A) +
          (∑ j ∈ selectedOld modulus M B x cx,({translateAtom step (x.2.2 j)} : Multiset (Atom P modulus))) := by
      rw [hp,hfull,←hq,hs]
      ac_rfl
    exact add_right_cancel he
  have hstore : newlyStored modulus M B x sigma step cx =
      newlyStored modulus M B' y sigma step cy := by
    change List.map (fun i => (⟨x.1 (sigma i),(step : ZMod (modulus (x.1 (sigma i))))⟩ :
        Atom P modulus)) store.toList =
      List.map (fun i => (⟨y.1 (sigma i),(step : ZMod (modulus (y.1 (sigma i))))⟩ :
        Atom P modulus)) store.toList
    apply congrArg (fun t : Fin M → Atom P modulus => List.map t store.toList)
    funext i
    exact congrArg (fun p : P => (⟨p,(step : ZMod (modulus p))⟩ : Atom P modulus))
      (congrFun ha (sigma i)).symm
  change physicalPendingMultiset modulus M B x sigma step cx =
    physicalPendingMultiset modulus M B' y sigma step cy + A
  unfold physicalPendingMultiset physicalPendingOutput
  rw [←Multiset.coe_add,←Multiset.coe_add,hsurv,hstore]
  ac_rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSourceEBackgroundFrame -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
variable (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
variable (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)

local notation "X" => sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y
local notation "Y" => sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
  (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background y)
local notation "E" => sourceOriginalCanonicalBackgroundEmbedding434 SP sm BP bm
  (J+ell) cap hcap background y seen hy

def sourceOriginalBackgroundFrameEmbed434
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns Y r) :
    SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns X r :=
  fun g => (f g).trans (E g)

theorem source_original_SOURCE_E_background_frame_prelegal434
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns Y r) :
    sourceOriginalSourceEPrelegal434 SP sm BP bm J ell m cap patterns Y o k
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns Y r f) ↔
    sourceOriginalSourceEPrelegal434 SP sm BP bm J ell m cap patterns X o k
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r
        (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
          hcap background y seen hy r f)) := by
  have hg (g : BG) := source_original_ORIENTED_E_prelegal_OLD_embedding434
    (bm g) (J+ell) (cap g) (cap g) (X.2 g) (Y.2 g) (E g) rfl
    (source_original_BACKGROUND_canonical_embedding_atoms434
      SP sm BP bm (J+ell) cap hcap background y seen hy g)
    (r.2.2.1.2.2.1 g).1 (sourceBigShared J ell m (patterns r.1) g)
    (r.2.2.1.1 g) (r.2.2.1.2.1 g)
    (sourceOrientedPhysicalD SP sm BP bm J ell m cap (patterns r.1) r.2.1 X
      r.2.2.1.1 r.2.2.2.1)
    (sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1 X
      r.2.2.1.1 r.2.2.2.1 o k)
    (r.2.2.1.2.2.1 g).2.1 (r.2.2.1.2.2.1 g).2.2 (f g)
  constructor <;> intro h
  · exact ⟨h.1,h.2.1,h.2.2.1,fun g => (hg g).mp (h.2.2.2.1 g),h.2.2.2.2⟩
  · exact ⟨h.1,h.2.1,h.2.2.1,fun g => (hg g).mpr (h.2.2.2.1 g),h.2.2.2.2⟩

theorem source_original_SOURCE_E_background_frame_factor434
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (htarget : ∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns X r)
    (hf : sourceOriginalSourceEPrelegal434 SP sm BP bm J ell m cap patterns X o k
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r f)) :
    ∃ g : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns Y r,
      sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
        hcap background y seen hy r g=f ∧
      sourceOriginalSourceEPrelegal434 SP sm BP bm J ell m cap patterns Y o k
        (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns Y r g) := by
  have hfactor (g : BG) := source_original_ORIENTED_E_prelegal_OLD_factor434
    (bm g) (J+ell) (cap g) (cap g) (X.2 g) (Y.2 g) (E g) rfl
    (source_original_BACKGROUND_canonical_embedding_atoms434
      SP sm BP bm (J+ell) cap hcap background y seen hy g)
    (r.2.2.1.2.2.1 g).1 (sourceBigShared J ell m (patterns r.1) g)
    (r.2.2.1.1 g) (r.2.2.1.2.1 g)
    (sourceOrientedPhysicalD SP sm BP bm J ell m cap (patterns r.1) r.2.1 X
      r.2.2.1.1 r.2.2.2.1)
    (sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1 X
      r.2.2.1.1 r.2.2.2.1 o k)
    (r.2.2.1.2.2.1 g).2.1 (r.2.2.1.2.2.1 g).2.2 (background g)
    (fun j hj => (source_original_BACKGROUND_canonical_embedding_range434
      SP sm BP bm (J+ell) cap hcap background y seen hy g j).mpr hj)
    (htarget g) (f g) (hf.2.2.2.1 g)
  choose g he hg using hfactor
  have he' : sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
      hcap background y seen hy r g=f := funext he
  refine ⟨g,he',?_⟩
  apply (source_original_SOURCE_E_background_frame_prelegal434
    SP sm BP bm J ell m cap patterns hcap background y seen hy r o k g).mpr
  simpa only [he'] using hf

theorem source_original_SOURCE_E_background_frame_admissible434
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns Y r) :
    sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns Y seen o k r f ↔
    sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns X seen o k r
      (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
        hcap background y seen hy r f) := by
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap X) seen := by
    rw [source_original_REACHABLE_canonical_projection434
      SP sm BP bm (J+ell) cap hcap y seen hy]
    exact hy
  have hz := source_original_BACKGROUND_filter_reachable434
    SP sm BP bm (J+ell) background y seen hy
  have hy' : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap Y) seen := by
    rw [source_original_REACHABLE_canonical_projection434
      SP sm BP bm (J+ell) cap hcap _ seen hz]
    exact hz
  rw [source_original_SOURCE_E_frame_admissible_without_capacity434
      SP sm BP bm J ell m cap patterns Y seen o k hy' hcap r f,
    source_original_SOURCE_E_frame_admissible_without_capacity434
      SP sm BP bm J ell m cap patterns X seen o k hx hcap r
      (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
        hcap background y seen hy r f)]
  exact and_congr (source_original_SOURCE_E_background_frame_prelegal434
    SP sm BP bm J ell m cap patterns hcap background y seen hy r o k f) Iff.rfl

/-- Actual all-group admissible frame fibres are equivalent after
deleting canonical OLD background avoided by the target. The original
global numerical birth gate and all source arithmetic tests remain. -/
def sourceOriginalBackgroundFrameEquiv434
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (htarget : ∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g) :
    {f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns Y r //
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns Y seen o k r f} ≃
    {f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns X r //
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns X seen o k r f} :=
  Equiv.ofBijective
    (fun f => ⟨sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
        hcap background y seen hy r f.1,
      (source_original_SOURCE_E_background_frame_admissible434
        SP sm BP bm J ell m cap patterns hcap background y seen hy r o k f.1).mp f.2⟩)
    ⟨by
      intro f g hfg
      apply Subtype.ext
      funext b
      apply Function.Embedding.ext
      intro j
      apply (E b).injective
      exact congrArg (fun h => (h.1 b) j) hfg,
     by
      intro f
      have hp := source_original_SOURCE_E_legal_implies_prelegal434
        SP sm BP bm J ell m cap patterns X o k
        (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r f.1) f.2.1
      obtain ⟨g,he,hg⟩ := source_original_SOURCE_E_background_frame_factor434
        SP sm BP bm J ell m cap patterns hcap background y seen hy r o k htarget f.1 hp
      have hg' : sourceOriginalSourceEFrameAdmissible434
          SP sm BP bm J ell m cap patterns Y seen o k r g := by
        apply (source_original_SOURCE_E_background_frame_admissible434
          SP sm BP bm J ell m cap patterns hcap background y seen hy r o k g).mpr
        simpa only [he] using f.2
      exact ⟨⟨g,hg'⟩,Subtype.ext he⟩⟩

theorem source_original_SOURCE_E_background_frame_fibre_sum434
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (htarget : ∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g)
    (H : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns X r → ℂ) :
    (∑ f : {f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns Y r //
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns Y seen o k r f},
      H (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
        hcap background y seen hy r f.1)) =
    ∑ f : {f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns X r //
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns X seen o k r f},H f.1 := by
  apply Fintype.sum_equiv (sourceOriginalBackgroundFrameEquiv434
    SP sm BP bm J ell m cap patterns hcap background y seen hy r o k htarget)
  intro f
  rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSourceEBackgroundTransfer -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Literal contribution of one original frame, summing its actual
admissible OLD injections with the original coefficient and marked output. -/
def sourceOriginalSourceEFrameFibreRow434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) : ℂ :=
  ∑ f : {f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r //
    sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f},
    let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f.1
    sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x z *
    F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
      (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset)

variable (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
variable (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
variable (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)

local notation "X" => sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y
local notation "Y" => sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
  (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background y)
local notation "E" => sourceOriginalCanonicalBackgroundEmbedding434 SP sm BP bm
  (J+ell) cap hcap background y seen hy


/-- Reattach exactly the original pending background at the frame's
physical step. The active output and SMALL state are untouched. -/
def sourceOriginalAttachPendingBackground434 (step : ℤ)
    (out : FullPhysicalOutput SP sm BP bm (J+ell)) :
    FullPhysicalOutput SP sm BP bm (J+ell) :=
  (out.1,fun g => ((out.2 g).1,(out.2 g).2 +
    ((y.2 g).2.filter (fun a => a.1 ∈ background g)).map
      (translateAtom (modulus := bm g) step)))

theorem source_original_SOURCE_E_background_frame_output434
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns Y r) :
    sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns X o k
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r
        (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
          hcap background y seen hy r f)) =
    sourceOriginalAttachPendingBackground434 SP sm BP bm J ell background y
      (sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1 X
        r.2.2.1.1 r.2.2.2.1 o k)
      (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns Y o k
        (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns Y r f)) := by
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · have hp := congrArg (fun z : FullPhysicalOutput SP sm BP bm (J+ell) => (z.2 g).2)
        (source_original_REACHABLE_canonical_projection434
          SP sm BP bm (J+ell) cap hcap y seen hy)
      change fockMultiset (X.2 g).2=(y.2 g).2 at hp
      have hh := source_original_E_pending_background_reconstruction434
        (bm g) (J+ell) (cap g) (cap g) (X.2 g) (Y.2 g) (E g) rfl
        (source_original_BACKGROUND_canonical_embedding_atoms434
          SP sm BP bm (J+ell) cap hcap background y seen hy g)
        (background g)
        (source_original_BACKGROUND_canonical_pending434
          SP sm BP bm (J+ell) cap hcap background y seen hy g)
        (r.2.2.1.1 g)
        (sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1 X
          r.2.2.1.1 r.2.2.2.1 o k)
        (r.2.2.1.2.2.1 g).2.1 (r.2.2.1.2.2.1 g).2.2 (f g)
      have hstep : sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1 Y
          r.2.2.1.1 r.2.2.2.1 o k =
        sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1 X
          r.2.2.1.1 r.2.2.2.1 o k := rfl
      simpa only [sourceOrientedPhysicalOutput,sourceOriginalSourceEFrameLift434,
        sourceOriginalBackgroundFrameEmbed434,sourceOriginalAttachPendingBackground434,
        fullPhysicalBranchOutput,bigGroupBranchOutput,physicalBranchOutput,hp,hstep] using hh

theorem source_original_SOURCE_E_background_frame_births434
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns Y r) :
    orientedEFreshBirths SP sm BP bm J ell m cap patterns
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r
        (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
          hcap background y seen hy r f)) =
    orientedEFreshBirths SP sm BP bm J ell m cap patterns
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns Y r f) := rfl

/-- The complete oscillatory coefficient is preserved at rho=1.
The original joint K, both phases, source divisor, auxiliary data and
endpoint permutations are carried literally by the same frame. -/
theorem source_original_SOURCE_E_background_frame_coefficient434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns Y r) :
    sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta o k X
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r
        (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
          hcap background y seen hy r f)) =
    sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta o k Y
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns Y r f) := by
  exact source_original_SOURCE_E_rho_one_active_weight434 SP sm BP bm J ell m cap cap patterns
    q Vs V mu K zeta theta o k X Y r.1 r.2.1 _ _ r.2.2.2.1 r.2.2.2.2
    rfl (fun _ => rfl) rfl rfl rfl (fun _ => rfl) (fun _ => rfl)

/- Exact actual E-frame transfer for every joint terminal observation.
The translated background stays inside F and inside this frame's step;
no separability of F or of K is assumed. -/
include hcap hy in
theorem source_original_SOURCE_E_background_frame_row434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (htarget : ∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta o k X seen r F =
    sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta o k Y seen r
      (fun out s => F
        (sourceOriginalAttachPendingBackground434 SP sm BP bm J ell background y
          (sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1 X
            r.2.2.1.1 r.2.2.2.1 o k) out) s) := by
  unfold sourceOriginalSourceEFrameFibreRow434
  symm
  apply Fintype.sum_equiv (sourceOriginalBackgroundFrameEquiv434
    SP sm BP bm J ell m cap patterns hcap background y seen hy r o k htarget)
  intro f
  change _ =
    sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta o k X
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r
        (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
          hcap background y seen hy r f.1)) *
    F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns X o k
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r
        (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
          hcap background y seen hy r f.1)))
      (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns
        (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r
          (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
            hcap background y seen hy r f.1))).toFinset)
  rw [source_original_SOURCE_E_background_frame_coefficient434,
    source_original_SOURCE_E_background_frame_output434,
    source_original_SOURCE_E_background_frame_births434]
end Green64Analytic.CorrelationSquare

end

end

