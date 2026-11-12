module

public import Green64.Library.Correlation.Part006
public import Green64.Library.Correlation.Part007
public import Green64.Library.Weights.Part002
public import Green64.Library.Weights.Part024
public import Green64.Library.Correlation.Part005
public import Green64.Library.Correlation.Part001
public import Green64.Library.Analysis.Estimates.Part003
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003

@[expose] public section

/-!
# Correlation / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalActualTerminalVacuum -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- A final actual source G_N witness contributing to the
physical vacuum root product necessarily terminates all OLD
pending particles and creates no terminal ghost births. -/
theorem physical_actual_terminal_vacuum_excludes_ghost_births
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1) :
    ∀ g : BG,
      (H.ghost N g).1.1 = Finset.univ ∧
      ((H.ghost N g).2.1.val) = 0 := by
  have hZero : ∀ g : BG,
      Green64Fock.fockMultiset (((H.afterG N).2 g).2) = 0 := by
    have h : ∀ g : BG,
        ((physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap (H.afterG N)).2 g).2 = 0 := by
      by_contra hn
      simp [physicalVacuum, hn] at hVac
    exact h
  exact real_nonzero_G_terminal_vacuum
    SP smallMod BP bigMod (J+ell) cap
    q rho N N Vbig muBig (H.before N) (H.afterG N)
    (H.ghost N) (H.G_nonzero N (Nat.le_refl N)) hZero

end Green64FullPhysicalE

end

/-! ## PhysicalGhostReindexSource -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- The original source G zero-OLD indices transform covariantly
under an actual bijection of OLD particle indices. This works
with REPEATED atoms: no value-injectivity or prime-set reduction. -/
theorem physical_ghost_zeroOld_reindex
    {U : Type} [DecidableEq U]
    (old next : List U)
    (atZero : U → Prop) [DecidablePred atZero]
    (e : Fin old.length ≃ Fin next.length)
    (h : ∀ j, old.get j = next.get (e j)) :
    (Green64MemoryGhostOp.zeroOld old atZero).image e =
      Green64MemoryGhostOp.zeroOld next atZero := by
  classical
  ext j
  simp only [Finset.mem_image,
    Green64MemoryGhostOp.zeroOld,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, he⟩
    subst j
    simpa only [h i] using hi
  · intro hj
    refine ⟨e.symm j, ?_, ?_⟩
    · simpa only [h (e.symm j), e.apply_symm_apply] using hj
    · exact e.apply_symm_apply j

/-- Every ORIGINAL ghost-row scalar, including old-zero χ powers,
deletion α powers, 1/b! and independent birth γ·ν factors, is
invariant under a reordering of indexed OLD particles. This is
a theorem about the literal sourceGhostTerm, not a new G law. -/
theorem physical_ghost_source_term_reindex
    {U : Type} [DecidableEq U]
    (old next : List U)
    (atZero : U → Prop) [DecidablePred atZero]
    (e : Fin old.length ≃ Fin next.length)
    (h : ∀ j, old.get j = next.get (e j))
    (A : Finset (Fin old.length))
    {b : ℕ} (fresh : Fin b → U)
    (α χ γ : ℂ) (nu : U → ℂ) :
    Green64MemoryGhostOp.sourceGhostTerm old atZero
      A fresh α χ γ nu =
    Green64MemoryGhostOp.sourceGhostTerm next atZero
      (A.image e) fresh α χ γ nu := by
  classical
  have hA : (A.image e).card = A.card := by
    apply Finset.card_image_iff.mpr
    intro i _ j _ hij
    exact e.injective hij
  have hZero := physical_ghost_zeroOld_reindex
    old next atZero e h
  have hzcard :
      (Green64MemoryGhostOp.zeroOld old atZero).card =
        (Green64MemoryGhostOp.zeroOld next atZero).card := by
    rw [← hZero]
    apply (Finset.card_image_iff.mpr
      (by intro i _ j _ hij; exact e.injective hij)).symm
  unfold Green64MemoryGhostOp.sourceGhostTerm
  rw [hA, hzcard]

end Green64FullPhysicalE

end

/-! ## PhysicalGhostReindexOutput -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Deletion of OLD indices and subsequent ordered fresh births
commute, as a full MULTISET, with any exact reindexing of the OLD
Fock atoms. This includes repeated equal atoms; the source's
afterGhost list ordering need not be fixed or canonically sorted. -/
theorem physical_ghost_after_multiset_reindex
    {U : Type} [DecidableEq U]
    (old next : List U)
    (e : Fin old.length ≃ Fin next.length)
    (h : ∀ j, old.get j = next.get (e j))
    (A : Finset (Fin old.length))
    {b : ℕ} (fresh : Fin b → U) :
    (Green64MemoryGhostOp.afterGhost old A fresh : Multiset U) =
    (Green64MemoryGhostOp.afterGhost next (A.image e) fresh : Multiset U) := by
  classical
  let Iold := (List.finRange old.length).filter (fun j => j ∉ A)
  let Inew := (List.finRange next.length).filter
    (fun j => j ∉ A.image e)
  have hIold : Iold.Nodup :=
    (List.nodup_finRange old.length).filter _
  have hInew : Inew.Nodup :=
    (List.nodup_finRange next.length).filter _
  have hindex : (Iold.map e).Perm Inew := by
    apply (List.perm_ext_iff_of_nodup
      (hIold.map e.injective) hInew).mpr
    intro j
    constructor
    · intro hjmap
      rcases List.mem_map.mp hjmap with ⟨i, hi, hij⟩
      have hnot : i ∉ A := by
        simpa using (List.mem_filter.mp hi).2
      have hnot' : j ∉ A.image e := by
        intro hj
        rcases Finset.mem_image.mp hj with ⟨a, ha, hae⟩
        have hai : a = i := e.injective (hae.trans hij.symm)
        exact hnot (hai ▸ ha)
      exact List.mem_filter.mpr
        ⟨List.mem_finRange _, by simpa using hnot'⟩
    · intro hj
      have hnot : j ∉ A.image e := by
        simpa using (List.mem_filter.mp hj).2
      have hpre : e.symm j ∉ A := by
        intro hi
        apply hnot
        exact Finset.mem_image.mpr
          ⟨e.symm j, hi, e.apply_symm_apply j⟩
      exact List.mem_map.mpr
        ⟨e.symm j, List.mem_filter.mpr
          ⟨List.mem_finRange _,by simpa using hpre⟩,
           e.apply_symm_apply j⟩
  have hsource :
      Iold.map old.get = Iold.map (fun j => next.get (e j)) := by
    apply List.map_congr_left
    intro j _
    exact h j
  have hperm :
      (Iold.map old.get).Perm (Inew.map next.get) := by
    rw [hsource]
    simpa only [List.map_map, Function.comp_def]
      using (hindex.map next.get)
  change ((Iold.map old.get ++ List.ofFn fresh : List U) : Multiset U) =
    ((Inew.map next.get ++ List.ofFn fresh : List U) : Multiset U)
  exact Quot.sound (hperm.append_right (List.ofFn fresh))

end Green64FullPhysicalE

end

/-! ## PhysicalInitialBirthGroupFibre -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- ORIGINAL initial BIG active labels are the first births:
one for every true source group and every ordered active slot.
No pending memory or auxiliary D label is counted at the boundary. -/
theorem physicalInitialAllGroupNumbers_exact
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) :
    (physicalInitialBirths SP smallMod BP bigMod J ell cap x).toFinset =
      (Finset.univ : Finset BG).biUnion (fun g =>
        ((Finset.univ : Finset (Fin (J+ell))).image
          ((x.2 g).1)).image (bigMod g)) := by
  classical
  ext n
  constructor
  · intro hn
    have hlist := List.mem_toFinset.mp hn
    unfold physicalInitialBirths at hlist
    rcases List.mem_flatMap.mp hlist with ⟨g, _, hg⟩
    rcases List.mem_map.mp hg with ⟨j, hj, hjnum⟩
    have hjSlot : j ∈ (Finset.univ : Finset (Fin (J+ell))) :=
      Finset.mem_univ _
    apply Finset.mem_biUnion.mpr
    refine ⟨g, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨((x.2 g).1 j), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨j,hjSlot,rfl⟩
    · exact hjnum
  · intro hn
    rcases Finset.mem_biUnion.mp hn with ⟨g, _, hg⟩
    rcases Finset.mem_image.mp hg with ⟨p, hp, hpn⟩
    rcases Finset.mem_image.mp hp with ⟨j, _, hjp⟩
    apply List.mem_toFinset.mpr
    unfold physicalInitialBirths
    apply List.mem_flatMap.mpr
    refine ⟨g, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
    apply List.mem_map.mpr
    refine ⟨j, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
    rw [hjp, hpn]

/-- If the source prime groups have injectively distinct numerical
prime values, the full original initial-birth seen state,
restricted back to a BIG group, is EXACTLY that group's initial
physical active-prime set. -/
theorem physicalInitialBirthGroupSeen_exact
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (g : BG) :
    actualNumericalSeenGroup BP bigMod
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset g =
    (Finset.univ : Finset (Fin (J+ell))).image ((x.2 g).1) := by
  unfold actualNumericalSeenGroup
  rw [physicalInitialAllGroupNumbers_exact SP smallMod BP bigMod
    J ell cap x]
  exact global_big_numeric_batch_group_fibre BP bigMod
    (fun gg => (Finset.univ : Finset (Fin (J+ell))).image
      ((x.2 gg).1)) hnum g

end Green64FullPhysicalE

end

/-! ## PhysicalActualGroupBirthHistory -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The source visit's ACTUAL fresh active birth prime set:
at visit 0 all initial active labels; at visit i+1 the
previous edge's independently integrated fresh target slots.
No OLD promotion, shared label, ghost birth or auxiliary D
draw enters this birth set. -/
noncomputable def physicalGroupFreshVisit
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (g : BG) : ℕ → Finset (BP g)
  | 0 => (Finset.univ : Finset (Fin (J+ell))).image
      (((H.before 0).2 g).1)
  | i+1 =>
      if i < N then
        trueBigFreshValues (J+ell) ((H.edge i).2.2.1.bigChoice g).1
          (sourceBigShared J ell m (patterns (H.edge i).1) g)
          (((H.edge i).2.2.1.bigChoice g).2.2.1)
          ((H.edge i).2.2.1.tauBig g)
      else ∅

/-- The source U_i record of genuinely PREVIOUS numerical births:
the actual group-specific global seen-prime record minus fresh
active births that happened precisely at the current visit. -/
noncomputable def physicalGroupPastVisit
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (g : BG) (i : ℕ) : Finset (BP g) :=
  actualNumericalSeenGroup BP bigMod (H.seen i) g \
    physicalGroupFreshVisit SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig muBig k N H g i

/-- Genuine source visit-zero numerical prime births precisely
equal each group's initial active list when the original prime
group carrier is globally numerically injective. -/
theorem physicalGroupFreshVisit_zero_seen
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (g : BG) :
    physicalGroupFreshVisit SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig muBig k N H g 0 =
    actualNumericalSeenGroup BP bigMod (H.seen 0) g := by
  rw [H.initial_seen]
  exact (physicalInitialBirthGroupSeen_exact SP smallMod BP bigMod
    J ell cap (H.before 0) hnum g).symm

/-- At any actual visit, the source fresh active births belong to
the global chronological set of primes already born up to that
visit. This includes the boundary i=0 and all interior endpoints. -/
theorem physicalGroupFreshVisit_subset_seen
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hi : i ≤ N) (g : BG) :
    physicalGroupFreshVisit SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig muBig k N H g i ⊆
    actualNumericalSeenGroup BP bigMod (H.seen i) g := by
  cases i with
  | zero =>
      rw [physicalGroupFreshVisit_zero_seen SP smallMod BP
        bigMod J ell m cap patterns q rho Vbig muBig k N
        H hnum g]
  | succ j =>
      have hj : j < N := Nat.lt_of_succ_le hi
      intro p hp
      have hUpdate := physical_actual_BIG_group_seen_update
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N j H hnum hj g
      simp only [physicalGroupFreshVisit, if_pos hj] at hp
      rw [hUpdate]
      exact Finset.mem_union_right _ hp

/-- Exactly the source visit's split seen-primes = older births
U_i union fresh active births F_i; no “ever-born set”
is postulated or separately guessed. -/
theorem physicalGroup_seen_eq_past_union_fresh
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hi : i ≤ N) (g : BG) :
    actualNumericalSeenGroup BP bigMod (H.seen i) g =
      physicalGroupPastVisit SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig muBig k N H g i ∪
      physicalGroupFreshVisit SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig muBig k N H g i := by
  unfold physicalGroupPastVisit
  exact (Finset.sdiff_union_of_subset
    (physicalGroupFreshVisit_subset_seen SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N i
      H hnum hi g)).symm

/-- Source boundary U_0 is literally empty, not an extra
assumption appended to the physical path. -/
theorem physicalGroupPastVisit_zero
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (g : BG) :
    physicalGroupPastVisit SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig muBig k N H g 0 = ∅ := by
  unfold physicalGroupPastVisit
  rw [physicalGroupFreshVisit_zero_seen SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H hnum g]
  exact Finset.sdiff_self _

end Green64FullPhysicalE

end

/-! ## PhysicalActualGroupPastRecursion -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The source lifetime's ORIGINAL ever-born update U_(i+1)
= U_i ∪ F_i ∪ G_i now follows from the genuine physical
chronological numerical seen-set, source BIG prime-group
injectivity, and the original G/E per-branch birth bans. -/
theorem physicalGroupPastVisit_succ
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hi : i < N) (g : BG) :
    physicalGroupPastVisit SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig muBig k N H g (i+1) =
    (physicalGroupPastVisit SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig muBig k N H g i ∪
     physicalGroupFreshVisit SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig muBig k N H g i) ∪
     physicalGhostGroupBornSet SP smallMod BP bigMod
       J ell cap (H.before i) (H.ghost i) g := by
  let S := actualNumericalSeenGroup BP bigMod (H.seen i) g
  let G := physicalGhostGroupBornSet SP smallMod BP bigMod
    J ell cap (H.before i) (H.ghost i) g
  let B := trueBigFreshValues (J+ell)
    ((H.edge i).2.2.1.bigChoice g).1
    (sourceBigShared J ell m (patterns (H.edge i).1) g)
    (((H.edge i).2.2.1.bigChoice g).2.2.1)
    ((H.edge i).2.2.1.tauBig g)
  have hSeen : actualNumericalSeenGroup BP bigMod
      (H.seen (i+1)) g = (S ∪ G) ∪ B :=
    physical_actual_BIG_group_seen_update SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k
      N i H hnum hi g
  have hBirth :
      physicalGroupFreshVisit SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig muBig k N H g (i+1) = B := by
    simp [physicalGroupFreshVisit, hi, B]
  have hDisj : Disjoint B (S ∪ G) := by
    have hRaw := (physical_actual_BIG_birth_frontier_disjoint
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N i H hi g).2
    rw [actualNumericalSeenGroup_union] at hRaw
    rw [actual_G_numeric_birth_group_fibre
      SP smallMod BP bigMod J ell cap (H.before i) (H.ghost i)
      hnum g] at hRaw
    exact hRaw
  have hRemove : ((S ∪ G) ∪ B) \ B = S ∪ G := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h,hnot⟩
      rcases h with hSG | hB
      · exact hSG
      · exact False.elim (hnot hB)
    · intro hSG
      exact ⟨Or.inl hSG,
        Finset.disjoint_left.mp hDisj.symm (Finset.mem_union.mpr hSG)⟩
  have hSplit : S =
      physicalGroupPastVisit SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig muBig k N H g i ∪
      physicalGroupFreshVisit SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig muBig k N H g i :=
    physicalGroup_seen_eq_past_union_fresh
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N i H hnum (Nat.le_of_lt hi) g
  calc
    physicalGroupPastVisit SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig muBig k N H g (i+1) =
      actualNumericalSeenGroup BP bigMod (H.seen (i+1)) g \
      physicalGroupFreshVisit SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig muBig k N H g (i+1) := rfl
    _ = ((S ∪ G) ∪ B) \ B := by rw [hSeen,hBirth]
    _ = S ∪ G := hRemove
    _ = _ := by rw [hSplit]

end Green64FullPhysicalE

end

/-! ## PhysicalActualGroupBirthDisjoint -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The source F_i active birth set is disjoint from all earlier
births U_i by its ACTUAL numerical seen-prime construction,
including source visit zero. No duplicate births are postulated. -/
theorem physicalGroupFreshPast_disjoint
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (g : BG) :
    Disjoint
      (physicalGroupFreshVisit SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig muBig k N H g i)
      (physicalGroupPastVisit SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig muBig k N H g i) := by
  unfold physicalGroupPastVisit
  exact Finset.sdiff_disjoint.symm

/-- The actual source G_i numerical ghost-birth list cannot reuse
a prime born during any earlier visit or as a fresh active birth
at this visit. This is the exact source condition G_i ∩ (U_i∪F_i)=∅. -/
theorem physicalGroupGhost_disjoint_past_fresh
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hi : i < N) (g : BG) :
    Disjoint
      (physicalGhostGroupBornSet SP smallMod BP bigMod
        J ell cap (H.before i) (H.ghost i) g)
      (physicalGroupPastVisit SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig muBig k N H g i ∪
       physicalGroupFreshVisit SP smallMod BP bigMod J ell m cap
        patterns q rho Vbig muBig k N H g i) := by
  have hRaw := (physical_actual_BIG_birth_frontier_disjoint
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g).1
  have hSeen := physicalGroup_seen_eq_past_union_fresh
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hnum (Nat.le_of_lt hi) g
  rw [hSeen] at hRaw
  exact hRaw

end Green64FullPhysicalE

end

/-! ## PhysicalActualGroupFreshActive -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The source F_i set of newly born active primes is indeed a
subset of the ACTUAL physical active list at that same visit:
at 0 these are the original initial labels; subsequently they
are exactly the preceding edge's nonpromoted fresh target draws. -/
theorem physicalGroupFreshVisit_subset_active
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ)
    (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i ≤ N) (g : BG) :
    physicalGroupFreshVisit SP smallMod BP bigMod J ell m cap
      patterns q rho Vbig muBig k N H g i ⊆
    (Finset.univ : Finset (Fin (J+ell))).image
      (((H.before i).2 g).1) := by
  cases i with
  | zero =>
      intro p hp
      exact hp
  | succ j =>
      have hj : j < N := Nat.lt_of_succ_le hi
      have hA := (actual_physical_path_big_E_set_update
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N j H hj g).1
      intro p hp
      have hFresh : p ∈ trueBigFreshValues (J+ell)
        ((H.edge j).2.2.1.bigChoice g).1
        (sourceBigShared J ell m (patterns (H.edge j).1) g)
        (((H.edge j).2.2.1.bigChoice g).2.2.1)
        ((H.edge j).2.2.1.tauBig g) := by
        simpa only [physicalGroupFreshVisit, if_pos hj] using hp
      have hTarget :
          p ∈ (Finset.univ : Finset (Fin (J+ell))).image
            (((physicalFockProjection SP smallMod BP bigMod
              (J+ell) cap (H.before (j+1))).2 g).1) := by
        rw [hA]
        exact Finset.mem_union_right _ hFresh
      simpa only [physicalFockProjection] using hTarget

end Green64FullPhysicalE

end

/-! ## PhysicalActualSourceClock -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Concrete time-indexed source row SET carrier for one BIG group;
its fields do not add ANY transition axioms. -/
structure ActualSourceSetClock (P : Type) where
  active : ℕ → Finset P
  pending : ℕ → Finset P
  fresh : ℕ → Finset P
  ghost : ℕ → Finset P
  ended : ℕ → Finset P
  shared : ℕ → Finset P
  stored : ℕ → Finset P
  promoted : ℕ → Finset P
  past : ℕ → Finset P

/-- Exactly the original finite physical source witness variables
with the terminal G_N represented as the last source row.
T=N+1; times >= T are frozen empty states, while past births stay. -/
noncomputable def physicalActualSourceSetClock
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (g : BG) : ActualSourceSetClock (BP g) where
  active := fun i =>
    if i ≤ N then (Finset.univ : Finset (Fin (J+ell))).image
      (((H.before i).2 g).1) else ∅
  pending := fun i =>
    if i ≤ N then actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap (H.before i) g else ∅
  fresh := fun i =>
    if i ≤ N then physicalGroupFreshVisit SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g i else ∅
  ghost := fun i =>
    if i < N then physicalGhostGroupBornSet
      SP smallMod BP bigMod J ell cap (H.before i) (H.ghost i) g
    else ∅
  ended := fun i =>
    if i < N then ((H.ghost i g).1.1).image
      (fun j => ((Green64Fock.fockToList
        (((H.before i).2 g).2)).get j).1)
    else if i = N then actualPhysicalPendingSet SP smallMod BP bigMod
      J ell cap (H.before N) g else ∅
  shared := fun i =>
    if i < N then trueBigSharedValues (bigMod g) (J+ell) (cap g)
      ((H.beforeE i).2 g)
      (sourceBigShared J ell m (patterns (H.edge i).1) g)
      ((H.edge i).2.2.1.sigmaBig g)
    else ∅
  stored := fun i =>
    if i < N then trueBigStoredValues (bigMod g) (J+ell) (cap g)
      ((H.beforeE i).2 g) ((H.edge i).2.2.1.sigmaBig g)
      ((H.edge i).2.2.1.bigChoice g).2
    else ∅
  promoted := fun i =>
    if i < N then trueBigPromotedValues (bigMod g) (J+ell) (cap g)
      ((H.beforeE i).2 g) ((H.edge i).2.2.1.bigChoice g).2
    else ∅
  past := fun i =>
    if i ≤ N then physicalGroupPastVisit SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g i
    else actualNumericalSeenGroup BP bigMod (H.seen N) g

end Green64FullPhysicalE

end

/-! ## PhysicalActualSourceClockBoundary -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Actual original source finite clock has the required initial
empty past, empty OLD pending memory and F_0=A_0. -/
theorem physical_source_clock_initial
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (g : BG) :
    let c := physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g
    c.past 0 = ∅ ∧ c.pending 0 = ∅ ∧ c.fresh 0 = c.active 0 := by
  dsimp only
  have hU := physicalGroupPastVisit_zero SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H hnum g
  have hZero := H.initial_vacuum g
  have hList :
      Green64Fock.fockToList (((H.before 0).2 g).2) = [] := by
    apply List.eq_nil_iff_length_eq_zero.mpr
    have hh := congrArg Multiset.card hZero
    simpa [Green64Fock.fockMultiset, Green64Fock.fockToList] using hh
  constructor
  · simpa [physicalActualSourceSetClock] using hU
  constructor
  · simp [physicalActualSourceSetClock,
      actualPhysicalPendingSet, hList]
  · simp [physicalActualSourceSetClock, physicalGroupFreshVisit]

/-- The true physical clock has exactly the source finite
zero-tail convention beyond its last G_N row T=N+1. -/
theorem physical_source_clock_tail
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (g : BG) (hi : N+1 ≤ i) :
    let c := physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g
    c.active i = ∅ ∧ c.pending i = ∅ ∧
      c.fresh i = ∅ ∧ c.ghost i = ∅ ∧
      c.past i = c.past (N+1) := by
  dsimp only
  have hnot : ¬ i ≤ N := by omega
  have hlt : ¬ i < N := by omega
  have hN : ¬ N+1 ≤ N := by omega
  simp [physicalActualSourceSetClock, hnot, hlt, hN]

end Green64FullPhysicalE

end

/-! ## PhysicalActualSourceClockTerminal -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The terminal physical source row at i=N has no E edge:
it ends all remaining pending primes, has empty G_N births,
and leaves an empty active/pending state at N+1. The global
ever-born ledger still includes F_N, the last active births. -/
theorem physical_source_clock_terminal
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (g : BG) :
    let c := physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g
    c.ended N = c.pending N ∧
    c.ghost N = ∅ ∧ c.shared N = ∅ ∧
    c.stored N = ∅ ∧ c.promoted N = ∅ ∧
    c.active (N+1) = ∅ ∧ c.pending (N+1) = ∅ ∧
    c.fresh (N+1) = ∅ ∧
    c.past (N+1) = (c.past N ∪ c.fresh N) ∪ c.ghost N := by
  dsimp only
  have hSplit := physicalGroup_seen_eq_past_union_fresh
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N N H hnum (Nat.le_refl N) g
  have hn : ¬ N+1 ≤ N := by omega
  have hlt : ¬ N < N := Nat.lt_irrefl N
  simp only [physicalActualSourceSetClock,
    if_pos (Nat.le_refl N), if_neg hn, if_neg hlt,
    if_true, Finset.union_empty, true_and]
  exact hSplit

end Green64FullPhysicalE

end

/-! ## PhysicalActualSourceClockInterior -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Original source BIG row set transitions hold for EVERY actual
interior G_i/E_i physical witness, including selected OLD indices
and the correct independent source endpoint permutations. -/
theorem physical_source_clock_interior_E
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hi : i < N) (g : BG) :
    let c := physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g
    c.shared i ⊆ c.active i ∧
    c.stored i ⊆ c.active i \ c.shared i ∧
    c.promoted i ⊆ (c.pending i \ c.ended i) ∪ c.ghost i ∧
    c.active (i+1) = c.shared i ∪ c.promoted i ∪ c.fresh (i+1) ∧
    c.pending (i+1) =
      (((c.pending i \ c.ended i) ∪ c.ghost i) \
        c.promoted i) ∪ c.stored i := by
  dsimp only
  have hRows := physical_actual_BIG_local_source_rows
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hi g
  have hi_le : i ≤ N := Nat.le_of_lt hi
  have hi1_le : i+1 ≤ N := Nat.succ_le_of_lt hi
  simpa only [physicalActualSourceSetClock,
    if_pos hi, if_pos hi_le, if_pos hi1_le,
    physicalGroupFreshVisit, physicalGhostGroupBornSet] using hRows

end Green64FullPhysicalE

end

/-! ## PhysicalActualSourceClockBirth -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Exact source birth, termination and ever-born conditions
for each REAL interior physical G/E witness at BIG group g. -/
theorem physical_source_clock_interior_birth
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N i : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hi : i < N) (g : BG) :
    let c := physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g
    c.fresh i ⊆ c.active i ∧
    Disjoint (c.fresh i) (c.past i) ∧
    Disjoint (c.ghost i) (c.past i ∪ c.fresh i) ∧
    c.ended i ⊆ c.pending i ∧
    c.past (i+1) = (c.past i ∪ c.fresh i) ∪ c.ghost i := by
  dsimp only
  have hF := physicalGroupFreshVisit_subset_active
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H (Nat.le_of_lt hi) g
  have hFD := physicalGroupFreshPast_disjoint
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H g
  have hGD := physicalGroupGhost_disjoint_past_fresh
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hnum hi g
  have hP := physicalGroupPastVisit_succ
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N i H hnum hi g
  have hEnd :
      ((H.ghost i g).1.1).image (fun j =>
        ((Green64Fock.fockToList (((H.before i).2 g).2)).get j).1)
      ⊆ actualPhysicalPendingSet SP smallMod BP bigMod
          J ell cap (H.before i) g := by
    simpa only [actualPhysicalPendingSet] using
      (ghost_actual_terminated_subset_pending
        (Green64Fock.fockToList (((H.before i).2 g).2))
        (H.ghost i g).1.1
        (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.1))
  have hi_le : i ≤ N := Nat.le_of_lt hi
  have hi1_le : i+1 ≤ N := Nat.succ_le_of_lt hi
  simpa only [physicalActualSourceSetClock,
    if_pos hi, if_pos hi_le, if_pos hi1_le,
    physicalGhostGroupBornSet] using
      ⟨hF,hFD,hGD,hEnd,hP⟩

end Green64FullPhysicalE

end

/-! ## PhysicalActualSourceClockTerminalRow -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The final G_N vacuum row of the actual finite physical
source clock satisfies the COMPLETE source lifespan row schema
with no extra E_N edge and zero terminal ghost births. -/
theorem physical_source_clock_terminal_row
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (g : BG) :
    let c := physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g
    c.fresh N ⊆ c.active N ∧
    Disjoint (c.fresh N) (c.past N) ∧
    Disjoint (c.ghost N) (c.past N ∪ c.fresh N) ∧
    c.ended N ⊆ c.pending N ∧ c.shared N ⊆ c.active N ∧
    c.stored N ⊆ c.active N \ c.shared N ∧
    c.promoted N ⊆ (c.pending N \ c.ended N) ∪ c.ghost N ∧
    c.active (N+1) = c.shared N ∪ c.promoted N ∪ c.fresh (N+1) ∧
    c.pending (N+1) = (((c.pending N \ c.ended N) ∪ c.ghost N) \
      c.promoted N) ∪ c.stored N ∧
    c.past (N+1) = (c.past N ∪ c.fresh N) ∪ c.ghost N := by
  dsimp only
  have hTerm := physical_source_clock_terminal
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H hnum g
  have hFresh := physicalGroupFreshVisit_subset_active
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N N H (Nat.le_refl N) g
  have hDisjoint := physicalGroupFreshPast_disjoint
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N N H g
  have hf : (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g).fresh N ⊆
    (physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g).active N := by
    simpa only [physicalActualSourceSetClock,
      if_pos (Nat.le_refl N)] using hFresh
  have hd : Disjoint
    ((physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g).fresh N)
    ((physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g).past N) := by
    simpa only [physicalActualSourceSetClock,
      if_pos (Nat.le_refl N)] using hDisjoint
  rcases hTerm with ⟨he,hg,hs,hk,hr,ha,hm,hfNext,hu⟩
  refine ⟨hf, hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hu⟩
  · rw [hg]
    exact Finset.disjoint_empty_left _
  · rw [he]
  · rw [hs]
    exact Finset.empty_subset _
  · rw [hk]
    exact Finset.empty_subset _
  · rw [hr]
    exact Finset.empty_subset _
  · simp [ha, hs, hr, hfNext]
  · simp [hm, he, hg, hr, hk]

end Green64FullPhysicalE

end

/-! ## PhysicalActualSourceClockAllRows -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The exact source_set_lifespans ROW HYPOTHESIS is satisfied
at EVERY time by the ACTUAL source-oriented physical G/E witness
clock, including terminal G_N, with all source sets derived from
real old-index operations and independent prime sampling. -/
theorem physical_source_clock_all_rows
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (g : BG) :
    let c := physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g
    ∀ i, c.fresh i ⊆ c.active i ∧
      Disjoint (c.fresh i) (c.past i) ∧
      Disjoint (c.ghost i) (c.past i ∪ c.fresh i) ∧
      c.ended i ⊆ c.pending i ∧ c.shared i ⊆ c.active i ∧
      c.stored i ⊆ c.active i \ c.shared i ∧
      c.promoted i ⊆ (c.pending i \ c.ended i) ∪ c.ghost i ∧
      c.active (i+1) =
        c.shared i ∪ c.promoted i ∪ c.fresh (i+1) ∧
      c.pending (i+1) =
        (((c.pending i \ c.ended i) ∪ c.ghost i) \
          c.promoted i) ∪ c.stored i ∧
      c.past (i+1) = (c.past i ∪ c.fresh i) ∪ c.ghost i := by
  dsimp only
  intro i
  by_cases hi : i < N
  · have he := physical_source_clock_interior_E
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N i H hi g
    have hb := physical_source_clock_interior_birth
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig muBig k N i H hnum hi g
    rcases he with ⟨hs,hk,hr,ha,hm⟩
    rcases hb with ⟨hf,hfd,hgd,he,hu⟩
    exact ⟨hf,hfd,hgd,he,hs,hk,hr,ha,hm,hu⟩
  · by_cases hN : i = N
    · subst i
      exact physical_source_clock_terminal_row
        SP smallMod BP bigMod J ell m cap patterns
        q rho Vbig muBig k N H hnum g
    · have hn : ¬ i ≤ N := by omega
      have hn1 : ¬ i+1 ≤ N := by omega
      have hlt : ¬ i < N := by omega
      simp [physicalActualSourceSetClock, hn, hn1, hlt, hN]

end Green64FullPhysicalE

end

/-! ## PhysicalActualSourceLifespans -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The source-independent-residue lifespan profile is now DERIVED
from the complete corrected physical witness set transition
system (including real terminal G_N and vacuum), not stipulated.
This is the source_set_lifespans theorem with all its hypotheses
proved from the genuine physical G/E path, for each actual BIG
prime group. This theorem alone does not establish weighted path
equivalence or the infinite Exact Memory Identity. -/
theorem physical_actual_BIG_lifespans
    (q rho : ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N)
    (hnum : Function.Injective (globalSigmaPrime BP bigMod))
    (hVac : physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap (H.afterG N)) = 1)
    (g : BG) :
    let c := physicalActualSourceSetClock SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N H g
    ∃ life : BP g → Option (ℕ × ℕ), ∀ p,
      match life p with
      | none =>
          ∀ i, p ∉ c.active i ∧ p ∉ c.pending i ∧ p ∉ c.ghost i
      | some az =>
          az.1 ≤ az.2 ∧ az.2 < N+1 ∧
          (az.1 = az.2 → p ∈ c.active az.1) ∧
          ∀ i,
            (p ∈ c.active i → az.1 ≤ i ∧ i ≤ az.2) ∧
            (p ∈ c.pending i ↔
              az.1 < i ∧ i ≤ az.2 ∧ p ∉ c.active i) ∧
            (p ∈ (c.pending i \ c.ended i) ∪ c.ghost i ↔
              az.1 ≤ i ∧ i < az.2 ∧ p ∉ c.active i) ∧
            (p ∈ c.fresh i ∪ c.ghost i ↔ az.1 = i) ∧
            (p ∈ c.ended i ∪
              (c.active i \ (c.shared i ∪ c.stored i)) ↔ az.2 = i) := by
  dsimp only
  let c := physicalActualSourceSetClock SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig muBig k N H g
  have hInit := physical_source_clock_initial
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H hnum g
  have hRows := physical_source_clock_all_rows
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H hnum g
  have hTail : ∀ i, N+1 ≤ i →
      c.active i = ∅ ∧ c.pending i = ∅ ∧
      c.fresh i = ∅ ∧ c.ghost i = ∅ ∧
      c.past i = c.past (N+1) := by
    intro i hi
    exact physical_source_clock_tail SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig muBig k N i H g hi
  have hLastG := physical_actual_terminal_vacuum_excludes_ghost_births
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vbig muBig k N H hVac
  have hLastSource : (H.ghost N g).1.1 = Finset.univ ∧
      (H.ghost N g).2.1.val = 0 := hLastG g
  have hLife := Green64OrderedLift.source_set_lifespans
    (N+1) c.active c.pending c.fresh c.ghost
    c.ended c.shared c.stored c.promoted c.past
    hInit.1 hInit.2.1 hInit.2.2 hRows hTail
  exact hLife

end Green64FullPhysicalE

end

/-! ## PhysicalLifeFits -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Exact source lifespan meaning on a concrete physical group
clock, including all five equivalent active/pending/birth/end
criteria. No weight normalization is assumed here. -/
def PhysicalLifeFits {P : Type} [DecidableEq P]
    (c : ActualSourceSetClock P) (T : ℕ)
    (life : P → Option (ℕ × ℕ)) : Prop :=
  ∀ p, match life p with
  | none => ∀ i, p ∉ c.active i ∧ p ∉ c.pending i ∧ p ∉ c.ghost i
  | some az =>
      az.1 ≤ az.2 ∧ az.2 < T ∧
      (az.1 = az.2 → p ∈ c.active az.1) ∧
      ∀ i,
        (p ∈ c.active i → az.1 ≤ i ∧ i ≤ az.2) ∧
        (p ∈ c.pending i ↔
          az.1 < i ∧ i ≤ az.2 ∧ p ∉ c.active i) ∧
        (p ∈ (c.pending i \ c.ended i) ∪ c.ghost i ↔
          az.1 ≤ i ∧ i < az.2 ∧ p ∉ c.active i) ∧
        (p ∈ c.fresh i ∪ c.ghost i ↔ az.1 = i) ∧
        (p ∈ c.ended i ∪
          (c.active i \ (c.shared i ∪ c.stored i)) ↔ az.2 = i)


end Green64FullPhysicalE

end

/-! ## PhysicalMarkedRootMoment -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The source G_i with globally marked numerical prime births,
including all independent per-group OLD zero/fresh witnesses BEFORE
summing to an observed Fock output. The source q_i, eta_i, rho and
group V_g and mu-tilde mass belong to the actual G kernel. -/
noncomputable def physicalMarkedSymmetricG
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ) : ℂ :=
  fullPhysicalOrbitAverage SP smallMod BP bigMod (J + ell) cap
    Vsmall muBig
    (fun x => physicalGBirthMarkedRow SP smallMod BP bigMod
      (J + ell) cap q rho N i Vbig muBig x seen F) y

/-- The true finite source-pattern/auxiliary-D/independent-permutations
physical E_i row, now with the PATH-level distinct-birth mark on
the fresh target prime integrations. OLD promotions and stores do
not change the seen-prime set; local E coefficients remain unchanged. -/
noncomputable def physicalMarkedSymmetricE
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ) : ℂ :=
  fullPhysicalOrbitAverage SP smallMod BP bigMod (J + ell) cap
    Vsmall muBig
    (fun x => physicalBirthMarkedE SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k x seen F) y

/-- Initial prime births are precisely the original BIG-group
ordered active labels. Nothing in the small Haar, pending memory,
or independently drawn auxiliary D is counted as a new initial
prime birth. Shared numerical labels across groups are tested
globally, not merely within each group. -/
noncomputable def physicalOutputInitialBirths
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell)) :
    List ℕ :=
  (Finset.univ : Finset BG).toList.flatMap (fun g =>
    (Finset.univ : Finset (Fin (J + ell))).toList.map
      (fun j => bigMod g ((y.2 g).1 j)))

theorem physicalOutputInitialBirths_source_exact
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap) :
    physicalOutputInitialBirths SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J + ell) cap x) =
    physicalInitialBirths SP smallMod BP bigMod
      J ell cap x := rfl

/-- The source-alternating marked G_0 E_0 ... G_N finite expression.
Every G and E retains its raw branch birth list until applying the
GLOBAL distinct-prime test (the seen set), and only then is it
Hilbert-averaged over true SMALL Haar/BIG active/BIG symmetric Fock
input states. This is not an abstract Markov kernel or a standalone
literal row-weight assertion. -/
noncomputable def physicalMarkedGEChain
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
  | 0, start, F =>
      fun y seen =>
        physicalMarkedSymmetricG SP smallMod BP bigMod
          J ell cap q rho N start Vsmall Vbig muBig
          y seen F
  | remaining + 1, start, F =>
      fun y seen =>
        physicalMarkedSymmetricG SP smallMod BP bigMod
          J ell cap q rho N start Vsmall Vbig muBig y seen
          (fun yz seenG =>
            physicalMarkedSymmetricE SP smallMod BP bigMod
              J ell m cap patterns q rho Vsmall Vbig muBig
              Knu ((start : ℝ) * zeta) theta
              (physicalAlternatingSign start) k yz seenG
              (physicalMarkedGEChain q rho Vsmall Vbig muBig
                Knu zeta theta k N remaining (start+1) F))

theorem physicalMarkedGEChain_zero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N start : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ) (y : FullPhysicalOutput SP smallMod BP bigMod
        (J + ell)) (seen : Finset ℕ) :
    physicalMarkedGEChain SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta k N 0 start F y seen =
    physicalMarkedSymmetricG SP smallMod BP bigMod
      J ell cap q rho N start Vsmall Vbig muBig y seen F := rfl

/-- SOURCE-INDEXED FINITE marked physical vacuum product with
N=2R: b_p prefactor, µtilde(p)=1/(V_g p b_p) active/Fock Hilbert
mass, true small Haar, true big symmetric Fock 1/j!, complete
original G_i witnesses, E_i pattern/free D+Kν/phase and
independent endpoint permutations, and ONE numerical distinct-birth
indicator for initial BIG active + ALL later G/E births.

This is an exact finite physical OPERATOR DEFINITION, not yet the
full Exact Memory Identity: cutoff removal, symmetry preservation,
and the source histories<->lifespans weighted pushforward remain
independent proof debts, not axioms. -/
noncomputable def physicalFiniteMarkedRoot
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2 * R
  let mu := physicalSourceMuTilde BP bigMod q N Vbig
  (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod
        (J + ell) cap,
      (physicalOrbitMass SP smallMod BP bigMod (J + ell)
        cap Vsmall mu y : ℂ) *
      star (physicalVacuum SP smallMod BP bigMod J ell y) *
      (if (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).Nodup then
        physicalMarkedGEChain SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig mu
          Knu zeta theta k N N 0
          (fun out _seen =>
            physicalVacuum SP smallMod BP bigMod J ell out)
          y (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).toFinset
       else 0)

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedEOldIndexEquiv -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- Reindex ONLY the original OLD pending injection in a true E
witness. Stores, promoted target slots, the independent endpoint
sigma/tau, and fresh target labels are unchanged. -/
def physical_reindex_E_old_choice
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (c : BigEdgeChoice modulus M B x) :
    BigEdgeChoice modulus M B y :=
  (c.1, ⟨c.2.1,
    ⟨(fun j => e (c.2.2 j)),
      by intro a b h; exact c.2.2.injective (e.injective h)⟩⟩)

/-- Transport is invertible on the actual indexed physical E
choices, including OLD positions with identical prime/residue
values. No set-of-primes or deduplication argument is involved. -/
theorem physical_reindex_E_old_choice_inverse
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (c : BigEdgeChoice modulus M B x) :
    physical_reindex_E_old_choice modulus M B y x e.symm
      (physical_reindex_E_old_choice modulus M B x y e c) = c := by
  apply Prod.ext
  · rfl
  · apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Function.Embedding.ext
      intro j
      change e.symm (e (c.2.2 j)) = c.2.2 j
      exact e.symm_apply_apply _

/-- The source E-legal witness predicate is EXACTLY invariant
under indexed OLD Fock reordering. The proof keeps independent
source and target permutations, genuine promoted residues and
the actual output Fock cutoff; it does not identify ordered OLD
atoms by their prime values. -/
theorem physical_oriented_E_legal_reindex_iff
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (hActive : x.1 = y.1)
    (hAtoms : ∀ i, x.2.2 i = y.2.2 (e i))
    (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) :
    PhysicalEdgeLegal modulus M B x target shared sigma tau D step c ↔
    PhysicalEdgeLegal modulus M B y target shared sigma tau D step
      (physical_reindex_E_old_choice modulus M B x y e c) := by
  let d := physical_reindex_E_old_choice modulus M B x y e c
  have hlen : x.2.1.val = y.2.1.val := by
    simpa using (Fintype.card_congr e)
  have hmem (j : ↥c.2.1) :
      y.2.2 ((physical_reindex_E_old_choice modulus M B x y e c).2.2 j) =
        x.2.2 (c.2.2 j) := by
    change y.2.2 (e (c.2.2 j)) = x.2.2 (c.2.2 j)
    exact (hAtoms (c.2.2 j)).symm
  have hout :
      (physicalPendingOutput modulus M B x sigma step c).length =
      (physicalPendingOutput modulus M B y sigma step d).length := by
    rw [pending_output_length, pending_output_length]
    simpa [d, physical_reindex_E_old_choice, hlen]
  constructor
  · intro hc
    refine
      { shared_copy := ?_
        stores_unshared := ?_
        promotes_unshared := ?_
        promoted_matches := ?_
        promoted_zero := ?_
        promoted_not_dividing := ?_
        stored_not_dividing := ?_
        output_within_cutoff := ?_ }
    · intro i hi
      simpa [← hActive] using hc.shared_copy i hi
    · exact hc.stores_unshared
    · exact hc.promotes_unshared
    · intro j
      rw [hmem j]
      exact hc.promoted_matches j
    · intro j
      rw [hmem j]
      exact hc.promoted_zero j
    · intro j
      rw [hmem j]
      exact hc.promoted_not_dividing j
    · intro j hj
      simpa only [← hActive] using hc.stored_not_dividing j hj
    · rw [← hout]
      exact hc.output_within_cutoff
  · intro hd
    refine
      { shared_copy := ?_
        stores_unshared := ?_
        promotes_unshared := ?_
        promoted_matches := ?_
        promoted_zero := ?_
        promoted_not_dividing := ?_
        stored_not_dividing := ?_
        output_within_cutoff := ?_ }
    · intro i hi
      simpa [hActive] using hd.shared_copy i hi
    · exact hd.stores_unshared
    · exact hd.promotes_unshared
    · intro j
      simpa only [hmem j] using hd.promoted_matches j
    · intro j
      have hz := hd.promoted_zero j
      rw [hmem j] at hz
      exact hz
    · intro j
      simpa only [hmem j] using hd.promoted_not_dividing j
    · intro j hj
      simpa only [hActive] using hd.stored_not_dividing j hj
    · rw [hout]
      exact hd.output_within_cutoff

/-- The inverse on indexed OLD E-witnesses is the reindexing by
the inverse occurrence permutation, even for repeated atoms. -/
def physical_reindex_E_old_choice_equiv
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val) :
    BigEdgeChoice modulus M B x ≃ BigEdgeChoice modulus M B y where
  toFun := physical_reindex_E_old_choice modulus M B x y e
  invFun := physical_reindex_E_old_choice modulus M B y x e.symm
  left_inv := physical_reindex_E_old_choice_inverse modulus M B x y e
  right_inv := by
    intro d
    exact physical_reindex_E_old_choice_inverse
      modulus M B y x e.symm d

/-- Exact bijection between legal E-witnesses for two reorderings
of the same OLD atom occurrences. Both endpoint permutations,
the divisor, all branch data, and the cutoff are unchanged. -/
noncomputable def physical_oriented_E_legal_choice_equiv
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (hActive : x.1 = y.1)
    (hAtoms : ∀ i, x.2.2 i = y.2.2 (e i))
    (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) :
    {c : BigEdgeChoice modulus M B x //
      PhysicalEdgeLegal modulus M B x target shared sigma tau D step c} ≃
    {d : BigEdgeChoice modulus M B y //
      PhysicalEdgeLegal modulus M B y target shared sigma tau D step d} :=
  (physical_reindex_E_old_choice_equiv modulus M B x y e).subtypeEquiv
    (fun c => physical_oriented_E_legal_reindex_iff modulus M B
      x y e hActive hAtoms target shared sigma tau D step c)

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedEOldIndexSourceEquiv -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- Corrected source E-legal witness is invariant under indexed OLD
reordering even when source sigma and target tau differ. The argument
does not replace these permutations by the identity. -/
theorem physical_source_oriented_E_legal_reindex_iff
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (hActive : x.1 = y.1)
    (hAtoms : ∀ i, x.2.2 i = y.2.2 (e i))
    (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x) :
    OrientedBigEdgeLegal modulus M B x target shared sigma tau D step c ↔
    OrientedBigEdgeLegal modulus M B y target shared sigma tau D step
      (physical_reindex_E_old_choice modulus M B x y e c) := by
  let d := physical_reindex_E_old_choice modulus M B x y e c
  have hlen : x.2.1.val = y.2.1.val := by
    simpa using (Fintype.card_congr e)
  have hmem (j : ↥c.2.1) :
      y.2.2 ((physical_reindex_E_old_choice modulus M B x y e c).2.2 j) =
        x.2.2 (c.2.2 j) := by
    change y.2.2 (e (c.2.2 j)) = x.2.2 (c.2.2 j)
    exact (hAtoms (c.2.2 j)).symm
  have hout :
      (physicalPendingOutput modulus M B x sigma step c).length =
      (physicalPendingOutput modulus M B y sigma step d).length := by
    rw [pending_output_length, pending_output_length]
    simpa [d, physical_reindex_E_old_choice, hlen]
  constructor
  · intro hc
    refine
      { shared_copy := ?_
        stores_unshared := ?_
        promotes_unshared := ?_
        promoted_matches := ?_
        promoted_zero := ?_
        promoted_not_dividing := ?_
        stored_not_dividing := ?_
        output_within_cutoff := ?_ }
    · intro j hj
      simpa only [← hActive] using hc.shared_copy j hj
    · exact hc.stores_unshared
    · exact hc.promotes_unshared
    · intro j
      rw [hmem j]
      exact hc.promoted_matches j
    · intro j
      rw [hmem j]
      exact hc.promoted_zero j
    · intro j
      rw [hmem j]
      exact hc.promoted_not_dividing j
    · intro j hj
      simpa only [← hActive] using hc.stored_not_dividing j hj
    · rw [← hout]
      exact hc.output_within_cutoff
  · intro hd
    refine
      { shared_copy := ?_
        stores_unshared := ?_
        promotes_unshared := ?_
        promoted_matches := ?_
        promoted_zero := ?_
        promoted_not_dividing := ?_
        stored_not_dividing := ?_
        output_within_cutoff := ?_ }
    · intro j hj
      simpa only [hActive] using hd.shared_copy j hj
    · exact hd.stores_unshared
    · exact hd.promotes_unshared
    · intro j
      simpa only [hmem j] using hd.promoted_matches j
    · intro j
      have hz := hd.promoted_zero j
      rw [hmem j] at hz
      exact hz
    · intro j
      simpa only [hmem j] using hd.promoted_not_dividing j
    · intro j hj
      simpa only [hActive] using hd.stored_not_dividing j hj
    · rw [hout]
      exact hd.output_within_cutoff

/-- Source-oriented E legal choices are equivalent after reindexing
OLD occurrences, with both independent frames unchanged. -/
noncomputable def physical_source_oriented_E_legal_choice_equiv
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (hActive : x.1 = y.1)
    (hAtoms : ∀ i, x.2.2 i = y.2.2 (e i))
    (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) :
    {c : BigEdgeChoice modulus M B x //
      OrientedBigEdgeLegal modulus M B x target shared sigma tau D step c} ≃
    {d : BigEdgeChoice modulus M B y //
      OrientedBigEdgeLegal modulus M B y target shared sigma tau D step d} :=
  (physical_reindex_E_old_choice_equiv modulus M B x y e).subtypeEquiv
    (fun c => physical_source_oriented_E_legal_reindex_iff modulus M B
      x y e hActive hAtoms target shared sigma tau D step c)

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedEWeightedReindex -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- Old surviving particle INDICES transform by a bijection, even for
identical particle values. This is independent of sigma and tau. -/
theorem physical_oriented_E_survivor_indices_reindex
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (c : BigEdgeChoice modulus M B x) :
    survivorIndices modulus M B y
      (physical_reindex_E_old_choice modulus M B x y e c) =
    (survivorIndices modulus M B x c).image e := by
  classical
  have hselected :
      selectedOld modulus M B y
        (physical_reindex_E_old_choice modulus M B x y e c) =
      (selectedOld modulus M B x c).image e := by
    unfold selectedOld
    change (Finset.univ : Finset (↥c.2.1)).image
      (fun j => e (c.2.2 j)) =
      ((Finset.univ : Finset (↥c.2.1)).image c.2.2).image e
    exact Finset.image_image.symm
  have heuniv :
      (Finset.univ : Finset (Fin x.2.1.val)).image e =
      (Finset.univ : Finset (Fin y.2.1.val)) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact ⟨e.symm i, e.apply_symm_apply i⟩
  unfold survivorIndices
  rw [hselected, ← heuniv]
  exact (Finset.image_sdiff
    (Finset.univ : Finset (Fin x.2.1.val))
    (selectedOld modulus M B x c) e.injective).symm

/-- The stored atoms themselves are identical when the active
arrays are identical, even for independent endpoint permutations. -/
theorem physical_oriented_E_stored_reindex
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (hActive : x.1 = y.1)
    (c : BigEdgeChoice modulus M B x)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ) :
    newlyStored modulus M B x sigma step c =
    newlyStored modulus M B y sigma step
      (physical_reindex_E_old_choice modulus M B x y e c) := by
  simp only [newlyStored, physical_reindex_E_old_choice]
  rw [← hActive]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedEOutputReindex -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- Enumerating an indexed finite set before or after a bijection
gives the same list with a possibly different order. -/
theorem physical_finset_image_toList_perm
    {A Z : Type} [DecidableEq A] [DecidableEq Z]
    (s : Finset A) (e : A ≃ Z) :
    (s.toList.map e).Perm ((s.image e).toList) := by
  classical
  apply (List.perm_ext_iff_of_nodup
    (s.nodup_toList.map e.injective) (Finset.nodup_toList _)).mpr
  intro z
  simp

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- True translated OLD survivor multiset is invariant under OLD
index permutation. Identical atoms are retained with multiplicity. -/
theorem physical_oriented_E_survivors_list_perm
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (hAtoms : ∀ i, x.2.2 i = y.2.2 (e i))
    (c : BigEdgeChoice modulus M B x) (step : ℤ) :
    (survivors modulus M B x step c).Perm
      (survivors modulus M B y step
        (physical_reindex_E_old_choice modulus M B x y e c)) := by
  let s := survivorIndices modulus M B x c
  have hs :
      survivorIndices modulus M B y
        (physical_reindex_E_old_choice modulus M B x y e c) =
      s.image e :=
    physical_oriented_E_survivor_indices_reindex modulus M B x y e c
  have hvalues :
      s.toList.map (fun i =>
        Green64PhysicalEdge.translateAtom step (x.2.2 i)) =
      (s.toList.map e).map (fun i =>
        Green64PhysicalEdge.translateAtom step (y.2.2 i)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply]
    rw [hAtoms i]
  unfold survivors
  rw [hs]
  rw [hvalues]
  exact (physical_finset_image_toList_perm s e).map _
/-- The entire physical E pending output is unchanged as a
multiset of actual prime-residue atoms, including newly stored atoms. -/
theorem physical_oriented_E_pending_output_perm
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (hActive : x.1 = y.1)
    (hAtoms : ∀ i, x.2.2 i = y.2.2 (e i))
    (c : BigEdgeChoice modulus M B x)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ) :
    (physicalPendingOutput modulus M B x sigma step c).Perm
      (physicalPendingOutput modulus M B y sigma step
        (physical_reindex_E_old_choice modulus M B x y e c)) := by
  unfold physicalPendingOutput
  rw [← physical_oriented_E_stored_reindex
    modulus M B x y e hActive c sigma step]
  exact (physical_oriented_E_survivors_list_perm
    modulus M B x y e hAtoms c step).append_right _

/-- Output zero-multiplicity counts agree for every oriented E. -/
theorem physical_oriented_E_output_zero_count_reindex
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (hActive : x.1 = y.1)
    (hAtoms : ∀ i, x.2.2 i = y.2.2 (e i))
    (c : BigEdgeChoice modulus M B x)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ) :
    outputZeroCount modulus M B x sigma step c =
      outputZeroCount modulus M B y sigma step
        (physical_reindex_E_old_choice modulus M B x y e c) := by
  unfold outputZeroCount
  exact (physical_oriented_E_pending_output_perm
    modulus M B x y e hActive hAtoms c sigma step).countP_eq _

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedEBranchCoefficientReindex -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- The number of zero OLD *occurrences* is unchanged by any
particle-index permutation, including when atoms repeat exactly. -/
theorem physical_oriented_E_old_zero_count_reindex
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (hAtoms : ∀ i, x.2.2 i = y.2.2 (e i)) :
    Green64PhysicalEdge.oldZeroCount x.2 =
      Green64PhysicalEdge.oldZeroCount y.2 := by
  let Zx : Finset (Fin x.2.1.val) :=
    Finset.univ.filter (fun i => (x.2.2 i).2 = 0)
  let Zy : Finset (Fin y.2.1.val) :=
    Finset.univ.filter (fun i => (y.2.2 i).2 = 0)
  have hZ : Zx.image e = Zy := by
    ext j
    simp only [Zx, Zy, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [← hAtoms i]
      exact hi
    · intro hj
      refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
      rw [hAtoms (e.symm j), e.apply_symm_apply]
      exact hj
  have hcard : (Zx.image e).card = Zx.card := by
    apply Finset.card_image_iff.mpr
    intro i hi j hj hij
    exact e.injective hij
  change Zx.card = Zy.card
  rw [← hZ]
  exact hcard.symm

/-- Every original oriented big-E branch scalar, with both
arbitrary independent permutation frames, is invariant under OLD
Fock reindexing. This includes rho, V^-a and the mu-tilde mass. -/
theorem physical_oriented_E_branch_coefficient_reindex
    (mu : P → ℝ) (V rho : ℝ)
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (hActive : x.1 = y.1)
    (hAtoms : ∀ i, x.2.2 i = y.2.2 (e i))
    (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (step : ℤ) (c : BigEdgeChoice modulus M B x) :
    orientedBigBranchCoefficient modulus M B mu V rho
      x target shared sigma tau step c =
    orientedBigBranchCoefficient modulus M B mu V rho
      y target shared sigma tau step
        (physical_reindex_E_old_choice modulus M B x y e c) := by
  have hz := physical_oriented_E_old_zero_count_reindex
    modulus M B x y e hAtoms
  have ho := physical_oriented_E_output_zero_count_reindex
    modulus M B x y e hActive hAtoms c sigma step
  unfold orientedBigBranchCoefficient
  rw [hz, ho]
  rfl

/-- Actual oriented E output equality in source Hilbert Fock
multisets, not a deduplicated set of prime values. -/
theorem physical_oriented_E_pending_multiset_reindex
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (hActive : x.1 = y.1)
    (hAtoms : ∀ i, x.2.2 i = y.2.2 (e i))
    (c : BigEdgeChoice modulus M B x)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ) :
    physicalPendingMultiset modulus M B x sigma step c =
      physicalPendingMultiset modulus M B y sigma step
        (physical_reindex_E_old_choice modulus M B x y e c) := by
  apply Quot.sound
  exact physical_oriented_E_pending_output_perm
    modulus M B x y e hActive hAtoms c sigma step

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedEWeightedFibreSum -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- Weighted pushforward of every indexed OLD-choice over a complete
SOURCE-ORIENTED fixed BIG frame. There is no bijection of prime SETS:
the map is on genuine injections into original OLD Fock occurrences.
All possible sigma/tau, repeated atoms, 1/sector mass external to
this row, rho powers, V, and new target mu masses are preserved. -/
theorem physical_source_oriented_E_old_fibre_weighted_sum
    (mu : P → ℝ) (V rho : ℝ)
    (x y : BigState modulus M B)
    (e : Fin x.2.1.val ≃ Fin y.2.1.val)
    (hActive : x.1 = y.1)
    (hAtoms : ∀ i, x.2.2 i = y.2.2 (e i))
    (target : Fin M → P)
    (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ)
    (F : BigPhysicalOutput modulus M → ℂ) :
    (∑ c ∈ (Finset.univ : Finset (BigEdgeChoice modulus M B x)).filter
        (OrientedBigEdgeLegal modulus M B x target shared sigma tau D step),
        orientedBigBranchCoefficient modulus M B mu V rho
          x target shared sigma tau step c *
        F (target, physicalPendingMultiset modulus M B x sigma step c)) =
    (∑ d ∈ (Finset.univ : Finset (BigEdgeChoice modulus M B y)).filter
        (OrientedBigEdgeLegal modulus M B y target shared sigma tau D step),
        orientedBigBranchCoefficient modulus M B mu V rho
          y target shared sigma tau step d *
        F (target, physicalPendingMultiset modulus M B y sigma step d)) := by
  classical
  apply Finset.sum_equiv
    (physical_reindex_E_old_choice_equiv modulus M B x y e)
  · intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact physical_source_oriented_E_legal_reindex_iff
      modulus M B x y e hActive hAtoms
      target shared sigma tau D step c
  · intro c hc
    rw [physical_oriented_E_branch_coefficient_reindex
      modulus M B mu V rho x y e hActive hAtoms
      target shared sigma tau step c]
    rw [physical_oriented_E_pending_multiset_reindex
      modulus M B x y e hActive hAtoms c sigma step]
    rfl

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFullHilbert -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Genuine physical Hilbert compression of the corrected ORIENTED
E_i row, not an abstract Markov kernel. -/
noncomputable def physicalSymmetricOrientedE
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) → ℂ) :
    ℂ :=
  fullPhysicalOrbitAverage SP smallMod BP bigMod
    (J + ell) cap Vsmall muBig
    (fun x => fullSourceOrientedPhysicalE
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig muBig Knu zeta theta
      orientation k x F) y

/-- Exact physical small Haar × big active L² × 1/j! Fock
Hilbert pairing for source-permutation-correct E_i, preserving
the original nu/free-D/OLD/fresh physical witness enumeration. -/
theorem physicalSymmetricOrientedE_pairing
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g) (hmu : ∀ g p, 0 < muBig g p)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (F H : FullPhysicalOutput SP smallMod BP bigMod (J + ell) → ℂ) :
    physicalSymmetricInner SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig F
      (physicalSymmetricOrientedE SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig
        Knu zeta theta orientation k · H) =
    ∑ x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap,
      (fullPhysicalMass SP smallMod BP bigMod
        (J + ell) cap Vsmall muBig x : ℂ) *
      star (F (physicalFockProjection SP smallMod BP bigMod
        (J + ell) cap x)) *
      fullSourceOrientedPhysicalE SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig
        Knu zeta theta orientation k x H := by
  exact fullPhysicalOrbitAverage_pairing SP smallMod BP bigMod
    (J + ell) cap Vsmall muBig hV hmu F _

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedRootMoment -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
variable [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
variable [∀ g, ∀ p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)]
variable [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ)
variable [∀ g, ∀ p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Input-weighted physical Hilbert E with BOTH small endpoint
permutations sampled as original witnesses before taking the
quotient. All numerical birth marks are retained until Fock
output fibre aggregation. -/
noncomputable def physicalOrientedMarkedSymmetricE
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ) : ℂ :=
  fullPhysicalOrbitAverage SP smallMod BP bigMod (J + ell)
    cap Vsmall muBig
    (fun x => physicalOrientedBirthMarkedE SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k x seen F) y

/-- Source-oriented finite G_0 E_0 ... E_(N-1) G_N, carrying the
global chronological seen-prime set. This DOES NOT reuse the
unoriented PhysicalSourcePatternE from the earlier implementation. -/
noncomputable def physicalOrientedMarkedGEChain
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J + ell) →
      Finset ℕ → ℂ)
  | 0, start, F =>
      fun y seen =>
        physicalMarkedSymmetricG SP smallMod BP bigMod
          J ell cap q rho N start Vsmall Vbig muBig y seen F
  | remaining + 1, start, F =>
      fun y seen =>
        physicalMarkedSymmetricG SP smallMod BP bigMod
          J ell cap q rho N start Vsmall Vbig muBig y seen
          (fun yg seenG =>
            physicalOrientedMarkedSymmetricE SP smallMod BP bigMod
              J ell m cap patterns q rho Vsmall Vbig muBig
              Knu ((start : ℝ) * zeta) theta
              (physicalAlternatingSign start) k yg seenG
              (physicalOrientedMarkedGEChain q rho Vsmall Vbig
                muBig Knu zeta theta k N remaining
                (start + 1) F))

/-- The repaired full finite physical root moment. Compare TeX
lem:memory-identity: b_p prefactor; all initial and subsequent
births globally unique, actual small Haar, genuine big active
mu-tilde L2, the Fock 1/j! weighting, exact oriented D and
every original G/E ghost/store/promote source witness.
Source lifespan pushforward and unrestricted Hilbert completion
are still UNPROVED and NOT definitions of this expression. -/
noncomputable def physicalOrientedFiniteMarkedRoot
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2 * R
  let mu := physicalSourceMuTilde BP bigMod q N Vbig
  (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod
      (J + ell) cap,
      (physicalOrbitMass SP smallMod BP bigMod (J + ell)
        cap Vsmall mu y : ℂ) *
      star (physicalVacuum SP smallMod BP bigMod J ell y) *
      (if (physicalOutputInitialBirths SP smallMod BP bigMod
          J ell y).Nodup then
        physicalOrientedMarkedGEChain SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig mu
          Knu zeta theta k N N 0
          (fun out _seen =>
            physicalVacuum SP smallMod BP bigMod J ell out)
          y (physicalOutputInitialBirths SP smallMod BP bigMod
            J ell y).toFinset
       else 0)

end Green64FullPhysicalE

end

/-! ## MemorySourceExpressions -/

section

open Classical
open scoped BigOperators
noncomputable section

namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Source independent-residue physical states. BIG also has its complete
uniform residue torus here; it has no Fock state or chosen lifespan. -/
abbrev MemoryIndependentState :=
  Green64SmallHaar.GroupState SP smallMod (J+ell) ×
    Green64SmallHaar.GroupState BP bigMod (J+ell)

/-- Exact shared-label/auxiliary source divisor; numerical factors, including
repeated auxiliary draws, are retained with multiplicity. -/
def memoryIndependentD (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (bs : BigGroupPerm (BG := BG) (J+ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)) : ℕ :=
  (∏ g : SG, ∏ j ∈ sourceSmallShared J ell g,
    smallMod g (Green64SmallHaar.marks (smallMod g) (J+ell) (x.1 g) (ss g j))) *
  (∏ g : BG,
    (∏ j ∈ sourceBigShared J ell m pat g,
      bigMod g (Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (bs g j))) *
    (∏ j : ↥(pat.free g), bigMod g (aux g j)))

/-- The actual source adjoint interchanges the ordered BIG endpoints before
conjugating. This is an adaptor, not a change to inherited definitions. -/
def memoryOrientationK (Knu : SourcePatternK BP J ell m patterns) (o : ℤ) :
    SourcePatternK BP J ell m patterns :=
  if o = 1 then Knu else fun nu aux s t => Knu nu aux t s

def memoryIndependentAuxBan (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x y : MemoryIndependentState SP smallMod BP bigMod J ell) : Prop :=
  ∀ (g : BG) (j : ↥(pat.free g)) (i : Fin (J+ell)),
    aux g j ≠ Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) i ∧
    aux g j ≠ Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) i

/-- Independent residue path row from 02-transference.tex, lines 100-138,
218-239 and 312-319. Every target state is an ordered distinct list of
zero coordinates. BIG factors are physical V^(-t), not tilted μ integrals.
Both independent endpoint-permutation factors and original ν labels remain. -/
def memoryIndependentRow
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (F : MemoryIndependentState SP smallMod BP bigMod J ell → ℂ) : ℂ :=
  ∑ nu : Nu, ∑ aux : SourceBigAux BP J m (patterns nu),
    ∑ bs : BigGroupPerm (BG := BG) (J+ell),
    ∑ bt : BigGroupPerm (BG := BG) (J+ell),
    ∑ ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell),
    ∑ st : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell),
    ∑ y : MemoryIndependentState SP smallMod BP bigMod J ell,
      let D := memoryIndependentD SP smallMod BP bigMod J ell m
        (patterns nu) aux x bs ss
      let delta := o * k * (D : ℤ)
      if (o = 1 ∨ o = -1) ∧ k ≠ 0 ∧
          memoryIndependentAuxBan SP smallMod BP bigMod J ell m (patterns nu) aux x y then
        (sourceAuxMass BP bigMod J m Vbig (patterns nu) aux : ℂ) *
        (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
        (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
        Green64SmallHaar.groupPermutedKernel BP bigMod (J+ell) q Vbig
          (sourceBigShared J ell m (patterns nu)) delta (fun _ _ => 1) bs bt x.2 y.2 *
        Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell) q Vsmall
          (sourceSmallShared J ell) delta
          (fun _ _ => originalEdgeScalar
            (memoryOrientationK BP J ell m patterns Knu o nu aux
              (fun g i => Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (bs g i))
              (fun g i => Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) (bt g i)))
            zeta theta D o k) ss st x.1 y.1 *
        F y
      else 0

/-- Fixed ζ, alternating orientation; no memory and no terminal active-list
equality. Return to integer position is represented by the θ phase alone. -/
def memoryIndependentChain
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) :
    (remaining start : ℕ) →
    (MemoryIndependentState SP smallMod BP bigMod J ell → ℂ) →
    (MemoryIndependentState SP smallMod BP bigMod J ell → ℂ)
  | 0, _, F => F
  | n+1, start, F =>
      fun x => memoryIndependentRow SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta (physicalAlternatingSign start) k x
        (memoryIndependentChain q Vsmall Vbig Knu zeta theta k n (start+1) F)

def memoryIndependentRoot
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ) *
  (Green64SmallHaar.groupStateMass BP bigMod (J+ell) Vbig : ℂ) *
  ∑ x : MemoryIndependentState SP smallMod BP bigMod J ell,
    memoryIndependentChain SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k (2*R) 0 (fun _ => 1) x

variable (cap : BG → ℕ)

/-- Source-faithful schedule on the inherited physical G/E rows.
The inherited physicalOrientedMarkedGEChain uses start*ζ and does not
transpose K on reverse edges. Neither definition is edited here. -/
def memorySourceGEChain
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
  | 0, start, F => fun y seen =>
      physicalMarkedSymmetricG SP smallMod BP bigMod J ell cap
        q rho N start Vsmall Vbig muBig y seen F
  | n+1, start, F => fun y seen =>
      physicalMarkedSymmetricG SP smallMod BP bigMod J ell cap
        q rho N start Vsmall Vbig muBig y seen
        (fun yg seenG =>
          physicalOrientedMarkedSymmetricE SP smallMod BP bigMod
            J ell m cap patterns q rho Vsmall Vbig muBig
            (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k yg seenG
            (memorySourceGEChain q rho Vsmall Vbig muBig Knu zeta theta k N n (start+1) F))

/-- Actual marked Fock Hilbert root with source-faithful spectral schedule.
All inherited G, E, OLD, ghost factorial, orbit masses, vacuum and distinct
birth definitions are called unchanged. -/
def memorySourceRoot
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bigMod q N Vbig
  (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
  ∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod (J+ell) cap,
    (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu y : ℂ) *
    star (physicalVacuum SP smallMod BP bigMod J ell y) *
    (if (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).Nodup then
      memorySourceGEChain SP smallMod BP bigMod J ell m patterns cap
        q rho Vsmall Vbig mu Knu zeta theta k N N 0
        (fun out _ => physicalVacuum SP smallMod BP bigMod J ell out)
        y (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).toFinset
    else 0)

/-- Genuine source prime-domain obligations for the exact finite identity.
These are regularity conditions of the original prime groups, not replacement
hypotheses for a missing multiplicity, surjectivity or absolute bound. -/
structure MemorySourceDomain (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (k : ℤ) (R : ℕ) : Prop where
  q_pos : 0 < q
  q_lt_one : q < 1
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  rho_sq : Real.sqrt q < rho^2
  R_pos : 0 < R
  k_ne : k ≠ 0
  small_prime : ∀ g p, Nat.Prime (smallMod g p)
  big_prime : ∀ g p, Nat.Prime (bigMod g p)
  small_injective : Function.Injective (fun x : Sigma SP => smallMod x.1 x.2)
  big_injective : Function.Injective (fun x : Sigma BP => bigMod x.1 x.2)
  disjoint : ∀ gs ps gb pb, smallMod gs ps ≠ bigMod gb pb
  small_above_k : ∀ g p, k.natAbs < smallMod g p
  big_above_k : ∀ g p, k.natAbs < bigMod g p
  big_above_visits : ∀ g p, 2*R+1 < bigMod g p
  Vsmall_eq : ∀ g, Vsmall g = ∑ p : SP g, 1/(smallMod g p : ℝ)
  Vbig_eq : ∀ g, Vbig g = ∑ p : BP g, 1/(bigMod g p : ℝ)
  Vsmall_pos : ∀ g, 0 < Vsmall g
  Vbig_pos : ∀ g, 0 < Vbig g
  cap_saturated : ∀ g, Fintype.card (BP g) ≤ cap g

end Green64FullPhysicalE

end

end

/-! ## MemoryIndBIGStateSigma -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (M : ℕ)

/-- The complete ORIGINAL BIG residue torus: one independent numerical
residue coordinate for every prime, including primes never active. -/
abbrev MemoryIndependentBIGTorus :=
  (g : BG) → Green64SmallHaar.SmallTorus (bigMod g)

/-- Ordered injective ORIGINAL BIG marks at a fixed full torus residue.
The state carries M distinct ZERO-coordinate prime labels per group.
These are not an unordered prime subset or arbitrary marks. -/
abbrev MemoryIndependentBIGMarks
    (c : MemoryIndependentBIGTorus BP bigMod) :=
  (g : BG) → Green64SmallHaar.MarksAt (bigMod g) M (c g)

/-- Reassemble one ACTUAL independent BIG physical group state from its
full residue torus and ordered, valid ZERO-coordinate marks. -/
def memoryIndependentBIGStateFrom
    (c : MemoryIndependentBIGTorus BP bigMod)
    (a : MemoryIndependentBIGMarks BP bigMod M c) :
    Green64SmallHaar.GroupState BP bigMod M :=
  fun g => Green64SmallHaar.stateFrom (bigMod g) M (c g) (a g)

/-- Critical source-first BIG Haar disintegration is a BIJECTION:
each original source independent BIG GroupState has precisely one
full residue torus c AND a dependent family of ordered distinct zero
marks. Thus no torus or factorial multiplicity is invented. -/
def memoryIndependentBIGStateSigmaEquiv :
    Green64SmallHaar.GroupState BP bigMod M ≃
      (Σ c : MemoryIndependentBIGTorus BP bigMod,
        MemoryIndependentBIGMarks BP bigMod M c) where
  toFun x :=
    ⟨(fun g => (x g).val.1),
      (fun g => ⟨(x g).val.2,(x g).property⟩)⟩
  invFun := fun s => memoryIndependentBIGStateFrom BP bigMod M s.1 s.2
  left_inv x := by
    funext g
    apply Subtype.ext
    rfl
  right_inv s := by
    cases s with
    | mk c a =>
      apply Sigma.ext
      · rfl
      · rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryIndBIGHaarFubini -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (M : ℕ)

/-- The ORIGINAL tensor of independent BIG Hilbert state masses is
literally the product of its complete group Haar probability and
the source's individual V_g^{-M} active-mark mass. Neither mass is
normalized away and there is no cross-group factorial. -/
theorem memory_ind_BIG_true_group_mass_split (Vbig : BG → ℝ) :
    (Green64SmallHaar.groupStateMass BP bigMod M Vbig : ℂ) =
      (∏ g : BG, (Green64SmallHaar.haarAtomMass (bigMod g) : ℂ)) *
      (∏ g : BG, (((1:ℝ)/(Vbig g)^M : ℝ) : ℂ)) := by
  unfold Green64SmallHaar.groupStateMass Green64SmallHaar.stateMass
  push_cast
  rw [Finset.prod_mul_distrib]

/-- EXACT finite BIG group Haar disintegration of the ORIGINAL
independent-residue Hilbert state sum. First sum over EVERY independent
BIG numerical prime residue, including non-active primes; then over
the dependent ORIGINAL ordered injective active marks at that residue.
This preserves the source group probability, all V_g^{-M}, no
surrogate stochastic law and no phantom factorial multiplicity. -/
theorem memory_ind_BIG_true_group_state_disintegration
    (Vbig : BG → ℝ)
    (F : Green64SmallHaar.GroupState BP bigMod M → ℂ) :
    (∑ x : Green64SmallHaar.GroupState BP bigMod M,
      (Green64SmallHaar.groupStateMass BP bigMod M Vbig : ℂ) * F x) =
    ∑ c : MemoryIndependentBIGTorus BP bigMod,
      (∏ g : BG, (Green64SmallHaar.haarAtomMass (bigMod g) : ℂ)) *
      (∑ a : MemoryIndependentBIGMarks BP bigMod M c,
        (∏ g : BG, (((1:ℝ)/(Vbig g)^M : ℝ) : ℂ)) *
          F (memoryIndependentBIGStateFrom BP bigMod M c a)) := by
  let mass : ℂ := (Green64SmallHaar.groupStateMass BP bigMod M Vbig : ℂ)
  let haar : ℂ := ∏ g : BG, (Green64SmallHaar.haarAtomMass (bigMod g) : ℂ)
  let marksMass : ℂ := ∏ g : BG, (((1:ℝ)/(Vbig g)^M : ℝ) : ℂ)
  have hm : mass = haar * marksMass :=
    memory_ind_BIG_true_group_mass_split BP bigMod M Vbig
  have hsum := Fintype.sum_equiv
    (memoryIndependentBIGStateSigmaEquiv BP bigMod M)
    (fun x : Green64SmallHaar.GroupState BP bigMod M => mass * F x)
    (fun ca : Σ c : MemoryIndependentBIGTorus BP bigMod,
        MemoryIndependentBIGMarks BP bigMod M c =>
      mass * F (memoryIndependentBIGStateFrom BP bigMod M ca.1 ca.2))
    (by intro x; rfl)
  change (∑ x, mass * F x) = _ 
  rw [hsum,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hm]
  ring
end Green64FullPhysicalE

end

end

/-! ## MemoryIndOriginalRowLinear -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- SINGLE ORIGINAL independent physical row coefficient with all
original ν/aux, BIG source+target and SMALL source+target endpoint
permutations, q damping, signed kD phase, and reverse-K orientation.
No endpoint delta-or-Haar mass is lost. The continuation F is
deliberately NOT included; this is the genuine linear kernel scalar. -/
def memoryIndependentRowScalar
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x y : MemoryIndependentState SP smallMod BP bigMod J ell)
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG := BG) (J+ell))
    (ss st : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)) : ℂ :=
  let D := memoryIndependentD SP smallMod BP bigMod J ell m (patterns nu)
    aux x bs ss
  let delta := o*k*(D : ℤ)
  if (o = 1 ∨ o = -1) ∧ k ≠ 0 ∧
    memoryIndependentAuxBan SP smallMod BP bigMod J ell m
      (patterns nu) aux x y then
    (sourceAuxMass BP bigMod J m Vbig (patterns nu) aux : ℂ) *
    (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
    (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
    Green64SmallHaar.groupPermutedKernel BP bigMod (J+ell) q Vbig
      (sourceBigShared J ell m (patterns nu)) delta
      (fun _ _ => 1) bs bt x.2 y.2 *
    Green64SmallHaar.groupPermutedKernel SP smallMod (J+ell) q Vsmall
      (sourceSmallShared J ell) delta
      (fun _ _ => originalEdgeScalar
        (memoryOrientationK BP J ell m patterns Knu o nu aux
          (fun g i => Green64SmallHaar.marks (bigMod g) (J+ell) (x.2 g) (bs g i))
          (fun g i => Green64SmallHaar.marks (bigMod g) (J+ell) (y.2 g) (bt g i)))
        zeta theta D o k) ss st x.1 y.1
  else 0

/-- ORIGINAL independent source row is genuinely linear in its
continuation F, and its coefficient is precisely the original
nu/aux/four-permutation/BIG+SMALL kernel scalar. This transformation
works even for zero kernels and zero source weight; it only extracts
F without altering the original E source. -/
theorem memory_independent_row_exact_scalar_linear
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (F : MemoryIndependentState SP smallMod BP bigMod J ell → ℂ) :
    memoryIndependentRow SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta o k x F =
    ∑ nu : Nu, ∑ aux : SourceBigAux BP J m (patterns nu),
    ∑ bs : BigGroupPerm (BG := BG) (J+ell),
    ∑ bt : BigGroupPerm (BG := BG) (J+ell),
    ∑ ss : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell),
    ∑ st : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell),
    ∑ y : MemoryIndependentState SP smallMod BP bigMod J ell,
      memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta o k x y nu aux bs bt ss st * F y := by
  unfold memoryIndependentRow
  apply Finset.sum_congr rfl; intro nu hnu
  apply Finset.sum_congr rfl; intro aux haux
  apply Finset.sum_congr rfl; intro bs hbs
  apply Finset.sum_congr rfl; intro bt hbt
  apply Finset.sum_congr rfl; intro ss hss
  apply Finset.sum_congr rfl; intro st hst
  apply Finset.sum_congr rfl; intro y hy
  unfold memoryIndependentRowScalar
  rw [ite_mul]
  simp only [zero_mul]
end Green64FullPhysicalE

end

end

/-! ## MemoryIndOriginalRowSigma -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The ORIGINAL independent BIG and SMALL Haar row, with all its
literal dependent Nu/auxiliary choice and FOUR separately ordered
source/target permutation families (BIG sigma,tau and SMALL sigma,tau),
plus its actual independent target state y. This is a true FINITE
dependent Sigma index, not a quotient of permutations or a fake
transition-state kernel. -/
abbrev MemoryIndependentOriginalRowIndex :=
    Σ nu : Nu,
      SourceBigAux BP J m (patterns nu) ×
      BigGroupPerm (BG := BG) (J+ell) ×
      BigGroupPerm (BG := BG) (J+ell) ×
      Green64SmallHaar.GroupPermFamily (G := SG) (J+ell) ×
      Green64SmallHaar.GroupPermFamily (G := SG) (J+ell) ×
      MemoryIndependentState SP smallMod BP bigMod J ell

noncomputable instance : Fintype
    (MemoryIndependentOriginalRowIndex SP smallMod BP bigMod
      J ell m patterns) := by
  classical
  unfold MemoryIndependentOriginalRowIndex
  letI : (nu : Nu) → Fintype (
      SourceBigAux BP J m (patterns nu) ×
      BigGroupPerm (BG := BG) (J+ell) ×
      BigGroupPerm (BG := BG) (J+ell) ×
      Green64SmallHaar.GroupPermFamily (G := SG) (J+ell) ×
      Green64SmallHaar.GroupPermFamily (G := SG) (J+ell) ×
      MemoryIndependentState SP smallMod BP bigMod J ell) :=
    fun nu => inferInstance
  exact Sigma.instFintype

/-- The exact independent ORIGINAL row's literal output state, with
no quotient or changed chronological residue clock. -/
def memoryIndependentOriginalRowOutput
    (a : MemoryIndependentOriginalRowIndex SP smallMod BP bigMod
      J ell m patterns) :
    MemoryIndependentState SP smallMod BP bigMod J ell :=
  a.2.2.2.2.2.2

/-- The independent original row equals the exact single finite Sigma
sum over its original Nu/aux/BIG/SMALL permutation choices and original
target state. All source coefficients are literally unchanged and its
F continuation is evaluated at the original output state. -/
theorem memory_independent_row_exact_original_sigma
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (F : MemoryIndependentState SP smallMod BP bigMod J ell → ℂ) :
    memoryIndependentRow SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta o k x F =
    ∑ a : MemoryIndependentOriginalRowIndex SP smallMod BP bigMod
      J ell m patterns,
      memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta o k x
        (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
        a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1
        a.2.2.2.2.2.1 *
      F (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a) := by
  rw [memory_independent_row_exact_scalar_linear]
  convert memory_ind_dependent_sevenfold_Fubini
    (Aux := fun nu : Nu => SourceBigAux BP J m (patterns nu))
    (Bs := BigGroupPerm (BG := BG) (J+ell))
    (Bt := BigGroupPerm (BG := BG) (J+ell))
    (Ss := Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (St := Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (Y := MemoryIndependentState SP smallMod BP bigMod J ell)
    (f := fun a : MemoryIndependentOriginalRowIndex SP smallMod BP bigMod
      J ell m patterns =>
      memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta o k x
        (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
        a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1
        a.2.2.2.2.2.1 *
      F (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a))
  all_goals rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryIndOriginalPathIndex -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Genuine ORIGINAL independent finite path index. Each of n rows
contains the full dependent ν/aux, BIG σ/τ, SMALL σ/τ and next
physical independent state y; no quotient and no replacement kernel. -/
def memoryIndOriginalPathIndex : ℕ → Type
  | 0 => PUnit
  | n+1 => MemoryIndependentOriginalRowIndex SP smallMod BP bigMod J ell m patterns ×
      memoryIndOriginalPathIndex n

noncomputable instance (n : ℕ) :
    Fintype (memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n) := by
  induction n with
  | zero =>
    change Fintype PUnit
    infer_instance
  | succ n ih =>
    change Fintype (MemoryIndependentOriginalRowIndex SP smallMod BP bigMod
      J ell m patterns ×
      memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n)
    letI := ih
    infer_instance

/-- Exact original independent source coefficient of a complete
ordered path, with terminal continuation F. Recursion is over
TRUE source row indices; output of each row IS the next path state,
so the path carries the original state consistency exactly. -/
def memoryIndOriginalPathTerm
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (start : ℕ)
    (F : MemoryIndependentState SP smallMod BP bigMod J ell → ℂ)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell) :
    (n : ℕ) → memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n → ℂ
  | 0, _ => F x
  | n+1, ⟨a, tail⟩ =>
    memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta (physicalAlternatingSign start) k x
      (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
      a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1
      a.2.2.2.2.2.1 *
    memoryIndOriginalPathTerm q Vsmall Vbig Knu zeta theta k (start+1) F
      (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
      n tail
end Green64FullPhysicalE

end

end

/-! ## MemoryIndOriginalChainFullPaths -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

set_option maxHeartbeats 900000

/-- Source EXACT independent BIG/SMALL memory-free chronological
path Fubini. The ORIGINAL source recursive memoryIndependentChain
is the full sum over n actual row records (dependent Nu/aux,
BIG σ/τ and SMALL σ/τ, true next independent state) with the
original source row scalar at EACH time and its actual terminal
continuation. Holds for arbitrary terminal F, signed k, orientations
and zero Fourier coefficients. No new Markov kernel or stochastic
path-law assumption. -/
theorem memory_independent_chain_exact_original_paths
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (n start : ℕ)
    (F : MemoryIndependentState SP smallMod BP bigMod J ell → ℂ)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell) :
    memoryIndependentChain SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k n start F x =
    ∑ p : memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n,
      memoryIndOriginalPathTerm SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k start F x n p := by
  induction n generalizing start x with
  | zero =>
    change F x = (∑ p : PUnit, F x)
    simp
  | succ n ih =>
    change memoryIndependentRow SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta (physicalAlternatingSign start) k x
      (memoryIndependentChain SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k n (start+1) F) = _
    rw [memory_independent_row_exact_original_sigma]
    change
      (∑ a : MemoryIndependentOriginalRowIndex SP smallMod BP bigMod J ell m patterns,
        memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta (physicalAlternatingSign start) k x
          (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
          a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 *
        memoryIndependentChain SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k n (start+1) F
          (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)) =
      (∑ p : memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns (n+1),
        memoryIndOriginalPathTerm SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k start F x (n+1) p)
    simp only [memoryIndOriginalPathIndex, memoryIndOriginalPathTerm,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a ha
    rw [ih (start+1) (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)]
    rw [Finset.mul_sum]
end Green64FullPhysicalE

end

end

/-! ## MemoryIndOriginalChronologicalNonzero -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- TRUE source independent Markov path step coefficient extracted
CHRONOLOGICALLY from the original indexed Nu/aux/BIG-SMALL σ/τ
row indices, with actual preceding x and next row output y.
This direct recursive readout avoids treating coordinates as
independent new random variables after a transition. -/
def memoryIndOriginalChronologicalStep
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) :
    (n : ℕ) → (start : ℕ) →
    (x : MemoryIndependentState SP smallMod BP bigMod J ell) →
    memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n →
    Fin n → ℂ
  | 0, _, _, _, i => i.elim0
  | n+1, start, x, ⟨a,tail⟩, i =>
    Fin.cases
      (memoryIndependentRowScalar SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta (physicalAlternatingSign start) k x
        (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
        a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1)
      (fun j => memoryIndOriginalChronologicalStep q Vsmall Vbig Knu zeta theta k n (start+1)
        (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
        tail j)
      i

/-- Every original Markov transition in an ORIGINAL nonzero-weight
complete independent source path has a nonzero full source scalar.
The statement holds at EVERY indexed time, with alternating source K,
all original Nu/aux and four endpoint permutation families.
This follows from the actual original path product, not an
assumed nonzero independent transition law. -/
theorem memory_ind_original_nonzero_all_true_steps
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (F : MemoryIndependentState SP smallMod BP bigMod J ell → ℂ)
    (n start : ℕ)
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (p : memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns n)
    (h : memoryIndOriginalPathTerm SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k start F x n p ≠ 0)
    (i : Fin n) :
    memoryIndOriginalChronologicalStep SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k n start x p i ≠ 0 := by
  induction n generalizing start x with
  | zero => exact i.elim0
  | succ n ih =>
    rcases p with ⟨a,tail⟩
    have hsplit := mul_ne_zero_iff.mp h
    cases i using Fin.cases with
    | zero => exact hsplit.1
    | succ j =>
      change memoryIndOriginalChronologicalStep SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k n (start+1)
        (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
        tail j ≠ 0
      exact ih (start+1)
        (memoryIndependentOriginalRowOutput SP smallMod BP bigMod J ell m patterns a)
        tail hsplit.2 j
end Green64FullPhysicalE

end

end

/-! ## MemoryIndOriginalRootFullPaths -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The ORIGINAL, UNMODIFIED independent finite root with its TWO
initial SMALL/BIG physical Haar+V masses equals a finite sum over
all truly original independent initial states and all (2R) dependent
ν/aux/BIG+SMALL-endpoint-permutations/next-state path records.
The original signed K, ν, auxiliary ban, BIG and SMALL kernels,
endpoint damping, and every time-step coefficient are retained.
This is an exact global original-path expansion, not the still-OPEN
comparison to the frozen BIG Haar expectation. -/
theorem memory_independent_root_exact_true_original_path_sum
    (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    memoryIndependentRoot SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k R =
    (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ) *
    (Green64SmallHaar.groupStateMass BP bigMod (J+ell) Vbig : ℂ) *
    (∑ x : MemoryIndependentState SP smallMod BP bigMod J ell,
      ∑ p : memoryIndOriginalPathIndex SP smallMod BP bigMod J ell m patterns (2*R),
        memoryIndOriginalPathTerm SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k 0 (fun _ => 1) x (2*R) p) := by
  unfold memoryIndependentRoot
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  exact memory_independent_chain_exact_original_paths SP smallMod BP bigMod
    J ell m patterns q Vsmall Vbig Knu zeta theta k
    (2*R) 0 (fun _ => 1) x
end Green64FullPhysicalE

end

end

