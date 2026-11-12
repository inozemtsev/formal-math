module

public import Green64.Library.Correlation.PhysicalGhostSaturated
public import Green64.Library.Weights.GhostJointPushforward
public import Green64.Library.Correlation.Part028
public import Green64.Library.Weights.Part002
public import Green64.Library.Correlation.Part006

@[expose] public section

/-!
# Correlation / Part029

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalGhostSetExtraction -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

abbrev SourceOriginalPhysicalGhostSetWitness434
    (x : FullPhysicalState SP sm BP bm M cap) :=
  (g : BG) → SourceOriginalGhostSetChoice434
    (fockToList ((x.2 g).2)) (fun z : Atom (BP g) (bm g) => z.2=0)

def sourceOriginalPhysicalGhostSetProjection434
    (x : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x) :
    SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x :=
  fun g => sourceOriginalGhostSetProjection434
    (fockToList ((x.2 g).2)) (fun z => z.2=0) (cap g) (c g)

def sourceOriginalPhysicalGhostSetBirths434
    (x : FullPhysicalState SP sm BP bm M cap)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) : List ℕ :=
  (Finset.univ : Finset BG).toList.flatMap (fun g =>
    (d g).2.toList.map (fun z => bm g z.1))

def sourceOriginalPhysicalGhostSetEligible434
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) : Prop :=
  (sourceOriginalPhysicalGhostSetBirths434 SP sm BP bm M cap x d).Nodup ∧
    Disjoint seen (sourceOriginalPhysicalGhostSetBirths434 SP sm BP bm M cap x d).toFinset

def sourceOriginalPhysicalGhostSetOutput434
    (x : FullPhysicalState SP sm BP bm M cap)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) :
    FullPhysicalOutput SP sm BP bm M :=
  (x.1,fun g => ((x.2 g).1,
    memoryTupleBag (fun j : {j : Fin (fockToList ((x.2 g).2)).length // j ∉ (d g).1.1} =>
      (fockToList ((x.2 g).2)).get j) + ∑ z ∈ (d g).2,({z}:Multiset (Atom (BP g) (bm g)))))

def sourceOriginalPhysicalGhostSetFits434
    (x : FullPhysicalState SP sm BP bm M cap)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) : Prop :=
  ∀ g, ((sourceOriginalPhysicalGhostSetOutput434 SP sm BP bm M cap x d).2 g).2.card ≤ cap g

def sourceOriginalPhysicalGhostSetTest434
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) : ℂ :=
  if sourceOriginalPhysicalGhostSetEligible434 SP sm BP bm M cap x seen d then
    if sourceOriginalPhysicalGhostSetFits434 SP sm BP bm M cap x d then
      F (sourceOriginalPhysicalGhostSetOutput434 SP sm BP bm M cap x d)
        (seen ∪ (sourceOriginalPhysicalGhostSetBirths434 SP sm BP bm M cap x d).toFinset)
    else 0
  else 0

def sourceOriginalPhysicalGhostDistinctCoefficient434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x) : ℂ :=
  ∏ g, sourceOriginalGhostDistinctCoefficient434
    (fockToList ((x.2 g).2)) (fun z : Atom (BP g) (bm g) => z.2=0) (cap g)
    (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
    (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
    (-((sourceVisitEta q N i:ℝ):ℂ)*(Vb g:ℂ)/(rho:ℂ))
    (sourceBirthNu (fun p => (mu g p:ℂ))) (c g)

def sourceOriginalPhysicalGhostSetCoefficient434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) : ℂ :=
  ∏ g, sourceOriginalGhostSetCoefficient434
    (fockToList ((x.2 g).2)) (fun z : Atom (BP g) (bm g) => z.2=0) (cap g)
    (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
    (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
    (-((sourceVisitEta q N i:ℝ):ℂ)*(Vb g:ℂ)/(rho:ℂ))
    (sourceBirthNu (fun p => (mu g p:ℂ))) (d g)

theorem source_original_PHYSICAL_G_eligible_fresh_injective434
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (he : physicalGhostBatchEligible SP sm BP bm M cap x seen c) :
    ∀ g,Function.Injective (c g).2.2 := by
  intro g
  have hn := he.1
  change ((Finset.univ : Finset BG).toList.flatMap (fun g =>
    (List.ofFn (c g).2.2).map (fun z => bm g z.1))).Nodup at hn
  have hg := (List.nodup_flatMap.mp hn).1 g (by simp)
  exact List.nodup_ofFn.mp (List.Nodup.of_map (fun z => bm g z.1) hg)

theorem source_original_PHYSICAL_G_set_births_perm434
    (x : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (hi : ∀ g,Function.Injective (c g).2.2) :
    (physicalGhostFreshBirths SP sm BP bm M cap x c).Perm
      (sourceOriginalPhysicalGhostSetBirths434 SP sm BP bm M cap x
        (sourceOriginalPhysicalGhostSetProjection434 SP sm BP bm M cap x c)) := by
  unfold physicalGhostFreshBirths sourceOriginalPhysicalGhostSetBirths434
    sourceOriginalPhysicalGhostSetProjection434 sourceOriginalGhostSetProjection434
  apply List.Perm.flatMap (List.Perm.refl _)
  intro g hg
  apply List.Perm.map
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact List.nodup_ofFn.mpr (hi g)
  · exact Finset.nodup_toList _
  · rw [Finset.toList_toFinset]
    ext z
    simp

theorem source_original_PHYSICAL_G_set_gate434
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (hi : ∀ g,Function.Injective (c g).2.2) :
    physicalGhostBatchEligible SP sm BP bm M cap x seen c ↔
      sourceOriginalPhysicalGhostSetEligible434 SP sm BP bm M cap x seen
        (sourceOriginalPhysicalGhostSetProjection434 SP sm BP bm M cap x c) := by
  have hp := source_original_PHYSICAL_G_set_births_perm434 SP sm BP bm M cap x c hi
  have hs : (physicalGhostFreshBirths SP sm BP bm M cap x c).toFinset =
      (sourceOriginalPhysicalGhostSetBirths434 SP sm BP bm M cap x
        (sourceOriginalPhysicalGhostSetProjection434 SP sm BP bm M cap x c)).toFinset := by
    ext n
    simpa only [List.mem_toFinset] using (hp.mem_iff (a := n))
  exact and_congr hp.nodup_iff (by rw [hs])

theorem source_original_PHYSICAL_G_set_output_bag434
    (x : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (hi : ∀ g,Function.Injective (c g).2.2) (g : BG) :
    (afterGhost (fockToList ((x.2 g).2)) (c g).1.1 (c g).2.2 : Multiset (Atom (BP g) (bm g))) =
    ((sourceOriginalPhysicalGhostSetOutput434 SP sm BP bm M cap x
      (sourceOriginalPhysicalGhostSetProjection434 SP sm BP bm M cap x c)).2 g).2 := by
  dsimp only [sourceOriginalPhysicalGhostSetOutput434,
    sourceOriginalPhysicalGhostSetProjection434,sourceOriginalGhostSetProjection434]
  rw [memory_source_afterGhost_bag]
  congr 1
  exact source_original_GHOST_birth_fibre_bag434 (c g).2.1.val
    (Finset.univ.image (c g).2.2) ⟨(c g).2.2,hi g,rfl⟩ (fun z => z)

theorem source_original_PHYSICAL_G_set_fits434
    (x : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (hi : ∀ g,Function.Injective (c g).2.2) :
    sourceOriginalPhysicalGhostWitnessFits434 SP sm BP bm M cap x c ↔
    sourceOriginalPhysicalGhostSetFits434 SP sm BP bm M cap x
      (sourceOriginalPhysicalGhostSetProjection434 SP sm BP bm M cap x c) := by
  unfold sourceOriginalPhysicalGhostWitnessFits434 sourceOriginalPhysicalGhostSetFits434
  apply forall_congr'
  intro g
  rw [←source_original_PHYSICAL_G_set_output_bag434 SP sm BP bm M cap x c hi g]
  simp only [Multiset.coe_card]

theorem source_original_PHYSICAL_G_target_set_output434
    (x : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (hi : ∀ g,Function.Injective (c g).2.2)
    (hc : sourceOriginalPhysicalGhostWitnessFits434 SP sm BP bm M cap x c) :
    physicalFockProjection SP sm BP bm M cap
      (sourceOriginalPhysicalGhostWitnessTarget434 SP sm BP bm M cap x c hc) =
    sourceOriginalPhysicalGhostSetOutput434 SP sm BP bm M cap x
      (sourceOriginalPhysicalGhostSetProjection434 SP sm BP bm M cap x c) := by
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · simpa only [physicalFockProjection,sourceOriginalPhysicalGhostWitnessTarget434,
        fockMultiset,sourceOriginalFockFromList434,List.ofFn_get] using
        source_original_PHYSICAL_G_set_output_bag434 SP sm BP bm M cap x c hi g

theorem source_original_PHYSICAL_G_set_joint_transfer434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap)
    (H : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x → ℂ) :
    (∑ c : FullGhostWitness SP sm BP bm M cap x,
      sourceOriginalPhysicalGhostDistinctCoefficient434 SP sm BP bm M cap q rho N i Vb mu x c *
        H (sourceOriginalPhysicalGhostSetProjection434 SP sm BP bm M cap x c)) =
    ∑ d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x,
      sourceOriginalPhysicalGhostSetCoefficient434 SP sm BP bm M cap q rho N i Vb mu x d * H d := by
  have hinst : (instFintypeFullGhostWitness SP sm BP bm M cap x) =
      (Pi.instFintype : Fintype ((g : BG) →
        GhostWitnessChoice (fockToList ((x.2 g).2)) (fun z => z.2=0) (cap g))) :=
    Subsingleton.elim _ _
  rw [hinst]
  unfold sourceOriginalPhysicalGhostDistinctCoefficient434
    sourceOriginalPhysicalGhostSetProjection434 sourceOriginalPhysicalGhostSetCoefficient434
  refine source_original_GHOST_joint_exact_transfer434
    (fun g => GhostWitnessChoice (fockToList ((x.2 g).2)) (fun z => z.2=0) (cap g))
    (fun g => SourceOriginalGhostSetChoice434 (fockToList ((x.2 g).2)) (fun z => z.2=0))
    (fun g => sourceOriginalGhostSetProjection434 (fockToList ((x.2 g).2)) (fun z => z.2=0) (cap g))
    (fun g => sourceOriginalGhostDistinctCoefficient434 (fockToList ((x.2 g).2)) (fun z => z.2=0) (cap g)
      (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
      (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
      (-((sourceVisitEta q N i:ℝ):ℂ)*(Vb g:ℂ)/(rho:ℂ))
      (sourceBirthNu (fun p => (mu g p:ℂ))))
    (fun g => sourceOriginalGhostSetCoefficient434 (fockToList ((x.2 g).2)) (fun z => z.2=0) (cap g)
      (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
      (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
      (-((sourceVisitEta q N i:ℝ):ℂ)*(Vb g:ℂ)/(rho:ℂ))
      (sourceBirthNu (fun p => (mu g p:ℂ)))) ?_ H
  intro g F
  exact source_original_GHOST_group_set_pushforward434
    (fockToList ((x.2 g).2)) (fun z => z.2=0) (cap g) _ _ _ _ F

theorem source_original_PHYSICAL_MARKED_G_distinct_projection434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i Vb mu x seen F =
    ∑ c : FullGhostWitness SP sm BP bm M cap x,
      sourceOriginalPhysicalGhostDistinctCoefficient434 SP sm BP bm M cap q rho N i Vb mu x c *
        sourceOriginalPhysicalGhostSetTest434 SP sm BP bm M cap x seen F
          (sourceOriginalPhysicalGhostSetProjection434 SP sm BP bm M cap x c) := by
  rw [source_original_PHYSICAL_MARKED_G_target_collapse434]
  unfold sourceOriginalPhysicalMarkedGhostCollapsed434
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hi : ∀ g,Function.Injective (c g).2.2
  · have hw : sourceOriginalPhysicalGhostDistinctCoefficient434 SP sm BP bm M cap
        q rho N i Vb mu x c =
        sourceOriginalPhysicalGhostWitnessCoefficient434 SP sm BP bm M cap q rho N i Vb mu x c := by
      unfold sourceOriginalPhysicalGhostDistinctCoefficient434 sourceOriginalPhysicalGhostWitnessCoefficient434
      apply Finset.prod_congr rfl
      intro g hg
      simp only [sourceOriginalGhostDistinctCoefficient434,if_pos (hi g)]
    have hgate := source_original_PHYSICAL_G_set_gate434 SP sm BP bm M cap x seen c hi
    have hfits := source_original_PHYSICAL_G_set_fits434 SP sm BP bm M cap x c hi
    have hp := source_original_PHYSICAL_G_set_births_perm434 SP sm BP bm M cap x c hi
    have hs : (physicalGhostFreshBirths SP sm BP bm M cap x c).toFinset =
        (sourceOriginalPhysicalGhostSetBirths434 SP sm BP bm M cap x
          (sourceOriginalPhysicalGhostSetProjection434 SP sm BP bm M cap x c)).toFinset := by
      ext n
      simpa only [List.mem_toFinset] using (hp.mem_iff (a := n))
    rw [hw]
    unfold sourceOriginalPhysicalGhostSetTest434
    rw [←propext hgate,←propext hfits]
    by_cases he : physicalGhostBatchEligible SP sm BP bm M cap x seen c
    · simp only [if_pos he]
      by_cases hf : sourceOriginalPhysicalGhostWitnessFits434 SP sm BP bm M cap x c
      · simp only [dif_pos hf,if_pos hf]
        rw [source_original_PHYSICAL_G_target_set_output434 SP sm BP bm M cap x c hi hf,hs]
      · simp only [dif_neg hf,if_neg hf,mul_zero]
    · simp only [if_neg he,mul_zero]
  · obtain ⟨g,hg⟩ := not_forall.mp hi
    have he : ¬physicalGhostBatchEligible SP sm BP bm M cap x seen c := by
      intro hh
      exact hg (source_original_PHYSICAL_G_eligible_fresh_injective434 SP sm BP bm M cap x seen c hh g)
    have hw : sourceOriginalPhysicalGhostDistinctCoefficient434 SP sm BP bm M cap q rho N i Vb mu x c=0 := by
      unfold sourceOriginalPhysicalGhostDistinctCoefficient434
      apply Finset.prod_eq_zero (Finset.mem_univ g)
      simp only [sourceOriginalGhostDistinctCoefficient434,if_neg hg]
    simp only [if_neg he,hw,zero_mul]

/-- EXACT all-group original marked G expressed by OLD positions and
unordered distinct fresh ATOM sets. Its coefficients contain the original
q_i, eta_i, rho, V_g and birth law, with the original 1/b! already summed.
The arbitrary JOINT terminal function, numerical global birth indicator,
and both original cutoffs remain explicit. -/
theorem source_original_PHYSICAL_MARKED_G_set_extraction434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i Vb mu x seen F =
    ∑ d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x,
      sourceOriginalPhysicalGhostSetCoefficient434 SP sm BP bm M cap q rho N i Vb mu x d *
        sourceOriginalPhysicalGhostSetTest434 SP sm BP bm M cap x seen F d := by
  rw [source_original_PHYSICAL_MARKED_G_distinct_projection434]
  exact source_original_PHYSICAL_G_set_joint_transfer434 SP sm BP bm M cap
    q rho N i Vb mu x (sourceOriginalPhysicalGhostSetTest434 SP sm BP bm M cap x seen F)

/-- The same exact extraction inside the source Hilbert orbit average.
No 1/j! mass, repeated OLD multiplicity, or harmonic weight is replaced. -/
theorem source_original_PHYSICAL_SYMMETRIC_G_set_extraction434
    (J ell : ℕ) (q rho : ℝ) (N i : ℕ)
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N i Vs Vb mu y seen F =
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
      (fun x => ∑ d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm (J+ell) cap x,
        sourceOriginalPhysicalGhostSetCoefficient434 SP sm BP bm (J+ell) cap q rho N i Vb mu x d *
          sourceOriginalPhysicalGhostSetTest434 SP sm BP bm (J+ell) cap x seen F d) y := by
  unfold physicalMarkedSymmetricG
  congr 1
  funext x
  exact source_original_PHYSICAL_MARKED_G_set_extraction434 SP sm BP bm (J+ell) cap
    q rho N i Vb mu x seen F
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalGhostSetSaturated -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 18000000

def sourceOriginalGhostCanonicalFibre434
    {P : Type} [Fintype P] [DecidableEq P] (s : Finset P) :
    SourceOriginalGhostBirthFibre434 s.card s :=
  (sourceOriginalGhostBirthFibreEquiv434 s.card s).symm
    (Fintype.equivOfCardEq (by simp))

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

theorem source_original_PHYSICAL_G_set_eligible_card434
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x)
    (he : sourceOriginalPhysicalGhostSetEligible434 SP sm BP bm M cap x seen d) :
    ∀ g,(d g).2.card ≤ Fintype.card (BP g) := by
  intro g
  have hn := he.1
  change ((Finset.univ : Finset BG).toList.flatMap (fun g =>
    (d g).2.toList.map (fun z => bm g z.1))).Nodup at hn
  have hg := (List.nodup_flatMap.mp hn).1 g (by simp)
  have hp : ((d g).2.toList.map (fun z => z.1)).Nodup := by
    apply List.Nodup.of_map (bm g)
    simpa only [List.map_map,Function.comp_def] using hg
  simpa only [List.length_map,Finset.length_toList] using hp.length_le_card

def sourceOriginalPhysicalGhostSetLift434
    (x : FullPhysicalState SP sm BP bm M cap)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x)
    (hd : ∀ g,(d g).2.card ≤ cap g) : FullGhostWitness SP sm BP bm M cap x :=
  fun g => ⟨(d g).1,⟨⟨(d g).2.card,Nat.lt_succ_of_le (hd g)⟩,
    (sourceOriginalGhostCanonicalFibre434 (d g).2).1⟩⟩

/-- An explicit original ordered witness exists over EVERY set witness
whose birth counts fit. Surjectivity is proved, not postulated. -/
theorem source_original_PHYSICAL_G_set_lift434
    (x : FullPhysicalState SP sm BP bm M cap)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x)
    (hd : ∀ g,(d g).2.card ≤ cap g) :
    sourceOriginalPhysicalGhostSetProjection434 SP sm BP bm M cap x
      (sourceOriginalPhysicalGhostSetLift434 SP sm BP bm M cap x d hd) = d ∧
    ∀ g,Function.Injective
      ((sourceOriginalPhysicalGhostSetLift434 SP sm BP bm M cap x d hd g).2.2) := by
  constructor
  · funext g
    apply Prod.ext
    · rfl
    · exact (sourceOriginalGhostCanonicalFibre434 (d g).2).2.2
  · intro g
    exact (sourceOriginalGhostCanonicalFibre434 (d g).2).2.1

/-- Both the fresh-count cutoff and the target OLD-capacity cutoff are
discharged on the physical distinct/seen sector by cap_saturated. -/
theorem source_original_PHYSICAL_G_set_saturated_fits434
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hOld : sourceOriginalPhysicalPendingGroupDistinct434 SP sm BP bm M cap x)
    (hSeen : sourceOriginalPhysicalPendingSeen434 SP sm BP bm M cap x seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x)
    (he : sourceOriginalPhysicalGhostSetEligible434 SP sm BP bm M cap x seen d) :
    (∀ g,(d g).2.card ≤ cap g) ∧
      sourceOriginalPhysicalGhostSetFits434 SP sm BP bm M cap x d := by
  have hd : ∀ g,(d g).2.card ≤ cap g := fun g =>
    (source_original_PHYSICAL_G_set_eligible_card434 SP sm BP bm M cap x seen d he g).trans (hcap g)
  let c := sourceOriginalPhysicalGhostSetLift434 SP sm BP bm M cap x d hd
  have hl := source_original_PHYSICAL_G_set_lift434 SP sm BP bm M cap x d hd
  have hp : sourceOriginalPhysicalGhostSetProjection434 SP sm BP bm M cap x c=d := hl.1
  have hi : ∀ g,Function.Injective (c g).2.2 := hl.2
  have hc : physicalGhostBatchEligible SP sm BP bm M cap x seen c := by
    apply (source_original_PHYSICAL_G_set_gate434 SP sm BP bm M cap x seen c hi).mpr
    simpa only [hp] using he
  have hf := source_original_PHYSICAL_MARKED_G_cap_saturated434 SP sm BP bm M cap
    x seen c hOld hSeen hcap hc
  refine ⟨hd,?_⟩
  have hh := (source_original_PHYSICAL_G_set_fits434 SP sm BP bm M cap x c hi).mp hf
  simpa only [hp] using hh

def sourceOriginalPhysicalGhostSetUncutCoefficient434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap)
    (d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x) : ℂ :=
  ∏ g,
    (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))^(d g).1.1.card *
    (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)^
      ((zeroOld (fockToList ((x.2 g).2)) (fun z => z.2=0)).card-(d g).1.1.card) *
    (-((sourceVisitEta q N i:ℝ):ℂ)*(Vb g:ℂ)/(rho:ℂ))^(d g).2.card *
    (∏ z ∈ (d g).2,sourceBirthNu (fun p => (mu g p:ℂ)) z)

/-- Source G on the genuine sector, now with BOTH original cap tests
discharged. There is still one explicit global numeric eligibility test,
and the OLD-index and unordered-birth choices are coherently summed. -/
theorem source_original_PHYSICAL_MARKED_G_saturated_set_extraction434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hOld : sourceOriginalPhysicalPendingGroupDistinct434 SP sm BP bm M cap x)
    (hSeen : sourceOriginalPhysicalPendingSeen434 SP sm BP bm M cap x seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i Vb mu x seen F =
    ∑ d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm M cap x,
      if sourceOriginalPhysicalGhostSetEligible434 SP sm BP bm M cap x seen d then
        sourceOriginalPhysicalGhostSetUncutCoefficient434 SP sm BP bm M cap q rho N i Vb mu x d *
          F (sourceOriginalPhysicalGhostSetOutput434 SP sm BP bm M cap x d)
            (seen ∪ (sourceOriginalPhysicalGhostSetBirths434 SP sm BP bm M cap x d).toFinset)
      else 0 := by
  rw [source_original_PHYSICAL_MARKED_G_set_extraction434]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases he : sourceOriginalPhysicalGhostSetEligible434 SP sm BP bm M cap x seen d
  · obtain ⟨hcard,hfits⟩ := source_original_PHYSICAL_G_set_saturated_fits434 SP sm BP bm M cap
      x seen hOld hSeen hcap d he
    have hw : sourceOriginalPhysicalGhostSetCoefficient434 SP sm BP bm M cap q rho N i Vb mu x d =
        sourceOriginalPhysicalGhostSetUncutCoefficient434 SP sm BP bm M cap q rho N i Vb mu x d := by
      unfold sourceOriginalPhysicalGhostSetCoefficient434 sourceOriginalPhysicalGhostSetUncutCoefficient434
      apply Finset.prod_congr rfl
      intro g hg
      simp only [sourceOriginalGhostSetCoefficient434,if_pos (hcard g)]
    simp only [sourceOriginalPhysicalGhostSetTest434,if_pos he,if_pos hfits,hw]
  · simp only [sourceOriginalPhysicalGhostSetTest434,if_neg he,mul_zero]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryReachable -/

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
variable (M : ℕ) (cap : BG → ℕ)

theorem source_original_PHYSICAL_reachable_pending434
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen) :
    sourceOriginalPhysicalPendingGroupDistinct434 SP sm BP bm M cap x ∧
      sourceOriginalPhysicalPendingSeen434 SP sm BP bm M cap x seen := by
  have hl (g : BG) :
      (fockMultiset (x.2 g).2).map (fun z => bm g z.1) ≤
        sourceOriginalPhysicalInventory434 SP sm BP bm M
          (physicalFockProjection SP sm BP bm M cap x) := by
    apply le_trans (b := sourceOriginalBigInventory434 (bm g) M
      (x.2 g).1 (fockMultiset (x.2 g).2)) le_add_self
    have hh := Finset.sum_le_sum_of_subset
      (f := fun h : BG => sourceOriginalBigInventory434 (bm h) M
        (x.2 h).1 (fockMultiset (x.2 h).2))
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ g))
    simpa only [Finset.sum_singleton,sourceOriginalPhysicalInventory434,physicalFockProjection] using hh
  constructor
  · intro g
    have hn := Multiset.nodup_of_le (hl g) hx.1
    change (((fockToList (x.2 g).2).map (fun z => bm g z.1)) : List ℕ).Nodup at hn
    apply List.Nodup.of_map (bm g)
    simpa only [List.map_map,Function.comp_def] using hn
  · intro g p hp
    obtain ⟨z,hz,hzp⟩ := List.mem_map.mp hp
    apply hx.2
    apply Multiset.mem_of_le (hl g)
    exact Multiset.mem_map.mpr ⟨z,hz,congrArg (bm g) hzp⟩

/-- Original orbit compression respects the actual reachable sector
because the invariant is a function of its literal multiset projection. -/
theorem source_original_ORBIT_reachable_congr434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (f h : FullPhysicalState SP sm BP bm M cap → ℂ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen)
    (heq : ∀ x,sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen → f x = h x) :
    fullPhysicalOrbitAverage SP sm BP bm M cap Vs mu f y =
      fullPhysicalOrbitAverage SP sm BP bm M cap Vs mu h y := by
  unfold fullPhysicalOrbitAverage
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hp := (Finset.mem_filter.mp hx).2
  rw [heq x (by simpa only [hp] using hy)]

theorem source_original_MARKED_G_reachable_congr434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen)
    (F H : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ)
    (heq : ∀ y s,sourceOriginalPhysicalReachable434 SP sm BP bm M y s → F y s=H y s) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i V mu x seen F =
      physicalGBirthMarkedRow SP sm BP bm M cap q rho N i V mu x seen H := by
  unfold physicalGBirthMarkedRow
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro c hc
  by_cases he : physicalGhostBatchEligible SP sm BP bm M cap x seen c
  · simp only [if_pos he]
    by_cases ht : physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c=0
    · simp only [ht,zero_mul]
    · rw [heq _ _ (source_original_PHYSICAL_G_reachable434
        SP sm BP bm M cap q rho N i V mu x y seen c hx he ht)]
  · simp only [if_neg he]

variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

theorem source_original_SYMMETRIC_G_reachable_congr434
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (F H : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (heq : ∀ y s,sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y s → F y s=H y s) :
    physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N i Vs V mu y seen F =
      physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N i Vs V mu y seen H := by
  apply source_original_ORBIT_reachable_congr434 SP sm BP bm (J+ell) cap Vs mu _ _ y seen hy
  intro x hx
  exact source_original_MARKED_G_reachable_congr434
    SP sm BP bm (J+ell) cap q rho N i V mu x seen hx F H heq

theorem source_original_MARKED_E_reachable_congr434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (F H : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (heq : ∀ y s,sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y s → F y s=H y s) :
    physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F =
    physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen H := by
  unfold physicalOrientedBirthMarkedE
  apply Finset.sum_congr rfl
  intro z hz
  have hl := (Finset.mem_filter.mp hz).2
  by_cases he : orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z
  · simp only [if_pos he]
    rw [heq _ _ (source_original_SOURCE_ORIENTED_E_reachable434
      SP sm BP bm cap J ell m patterns x seen o k z hx hl he)]
  · simp only [if_neg he]

theorem source_original_SYMMETRIC_E_reachable_congr434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (F H : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (heq : ∀ y s,sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y s → F y s=H y s) :
    physicalOrientedMarkedSymmetricE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k y seen F =
    physicalOrientedMarkedSymmetricE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k y seen H := by
  apply source_original_ORBIT_reachable_congr434 SP sm BP bm (J+ell) cap Vs mu _ _ y seen hy
  intro x hx
  exact source_original_MARKED_E_reachable_congr434 SP sm BP bm cap J ell m patterns
    q rho Vs V mu K zeta theta o k x seen hx F H heq

/-- Source-faithful chain depends only on reachable terminal values.
The original orbit averaging, joint K, fixed phases and reverse-edge
transpose remain exactly those of memorySourceGEChain. -/
theorem source_original_MEMORY_chain_reachable_congr434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F H : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (heq : ∀ y s,sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y s → F y s=H y s)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    memorySourceGEChain SP sm BP bm J ell m patterns cap q rho Vs V mu K
      zeta theta k N n start F y seen =
    memorySourceGEChain SP sm BP bm J ell m patterns cap q rho Vs V mu K
      zeta theta k N n start H y seen := by
  induction n generalizing start y seen with
  | zero =>
      exact source_original_SYMMETRIC_G_reachable_congr434 SP sm BP bm cap J ell
        q rho N start Vs V mu y seen hy F H heq
  | succ n ih =>
      apply source_original_SYMMETRIC_G_reachable_congr434 SP sm BP bm cap J ell
        q rho N start Vs V mu y seen hy
      intro yg sg hg
      apply source_original_SYMMETRIC_E_reachable_congr434 SP sm BP bm cap J ell m patterns
        q rho Vs V mu _ zeta theta _ k yg sg hg
      intro ye se he
      exact ih (start+1) ye se he

theorem source_original_MEMORY_initial_reachable434
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (hv : physicalVacuum SP sm BP bm J ell y ≠ 0)
    (hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup) :
    sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y
      (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset := by
  have hp : ∀ g : BG,(y.2 g).2=0 := by
    by_contra h
    exact hv (if_neg h)
  have hi : sourceOriginalPhysicalInventory434 SP sm BP bm (J+ell) y =
      (physicalOutputInitialBirths SP sm BP bm J ell y : Multiset ℕ) := by
    unfold sourceOriginalPhysicalInventory434 sourceOriginalBigInventory434
    simp only [hp,Multiset.map_zero,add_zero]
    rw [physicalOutputInitialBirths,source_original_inventory_flatMap_bag434]
    simp_rw [source_original_inventory_indexed_bag434]
  change sourceOriginalInventoryValid434 _ _
  rw [hi]
  exact ⟨hn,fun p hp => List.mem_toFinset.mpr hp⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryReachableProjection -/

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

def sourceOriginalReachableCut434
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) : ℂ :=
  if sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen then F y seen else 0

/-- The literal source chain with the proved physical reachable-sector
indicator inserted before and after every G and E transition. -/
def sourceOriginalReachableGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,start,F => sourceOriginalReachableCut434 SP sm BP bm J ell
      (fun y seen => physicalMarkedSymmetricG SP sm BP bm J ell cap
        q rho N start Vs V mu y seen (sourceOriginalReachableCut434 SP sm BP bm J ell F))
  | n+1,start,F => sourceOriginalReachableCut434 SP sm BP bm J ell
      (fun y seen => physicalMarkedSymmetricG SP sm BP bm J ell cap
        q rho N start Vs V mu y seen
        (sourceOriginalReachableCut434 SP sm BP bm J ell (fun yg sg =>
          physicalOrientedMarkedSymmetricE SP sm BP bm J ell m cap patterns
            q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k yg sg
            (sourceOriginalReachableGEChain434 q rho Vs V mu K zeta theta k N n (start+1) F))))

theorem source_original_MEMORY_reachable_chain_exact434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    memorySourceGEChain SP sm BP bm J ell m patterns cap q rho Vs V mu K
      zeta theta k N n start F y seen =
    sourceOriginalReachableGEChain434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta k N n start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      simp only [sourceOriginalReachableGEChain434,sourceOriginalReachableCut434,
        if_pos hy,memorySourceGEChain]
      apply source_original_SYMMETRIC_G_reachable_congr434 SP sm BP bm cap J ell
        q rho N start Vs V mu y seen hy
      intro z s hz
      simp only [sourceOriginalReachableCut434,if_pos hz]
  | succ n ih =>
      simp only [sourceOriginalReachableGEChain434,sourceOriginalReachableCut434,
        if_pos hy,memorySourceGEChain]
      apply source_original_SYMMETRIC_G_reachable_congr434 SP sm BP bm cap J ell
        q rho N start Vs V mu y seen hy
      intro yg sg hg
      simp only [sourceOriginalReachableCut434,if_pos hg]
      apply source_original_SYMMETRIC_E_reachable_congr434 SP sm BP bm cap J ell m patterns
        q rho Vs V mu _ zeta theta _ k yg sg hg
      intro ye se he
      exact ih (start+1) ye se he

def sourceOriginalReachableMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalReachableGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N N 0
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- Exact full root restriction, with the original joint source K, signs,
Fourier/Mellin schedule, both vacuum factors and Fock measure unchanged.
No distinctness hypothesis is imposed on arbitrary ambient sectors. -/
theorem source_original_MEMORY_root_reachable_exact434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R =
    sourceOriginalReachableMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R := by
  unfold memorySourceRoot sourceOriginalReachableMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : physicalVacuum SP sm BP bm J ell y=0
  · simp only [hv,star_zero,mul_zero,zero_mul]
  · by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
    · simp only [if_pos hn]
      rw [source_original_MEMORY_reachable_chain_exact434
        SP sm BP bm J ell m cap patterns q rho Vs V _ K zeta theta k (2*R)
        _ (2*R) 0 y _ (source_original_MEMORY_initial_reachable434
          SP sm BP bm J ell y hv hn)]
    · simp only [if_neg hn]

/-- Applicable uncut G set formula on the actual reachable physical sector.
The hOld and hSeen premises of the previous saturated theorem are derived
here, including after all original E steps and orbit compressions. -/
theorem source_original_SYMMETRIC_G_reachable_uncut_set434
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalMarkedSymmetricG SP sm BP bm J ell cap q rho N i Vs V mu y seen F =
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
      (fun x => ∑ d : SourceOriginalPhysicalGhostSetWitness434 SP sm BP bm (J+ell) cap x,
        if sourceOriginalPhysicalGhostSetEligible434 SP sm BP bm (J+ell) cap x seen d then
          sourceOriginalPhysicalGhostSetUncutCoefficient434 SP sm BP bm (J+ell) cap q rho N i V mu x d *
            F (sourceOriginalPhysicalGhostSetOutput434 SP sm BP bm (J+ell) cap x d)
              (seen ∪ (sourceOriginalPhysicalGhostSetBirths434 SP sm BP bm (J+ell) cap x d).toFinset)
        else 0) y := by
  apply source_original_ORBIT_reachable_congr434 SP sm BP bm (J+ell) cap Vs mu _ _ y seen hy
  intro x hx
  obtain ⟨ho,hs⟩ := source_original_PHYSICAL_reachable_pending434
    SP sm BP bm (J+ell) cap x seen hx
  exact source_original_PHYSICAL_MARKED_G_saturated_set_extraction434
    SP sm BP bm (J+ell) cap q rho N i V mu x seen ho hs hcap F
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGhostReturnCancellation -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- A globally once-born prime, in coordinates before the accumulated
translation. Retired and unborn have the same empty pending state but
different seen histories. -/
inductive SourceOriginalGhostReturnState434 (R : Type)
  | unborn
  | pending (r : R)
  | retired
  deriving DecidableEq

/-- The actual zero-ghost coefficients at rho=1 in the sector where a
numerical prime may be born only once. Birth and deletion have negative
signs; surviving a zero visit costs 1-eta. -/
def sourceOriginalGhostReturnRow434 {R : Type} [DecidableEq R]
    (a : R) (eta lambda : ℝ)
    (F : SourceOriginalGhostReturnState434 R → ℝ) :
    SourceOriginalGhostReturnState434 R → ℝ
  | .unborn => F .unborn - eta*lambda*F (.pending a)
  | .pending r => if r=a then (1-eta)*F (.pending r)-eta*F .retired
      else F (.pending r)
  | .retired => F .retired

def sourceOriginalGhostReturnVacuum434 {R : Type} :
    SourceOriginalGhostReturnState434 R → ℝ
  | .unborn => 1
  | .pending _ => 0
  | .retired => 1

def sourceOriginalGhostReturnChain434 {R : Type} [DecidableEq R]
    (visits : List (R × ℝ)) (lambda : ℝ)
    (F : SourceOriginalGhostReturnState434 R → ℝ) :
    SourceOriginalGhostReturnState434 R → ℝ :=
  match visits with
  | [] => F
  | v::vs => sourceOriginalGhostReturnRow434 v.1 v.2 lambda
      (sourceOriginalGhostReturnChain434 vs lambda F)

def sourceOriginalGhostReturnSurvival434 {R : Type} [DecidableEq R] :
    List (R × ℝ) → R → ℝ
  | [], _ => 1
  | v::vs, r => (if r=v.1 then 1-v.2 else 1) *
      sourceOriginalGhostReturnSurvival434 vs r

/-- Sum of all single ghost lifespans: the first visit contributes its
birth eta; the future factor sums the possible later deletion times.
This includes every exact return, without any non-return assumption. -/
def sourceOriginalGhostReturnLoops434 {R : Type} [DecidableEq R] :
    List (R × ℝ) → ℝ
  | [] => 0
  | v::vs => v.2*(1-sourceOriginalGhostReturnSurvival434 vs v.1) +
      sourceOriginalGhostReturnLoops434 vs

theorem source_original_GHOST_RETURN_chain_exact434
    {R : Type} [DecidableEq R] (visits : List (R × ℝ)) (lambda : ℝ) :
    sourceOriginalGhostReturnChain434 visits lambda
        sourceOriginalGhostReturnVacuum434 .retired = 1 ∧
    (∀ r, sourceOriginalGhostReturnChain434 visits lambda
        sourceOriginalGhostReturnVacuum434 (.pending r) =
      -(1-sourceOriginalGhostReturnSurvival434 visits r)) ∧
    sourceOriginalGhostReturnChain434 visits lambda
        sourceOriginalGhostReturnVacuum434 .unborn =
      1+lambda*sourceOriginalGhostReturnLoops434 visits := by
  induction visits with
  | nil => simp [sourceOriginalGhostReturnChain434,
      sourceOriginalGhostReturnVacuum434,sourceOriginalGhostReturnSurvival434,
      sourceOriginalGhostReturnLoops434]
  | cons v vs ih =>
    rcases v with ⟨a,eta⟩
    refine ⟨?_,?_,?_⟩
    · exact ih.1
    · intro r
      simp only [sourceOriginalGhostReturnChain434,sourceOriginalGhostReturnRow434,
        sourceOriginalGhostReturnSurvival434]
      rw [ih.1,ih.2.1 r]
      split_ifs <;> ring
    · simp only [sourceOriginalGhostReturnChain434,sourceOriginalGhostReturnRow434,
        sourceOriginalGhostReturnLoops434]
      rw [ih.2.2,ih.2.1 a]
      ring

/-- Exact coherent cancellation over arbitrary residue-return classes. -/
theorem source_original_GHOST_RETURN_loops_defect434
    {R : Type} [Fintype R] [DecidableEq R] (visits : List (R × ℝ)) :
    sourceOriginalGhostReturnLoops434 visits =
      (visits.map Prod.snd).sum -
        ∑ r : R, (1-sourceOriginalGhostReturnSurvival434 visits r) := by
  induction visits with
  | nil => simp [sourceOriginalGhostReturnLoops434,sourceOriginalGhostReturnSurvival434]
  | cons v vs ih =>
    rcases v with ⟨a,eta⟩
    have hstep (r : R) :
        1-sourceOriginalGhostReturnSurvival434 ((a,eta)::vs) r =
        (1-sourceOriginalGhostReturnSurvival434 vs r) +
          if r=a then eta*sourceOriginalGhostReturnSurvival434 vs a else 0 := by
      by_cases h : r=a
      · subst r
        simp only [sourceOriginalGhostReturnSurvival434,ite_true]
        ring
      · simp only [sourceOriginalGhostReturnSurvival434,if_neg h,one_mul,add_zero]
    simp only [sourceOriginalGhostReturnLoops434,List.map_cons,List.sum_cons,ih]
    simp_rw [hstep]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    ring

theorem source_original_GHOST_RETURN_survival_unit434
    {R : Type} [DecidableEq R] (visits : List (R × ℝ))
    (heta : ∀ v ∈ visits, 0 ≤ v.2 ∧ v.2 ≤ 1) (r : R) :
    0 ≤ sourceOriginalGhostReturnSurvival434 visits r ∧
      sourceOriginalGhostReturnSurvival434 visits r ≤ 1 := by
  induction visits with
  | nil => simp [sourceOriginalGhostReturnSurvival434]
  | cons v vs ih =>
    have hv := heta v (List.mem_cons_self)
    have ht := ih (fun w hw => heta w (List.mem_cons_of_mem v hw))
    dsimp only [sourceOriginalGhostReturnSurvival434]
    split_ifs
    · constructor
      · exact mul_nonneg (sub_nonneg.mpr hv.2) ht.1
      · exact mul_le_one₀ (by linarith only [hv.1]) ht.1 ht.2
    · simpa only [one_mul] using ht

/-- The original b_p and the tilted zero-atom mass cancel the entire
once-born ghost return sum. The result is a genuine residue average,
uniform in the number and pattern of visits. -/
theorem source_original_GHOST_RETURN_BASELINE_residue_average434
    {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
    (visits : List (R × ℝ))
    (hb : 1-(visits.map Prod.snd).sum/(Fintype.card R : ℝ) ≠ 0) :
    let p : ℝ := Fintype.card R
    let b := 1-(visits.map Prod.snd).sum/p
    b * sourceOriginalGhostReturnChain434 visits (1/(p*b))
      sourceOriginalGhostReturnVacuum434 .unborn =
      (∑ r : R,sourceOriginalGhostReturnSurvival434 visits r)/p := by
  dsimp only
  rw [(source_original_GHOST_RETURN_chain_exact434 visits _).2.2,
    source_original_GHOST_RETURN_loops_defect434]
  have hp : (Fintype.card R : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α:=R))
  have hs : (∑ r : R,(1-sourceOriginalGhostReturnSurvival434 visits r)) =
      (Fintype.card R : ℝ) - ∑ r : R,sourceOriginalGhostReturnSurvival434 visits r := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hs]
  have hps : (Fintype.card R : ℝ) - (visits.map Prod.snd).sum ≠ 0 := by
    intro h
    have he := (sub_eq_zero.mp h).symm
    apply hb
    simp only [he,div_self hp,sub_self]
  field_simp [hp,hps]
  <;> ring

theorem source_original_GHOST_RETURN_BASELINE_unit434
    {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
    (visits : List (R × ℝ))
    (heta : ∀ v ∈ visits, 0 ≤ v.2 ∧ v.2 ≤ 1)
    (hb : 1-(visits.map Prod.snd).sum/(Fintype.card R : ℝ) ≠ 0) :
    let p : ℝ := Fintype.card R
    let b := 1-(visits.map Prod.snd).sum/p
    0 ≤ b * sourceOriginalGhostReturnChain434 visits (1/(p*b))
        sourceOriginalGhostReturnVacuum434 .unborn ∧
    b * sourceOriginalGhostReturnChain434 visits (1/(p*b))
        sourceOriginalGhostReturnVacuum434 .unborn ≤ 1 := by
  dsimp only
  rw [source_original_GHOST_RETURN_BASELINE_residue_average434 visits hb]
  have hp : (0:ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun r _ =>
      (source_original_GHOST_RETURN_survival_unit434 visits heta r).1)) hp.le
  · apply (div_le_iff₀ hp).mpr
    calc
      _ ≤ ∑ _r : R, (1:ℝ) := Finset.sum_le_sum (fun r _ =>
        (source_original_GHOST_RETURN_survival_unit434 visits heta r).2)
      _ = _ := by simp
end Green64Analytic.CorrelationSquare

end

end

