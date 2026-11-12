module

public import Green64.Library.Correlation.PhysicalGhostWitnessCollapse

@[expose] public section

/-!
# Correlation / PhysicalGhostSaturated

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalGhostSaturated -/

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

def sourceOriginalPhysicalPendingGroupDistinct434
    (x : FullPhysicalState SP sm BP bm M cap) : Prop :=
  ∀ g, ((fockToList ((x.2 g).2)).map (fun z => z.1)).Nodup

def sourceOriginalPhysicalPendingSeen434
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ) : Prop :=
  ∀ g p, p ∈ (fockToList ((x.2 g).2)).map (fun z => z.1) → bm g p ∈ seen

private theorem fresh_mem_global
    (x : FullPhysicalState SP sm BP bm M cap)
    (c : FullGhostWitness SP sm BP bm M cap x) (g : BG) (p : BP g)
    (hp : p ∈ (List.ofFn (c g).2.2).map (fun z => z.1)) :
    bm g p ∈ (physicalGhostFreshBirths SP sm BP bm M cap x c).toFinset := by
  apply List.mem_toFinset.mpr
  unfold physicalGhostFreshBirths
  apply List.mem_flatMap.mpr
  refine ⟨g,by simp,?_⟩
  obtain ⟨z,hz,hzp⟩ := List.mem_map.mp hp
  exact List.mem_map.mpr ⟨z,hz,congrArg (bm g) hzp⟩

private theorem after_nodup
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (hOld : sourceOriginalPhysicalPendingGroupDistinct434 SP sm BP bm M cap x)
    (hSeen : sourceOriginalPhysicalPendingSeen434 SP sm BP bm M cap x seen)
    (he : physicalGhostBatchEligible SP sm BP bm M cap x seen c) (g : BG) :
    ((afterGhost (fockToList ((x.2 g).2)) (c g).1.1 (c g).2.2).map
      (fun z => z.1)).Nodup := by
  have hn := he.1
  change ((Finset.univ : Finset BG).toList.flatMap (fun g =>
    (List.ofFn (c g).2.2).map (fun z => bm g z.1))).Nodup at hn
  have hg := (List.nodup_flatMap.mp hn).1 g (by simp)
  have hFresh : ((List.ofFn (c g).2.2).map (fun z => z.1)).Nodup := by
    apply List.Nodup.of_map (bm g)
    simpa only [List.map_map,Function.comp_def] using hg
  apply original_ghost_afterGhost_prime_nodup (bm g)
    (fockToList ((x.2 g).2)) (c g).1.1 (c g).2.2 (hOld g) hFresh
  intro a ha v hv hav
  have hs := hSeen g a ha
  have hb := fresh_mem_global SP sm BP bm M cap x c g v hv
  exact (Finset.disjoint_left.mp he.2 hs) (by simpa only [hav] using hb)

/-- Original cap_saturated suffices on the genuine distinct-birth sector.
The proof uses OLD membership in seen and the global numeric birth gate;
it does not assume that the ambient Fock carrier is a set. -/
theorem source_original_PHYSICAL_MARKED_G_cap_saturated434
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (hOld : sourceOriginalPhysicalPendingGroupDistinct434 SP sm BP bm M cap x)
    (hSeen : sourceOriginalPhysicalPendingSeen434 SP sm BP bm M cap x seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (he : physicalGhostBatchEligible SP sm BP bm M cap x seen c) :
    sourceOriginalPhysicalGhostWitnessFits434 SP sm BP bm M cap x c := by
  intro g
  have hn := after_nodup SP sm BP bm M cap x seen c hOld hSeen he g
  have hl : (afterGhost (fockToList ((x.2 g).2)) (c g).1.1 (c g).2.2).length ≤
      Fintype.card (BP g) := by
    simpa only [List.length_map] using hn.length_le_card
  exact hl.trans (hcap g)

/-- The actual nonzero G branch propagates pending-prime distinctness
and membership in the updated numerical seen set. Repeated-atom sectors
remain in the full carrier; no unsupported invariant is assigned to them. -/
theorem source_original_PHYSICAL_MARKED_G_pending_invariant434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (c : FullGhostWitness SP sm BP bm M cap x)
    (hOld : sourceOriginalPhysicalPendingGroupDistinct434 SP sm BP bm M cap x)
    (hSeen : sourceOriginalPhysicalPendingSeen434 SP sm BP bm M cap x seen)
    (he : physicalGhostBatchEligible SP sm BP bm M cap x seen c)
    (ht : physicalGBranchTerm SP sm BP bm M cap q rho N i Vb mu x y c ≠ 0) :
    sourceOriginalPhysicalPendingGroupDistinct434 SP sm BP bm M cap y ∧
    sourceOriginalPhysicalPendingSeen434 SP sm BP bm M cap y
      (seen ∪ (physicalGhostFreshBirths SP sm BP bm M cap x c).toFinset) := by
  obtain ⟨_,hout⟩ := physical_nonzero_ghost_witness_is_operational
    SP sm BP bm M cap q rho N i Vb mu x y c ht
  constructor
  · intro g
    rw [←hout g]
    exact after_nodup SP sm BP bm M cap x seen c hOld hSeen he g
  · intro g p hp
    rw [←hout g] at hp
    simp only [afterGhost,List.map_append,List.map_map,List.mem_append] at hp
    rcases hp with hp|hp
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
      apply Finset.mem_union_left
      exact hSeen g _ (List.mem_map.mpr
        ⟨(fockToList ((x.2 g).2)).get j,List.get_mem _ j,rfl⟩)
    · exact Finset.mem_union_right _
        (fresh_mem_global SP sm BP bm M cap x c g p hp)

/-- Exact source marked G row with the saturated cutoff discharged.
All OLD subsets, ordered births, source signs, factorials, and the joint
terminal test remain inside the original witness sum. -/
theorem source_original_PHYSICAL_MARKED_G_saturated_row434
    (q rho : ℝ) (N i : ℕ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hOld : sourceOriginalPhysicalPendingGroupDistinct434 SP sm BP bm M cap x)
    (hSeen : sourceOriginalPhysicalPendingSeen434 SP sm BP bm M cap x seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i Vb mu x seen F =
    ∑ c : FullGhostWitness SP sm BP bm M cap x,
      if he : physicalGhostBatchEligible SP sm BP bm M cap x seen c then
        sourceOriginalPhysicalGhostWitnessCoefficient434 SP sm BP bm M cap q rho N i Vb mu x c *
          F (physicalFockProjection SP sm BP bm M cap
            (sourceOriginalPhysicalGhostWitnessTarget434 SP sm BP bm M cap x c
              (source_original_PHYSICAL_MARKED_G_cap_saturated434 SP sm BP bm M cap
                x seen c hOld hSeen hcap he)))
            (seen ∪ (physicalGhostFreshBirths SP sm BP bm M cap x c).toFinset)
      else 0 := by
  classical
  rw [source_original_PHYSICAL_MARKED_G_target_collapse434]
  unfold sourceOriginalPhysicalMarkedGhostCollapsed434
  apply Finset.sum_congr rfl
  intro c hc
  by_cases he : physicalGhostBatchEligible SP sm BP bm M cap x seen c
  · have hf := source_original_PHYSICAL_MARKED_G_cap_saturated434
      SP sm BP bm M cap x seen c hOld hSeen hcap he
    simp only [if_pos he,dif_pos he,dif_pos hf]
  · simp [he]
end Green64Analytic.CorrelationSquare

end

end

