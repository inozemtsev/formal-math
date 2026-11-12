module

public import Green64.Library.Correlation.Part056
public import Green64.Library.Weights.ActualFrameFilteredLiteral

@[expose] public section

/-!
# Weights / Part078

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMarkedFullOrbitCleanHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 700000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
variable (cap : BG → ℕ)

local notation "Small" => GroupState SP sm (J+ell)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Out" => FullPhysicalOutput SP sm BP bm (J+ell)
local notation "Sector" => SourceOriginalMarkedSectorIndex434 BP cap
local notation "SPerm" => GroupPermFamily (G := SG) (J+ell)
local notation "BPerm" => BigGroupPerm (BG := BG) (J+ell)
local notation "pat" => sourceOriginalProbeMemoryPattern434 J m hmJ nu
local notation "Frame" => SourceBigAux BP J m pat × (BPerm × BPerm) × (SPerm × SPerm)

/-- The joint coefficient may depend on the ACTUAL frozen pending sector. -/
abbrev SourceOriginalMarkedFullSectorK434 :=
  (d : Sector) → Frame → Shared →
    memoryFrozenResidueGroup SP sm BP bm (fun g => (d.1 g).val) d.2 →
    A → Finset ℕ → A → ℂ

/-- Assemble the verified literal CLEAN channels on every actual ordered
sector, with the SAME future and the original numerical history update. -/
def sourceOriginalMarkedFullOrderedClean434
    (o k : ℤ) (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourceOriginalMarkedFullSectorK434 SP sm BP bm J ell m hmJ nu cap)
    (f : State → Finset ℕ → ℂ) (x : State) (S : Finset ℕ) : ℂ :=
  let z := sourceOriginalMarkedSectorEquiv434 SP sm BP bm J ell cap x
  sourceOriginalMarkedPhysicalCleanMean434 SP sm BP bm J ell m hmJ nu
    cap (fun g => (z.1.1 g).val) (fun g => Nat.le_of_lt_succ (z.1.1 g).isLt) z.1.2
    o k q Vs Vb mu (K z.1)
    (fun xs a S t => f (sourceOriginalMarkedSectorEmbed434 SP sm BP bm J ell cap z.1 xs a t) S)
    z.2.1.1 z.2.2 S z.2.1.2

theorem source_original_MARKED_full_ordered_sector434
    (o k : ℤ) (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourceOriginalMarkedFullSectorK434 SP sm BP bm J ell m hmJ nu cap)
    (f : State → Finset ℕ → ℂ) (d : Sector) (xs : Small) (a : A)
    (S : Finset ℕ) (t : SourceOriginalMarkedSectorOld434 BP bm cap d) :
    sourceOriginalMarkedFullOrderedClean434 SP sm BP bm J ell m hmJ nu cap
      o k q Vs Vb mu K f
      (sourceOriginalMarkedSectorEmbed434 SP sm BP bm J ell cap d xs a t) S =
    sourceOriginalMarkedPhysicalCleanMean434 SP sm BP bm J ell m hmJ nu
      cap (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2
      o k q Vs Vb mu (K d)
      (fun ys b T u => f (sourceOriginalMarkedSectorEmbed434 SP sm BP bm J ell cap d ys b u) T)
      xs a S t := by
  rfl

/-- FULL ordered Fock x seen estimate. Direct summation costs NO number
of pending sectors, ordered histories, or permutations. -/
theorem source_original_MARKED_FULL_ORDERED_CLEAN_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (o k : ℤ) (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g,(∑ p : BP g,1/(bm g p:ℝ))=Vb g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (C : ℝ) (hC : 0 ≤ C)
    (K : SourceOriginalMarkedFullSectorK434 SP sm BP bm J ell m hmJ nu cap)
    (hK : ∀ d r e y a S b,‖K d r e y a S b‖ ≤ C)
    (f : State → Finset ℕ → ℂ) :
    sourceOriginalMarkedOrderedEnergy434 SP sm BP bm J ell cap Vs Vb mu
      (sourceOriginalMarkedFullOrderedClean434 SP sm BP bm J ell m hmJ nu cap
        o k q Vs Vb mu K f) ≤
    (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      (C^2*(∏ g : BG,((∑ p : BP g,mu g p)^2/4)^
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)) *
      sourceOriginalMarkedOrderedEnergy434 SP sm BP bm J ell cap Vs Vb mu f := by
  rw [source_original_MARKED_ordered_energy_sectors434,
    source_original_MARKED_ordered_energy_sectors434,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  simp only [source_original_MARKED_full_ordered_sector434]
  exact source_original_MARKED_PHYSICAL_mean_Hilbert434 SP sm BP bm J ell m hmJ nu
    cap (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2
    hi o k q hq hq1 Vs hVs Vb hVb hHarmonic mu hmu C hC (K d) (hK d) _

/-- Original weighted orbit compression of the full marked channel. -/
def sourceOriginalMarkedFullOrbitClean434
    (o k : ℤ) (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourceOriginalMarkedFullSectorK434 SP sm BP bm J ell m hmJ nu cap)
    (F : Out → Finset ℕ → ℂ) (X : Out) (S : Finset ℕ) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
    (fun x => sourceOriginalMarkedFullOrderedClean434 SP sm BP bm J ell m hmJ nu cap
      o k q Vs Vb mu K
      (fun y T => F (physicalFockProjection SP sm BP bm (J+ell) cap y) T) x S) X

/-- FULL orbit/history Hilbert estimate in the unchanged physical density.
K remains joint and may depend on every actual OLD-sector coordinate. -/
theorem source_original_MARKED_FULL_ORBIT_CLEAN_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (o k : ℤ) (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g,(∑ p : BP g,1/(bm g p:ℝ))=Vb g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (C : ℝ) (hC : 0 ≤ C)
    (K : SourceOriginalMarkedFullSectorK434 SP sm BP bm J ell m hmJ nu cap)
    (hK : ∀ d r e y a S b,‖K d r e y a S b‖ ≤ C)
    (F : Out → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu
      (sourceOriginalMarkedFullOrbitClean434 SP sm BP bm J ell m hmJ nu cap
        o k q Vs Vb mu K F) ≤
    (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      (C^2*(∏ g : BG,((∑ p : BP g,mu g p)^2/4)^
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)) *
      sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu F := by
  apply le_trans (source_original_MARKED_orbit_compression_energy434 SP sm BP bm
    J ell cap Vs Vb mu hVs hVb hmu _)
  have h := source_original_MARKED_FULL_ORDERED_CLEAN_Hilbert434 SP sm BP bm J ell m hmJ nu
    cap hi o k q hq hq1 Vs hVs Vb hVb hHarmonic mu hmu C hC K hK
    (fun y S => F (physicalFockProjection SP sm BP bm (J+ell) cap y) S)
  rw [source_original_MARKED_ordered_orbit_energy434] at h
  exact h

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMarkedCleanBirthLiteral -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 600000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ)
local notation "A" => SourceOriginalB26Active434 BP J ell

/-- The true CLEAN birth LIST after the target permutation.
Multiplicity remains visible to the global Nodup gate. -/
def sourceOriginalMarkedCleanBirthNumbers434 (pat : SourcePattern BG J m) (b : A) : List ℕ :=
  (Finset.univ : Finset BG).toList.flatMap (fun g =>
    (Finset.univ \ sourceBigShared J ell m pat g).toList.map (fun i => bm g (b g i)))

theorem source_original_MARKED_CLEAN_birth_mem434
    (pat : SourcePattern BG J m) (b : A) (p : ℕ) :
    p ∈ sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m pat b ↔
      ∃ g,∃ i : Fin (J+ell),i ∉ sourceBigShared J ell m pat g ∧ bm g (b g i)=p := by
  simp only [sourceOriginalMarkedCleanBirthNumbers434,List.mem_flatMap,
    Finset.mem_toList,Finset.mem_univ,true_and,List.mem_map,Finset.mem_sdiff]

/-- Exact equality with the old split-coordinate birth SET.
This equality does not drop the separate Nodup requirement on the list. -/
theorem source_original_MARKED_CLEAN_birth_set434
    (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) (b : A) :
    (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) b).toFinset =
    (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu b).image
      (fun p : Sigma BP => bm p.1 p.2) := by
  ext p
  rw [List.mem_toFinset,source_original_MARKED_CLEAN_birth_mem434]
  constructor
  · rintro ⟨g,i,hi,he⟩
    let j := (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ nu g).symm ⟨i,hi⟩
    refine Finset.mem_image.mpr ⟨⟨g,b g i⟩,?_,he⟩
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,?_⟩⟩
    change b g (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ nu g j).val = b g i
    simp only [j,Equiv.apply_symm_apply]
  · intro hp
    obtain ⟨⟨g,v⟩,hv,hp⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp (Finset.mem_sigma.mp hv).2
    let i := sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ nu g j
    refine ⟨g,i.val,i.property,?_⟩
    exact (congrArg (bm g) he).trans hp

variable (cap sizes : BG → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "Small" => GroupState SP sm (J+ell)
local notation "Old" => SourceOriginalB26OldResidues434 BP bm sizes prime
local notation "Frame" => SourceOriginalB26FrozenFrame434 BP J ell m patterns
local notation "SPerm" => GroupPermFamily (G := SG) (J+ell)

/-- Literal original CLEAN births are the same numerical LIST.
Every endpoint permutation and every repeated prime is retained. -/
theorem source_original_MARKED_CLEAN_births_literal434
    (xs ys : Small) (a b : A) (t : Old) (h : Frame) (ss tt : SPerm) :
    orientedEFreshBirths SP sm BP bm J ell m cap patterns
      (sourceOriginalB26FrozenOriginalChoice434 SP sm BP bm
        J ell m cap sizes hsizes prime patterns xs ys a (0,t) h b ss tt) =
    sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m (patterns h.1)
      (fun g i => b g (h.2.2.2 g i)) := by
  simp only [orientedEFreshBirths,sourceOriginalB26FrozenOriginalChoice434,
    sourceOriginalB26EmptyCleanChoice434,orientedFresh,orientedUnshared,
    Finset.sdiff_empty,sourceOriginalMarkedCleanBirthNumbers434]

/-- Equivalence of the two already used literal CLEAN predicates. -/
theorem source_original_MARKED_CLEAN_predicate434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns x z ↔
    memorySourceCleanChoice SP sm BP bm J ell m cap patterns x z := by
  simp only [sourceOriginalCleanChoice434,memorySourceCleanChoice,
    not_exists,Finset.not_nonempty_iff_eq_empty]
  constructor
  · rintro ⟨hp,hs⟩ g
    exact ⟨hs g,hp g⟩
  · intro h
    exact ⟨fun g => (h g).2,fun g => (h g).1⟩

/-- The SMALL shared product agrees with the actual frozen labels. -/
theorem source_original_MARKED_SMALL_shared_divisor434
    (xs : Small) (ss : SPerm) :
    sourceOriginalB26SmallSourceD434 SP sm J ell xs ss =
    sourceOriginalB26SmallTupleD434 SP sm J ell
      (memoryOriginalSmallGroupSharedLabels SP sm (J+ell) (sourceSmallShared J ell) ss xs) := by
  unfold sourceOriginalB26SmallSourceD434 sourceOriginalB26SmallTupleD434
  apply Finset.prod_congr rfl
  intro g hg
  simpa only [Finset.univ_eq_attach,memoryOriginalSmallGroupSharedLabels,
    memoryOriginalSmallSharedLabels] using
    (Finset.prod_attach (sourceSmallShared J ell g)
      (fun i => sm g (marks (sm g) (J+ell) (xs g) (ss g i)))).symm

end Green64Analytic.CorrelationSquare

end

end

