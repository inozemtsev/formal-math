module

public import Green64.Library.Weights.Part092
public import Green64.Library.Correlation.MemoryGEDampingCancellation
public import Green64.Library.Correlation.Part006
public import Green64.Library.Weights.Part087
public import Green64.Library.Correlation.Part045
public import Green64.Library.Correlation.Part044
public import Green64.Library.Weights.Part030
public import Green64.Library.Correlation.Part032
public import Green64.Library.Weights.Part090
public import Green64.Library.Correlation.Part031
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Weights / Part093

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredIdealSeenErased -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- The true total OLD size, with all repeated pending occurrences. -/
def sourceOriginalUnfilteredIdealOLD434 (T : ℕ) (X : Output) : Prop :=
  (∑ g : BG,((X.2 g).2).card) ≤ T

/-- NEW derived seen-erased CLEAN on the full symmetric physical Fock
support. Both original OLD gates, the true fresh LIST Nodup, all legality,
the actual full K orientation and weighted orbit average are present.
No seen index, reachable-history carrier or initial inventory restriction. -/
def sourceOriginalUnfilteredIdealSeenErasedClean434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (T : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F : Output → ℂ) (X : Output) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
    (fun x =>
      if sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
        (physicalFockProjection SP sm BP bm (J+ell) cap x) then
        sourceOriginalUnfilteredIdealLocalClean434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k x
            (fun Y => if sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T Y
              then F Y else 0)
      else 0) X

def sourceOriginalUnfilteredIdealOrbitEnergy434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (F : Output → ℂ) : ℝ :=
  ∑ X ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
    physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu X * ‖F X‖^2

theorem source_original_unfiltered_ideal_LOCAL_CLEAN_RHO434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : State) (F : Output → ℂ) :
    sourceOriginalUnfilteredIdealLocalClean434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x F =
    sourceOriginalMemoryOldInput434 SP sm BP bm J ell cap rho x *
      sourceOriginalUnfilteredIdealLocalClean434 SP sm BP bm J ell m cap patterns
        q 1 Vs V mu K zeta theta o k x
        (fun Y => sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho Y*F Y) := by
  unfold sourceOriginalUnfilteredIdealLocalClean434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs
  · rw [source_original_memory_OLD_source_coefficient_sandwich434]
    ring
  · simp

/-- Orbit-constant multipliers pull through the ACTUAL weighted quotient,
including zero-mass fibres. No counting or factorial normalization is changed. -/
theorem source_original_unfiltered_ideal_ORBIT_MULTIPLIER434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (D : Output → ℂ) (f : State → ℂ) (X : Output) :
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
      (fun x => D (physicalFockProjection SP sm BP bm (J+ell) cap x)*f x) X =
    D X*fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X := by
  unfold fullPhysicalOrbitAverage
  have he :
      (∑ x ∈ (Finset.univ : Finset State) with
          physicalFockProjection SP sm BP bm (J+ell) cap x=X,
        (fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x:ℂ)*
          (D (physicalFockProjection SP sm BP bm (J+ell) cap x)*f x)) =
      D X*(∑ x ∈ (Finset.univ : Finset State) with
          physicalFockProjection SP sm BP bm (J+ell) cap x=X,
        (fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x:ℂ)*f x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
    ring
  rw [he]
  ring

/-- Literal same-density rho sandwich on the complete seen-erased quotient
with both OLD gates and the actual fresh-batch filter. -/
theorem source_original_unfiltered_ideal_SEEN_ERASED_RHO434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (T : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F : Output → ℂ) (X : Output) :
    sourceOriginalUnfilteredIdealSeenErasedClean434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K T zeta theta o k F X =
    sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho X *
      sourceOriginalUnfilteredIdealSeenErasedClean434 SP sm BP bm J ell m cap patterns
        q 1 Vs V mu K T zeta theta o k
        (fun Y => sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho Y*F Y) X := by
  let D := sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho
  let gate := sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
  have hf : (fun Y : Output => D Y*(if gate Y then F Y else 0)) =
      (fun Y : Output => if gate Y then D Y*F Y else 0) := by
    funext Y
    split_ifs <;> simp
  have he :
      (fun x : State => if gate (physicalFockProjection SP sm BP bm (J+ell) cap x) then
        sourceOriginalUnfilteredIdealLocalClean434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k x (fun Y => if gate Y then F Y else 0)
        else 0) =
      (fun x : State => D (physicalFockProjection SP sm BP bm (J+ell) cap x)*
        (if gate (physicalFockProjection SP sm BP bm (J+ell) cap x) then
          sourceOriginalUnfilteredIdealLocalClean434 SP sm BP bm J ell m cap patterns
            q 1 Vs V mu K zeta theta o k x (fun Y => if gate Y then D Y*F Y else 0)
          else 0)) := by
    funext x
    split_ifs
    · rw [source_original_unfiltered_ideal_LOCAL_CLEAN_RHO434]
      rw [← source_original_memory_OLD_projection434 SP sm BP bm J ell cap rho x]
      change D _ * _ = D _ * _
      rw [hf]
    · simp
  unfold sourceOriginalUnfilteredIdealSeenErasedClean434
  change fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu _ X =
    D X*fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu _ X
  rw [he]
  exact source_original_unfiltered_ideal_ORBIT_MULTIPLIER434
    SP sm BP bm J ell cap Vs mu D _ X

/-- Both OLD endpoint diagonal multipliers contract in the SAME original
physical orbit density. This theorem includes repeated OLD atoms. -/
theorem source_original_unfiltered_ideal_ORBIT_DAMPING_ENERGY434
    (rho : ℝ) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (F : Output → ℂ) :
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (fun X => sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho X*F X) ≤
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  unfold sourceOriginalUnfilteredIdealOrbitEnergy434
  apply Finset.sum_le_sum
  intro X hX
  have hw := (physicalOrbitMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu X hX).le
  apply mul_le_mul_of_nonneg_left _ hw
  rw [norm_mul,mul_pow]
  have hd := pow_le_pow_left₀ (norm_nonneg _)
    (source_original_memory_OLD_output_norm_le_one434 SP sm BP bm J ell rho hr0 hr1 X) 2
  simpa only [one_pow,one_mul] using
    mul_le_mul_of_nonneg_right hd (sq_nonneg ‖F X‖)

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionDecomposition -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Literal original local FULL E, retaining the numerical birth LIST filter
and all source legality, orientation, coefficient and output definitions. -/
def sourceOriginalUnfilteredEvolutionLocalFull434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : State) (F : Output → ℂ) : ℂ :=
  ∑ z ∈ sourceOrientedPhysicalChoices SP sm BP bm J ell m cap patterns x o k,
    if (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup then
      sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu (memoryOrientationK BP J ell m patterns K o) zeta theta o k x z*
        F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
    else 0

/-- Literal DIRTY restriction: the complement of the original CLEAN choice
predicate on exactly the same original source witnesses. -/
def sourceOriginalUnfilteredEvolutionLocalDirty434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : State) (F : Output → ℂ) : ℂ :=
  ∑ z ∈ sourceOrientedPhysicalChoices SP sm BP bm J ell m cap patterns x o k,
    if ¬memorySourceCleanChoice SP sm BP bm J ell m cap patterns x z ∧
      (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup then
      sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu (memoryOrientationK BP J ell m patterns K o) zeta theta o k x z*
        F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
    else 0

theorem source_original_evolution_LOCAL_FULL_SPLIT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : State) (F : Output → ℂ) :
    sourceOriginalUnfilteredEvolutionLocalFull434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x F =
    sourceOriginalUnfilteredIdealLocalClean434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x F +
    sourceOriginalUnfilteredEvolutionLocalDirty434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x F := by
  unfold sourceOriginalUnfilteredEvolutionLocalFull434
    sourceOriginalUnfilteredIdealLocalClean434 sourceOriginalUnfilteredEvolutionLocalDirty434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hc : memorySourceCleanChoice SP sm BP bm J ell m cap patterns x z <;>
    by_cases hn : (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup <;>
      simp [hc,hn]

def sourceOriginalUnfilteredEvolutionSeenErasedFull434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (T : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F : Output → ℂ) (X : Output) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
    (fun x => if sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
        (physicalFockProjection SP sm BP bm (J+ell) cap x) then
      sourceOriginalUnfilteredEvolutionLocalFull434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x
        (fun Y => if sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T Y then F Y else 0)
      else 0) X

def sourceOriginalUnfilteredEvolutionSeenErasedDirty434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (T : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F : Output → ℂ) (X : Output) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
    (fun x => if sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
        (physicalFockProjection SP sm BP bm (J+ell) cap x) then
      sourceOriginalUnfilteredEvolutionLocalDirty434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x
        (fun Y => if sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T Y then F Y else 0)
      else 0) X

theorem source_original_evolution_ORBIT_add434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (f g : State → ℂ) (X : Output) :
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu (fun x => f x+g x) X =
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X+
      fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu g X := by
  unfold fullPhysicalOrbitAverage
  simp_rw [mul_add,Finset.sum_add_distrib,add_div]

/-- Exact same-row decomposition with BOTH original total-OLD gates and
the true local birth LIST filter. This asserts no DIRTY estimate. -/
theorem source_original_evolution_SEEN_ERASED_FULL_SPLIT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (T : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F : Output → ℂ) (X : Output) :
    sourceOriginalUnfilteredEvolutionSeenErasedFull434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K T zeta theta o k F X =
    sourceOriginalUnfilteredIdealSeenErasedClean434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K T zeta theta o k F X+
    sourceOriginalUnfilteredEvolutionSeenErasedDirty434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K T zeta theta o k F X := by
  unfold sourceOriginalUnfilteredEvolutionSeenErasedFull434
    sourceOriginalUnfilteredIdealSeenErasedClean434 sourceOriginalUnfilteredEvolutionSeenErasedDirty434
  rw [←source_original_evolution_ORBIT_add434]
  apply congrArg (fun f : State → ℂ =>
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext x
  by_cases h : sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
      (physicalFockProjection SP sm BP bm (J+ell) cap x)
  · simp only [h,if_true]
    exact source_original_evolution_LOCAL_FULL_SPLIT434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x _
  · simp [h]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEdgeDomination -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 2400000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Exact witness-phase extension on the unchanged legal carrier. The
arbitrary phase is allowed to depend on every OLD state and witness. -/
def sourceOriginalUnfilteredEdgePhasedLocal434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (phase : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → ℂ)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : Output → ℂ) (st : State) : ℂ :=
  ∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st,
    if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns st o k z ∧ keep st z then
      phase st z*sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k st z *
      F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z) else 0

theorem source_original_edge_PHASED_LOCAL_DOMINATION434
    (keep envelope : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (hkeep : ∀ st z,keep st z → envelope st z)
    (phase : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → ℂ)
    (hphase : ∀ st z,‖phase st z‖ ≤ 1)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : Output → ℂ) (st : State) :
    ‖sourceOriginalUnfilteredEdgePhasedLocal434 SP sm BP bm J ell m cap patterns
      keep phase q rho Vs V mu K zeta theta o k F st‖ ≤
    ∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st,
      if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns st o k z ∧ envelope st z then
        ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k st z‖ *
        ‖F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z)‖ else 0 := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro z _
  by_cases h : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns st o k z ∧ keep st z
  · rw [if_pos h,if_pos ⟨h.1,hkeep st z h.2⟩,norm_mul,norm_mul]
    have hp := mul_le_mul_of_nonneg_right (hphase st z)
      (norm_nonneg (sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k st z))
    have hp' : ‖phase st z‖ * ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k st z‖ ≤
      ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k st z‖ := by simpa only [one_mul] using hp
    exact mul_le_mul_of_nonneg_right hp' (norm_nonneg _)
  · rw [if_neg h,norm_zero]
    split_ifs <;> positivity

/-- Domination after the ORIGINAL normalized orbit mean. It applies to
any locally dominated row, including arbitrary witness phases. -/
theorem source_original_edge_ORBIT_DOMINATION434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : Output → ℂ) (f : State → ℂ)
    (hf : ∀ st,‖f st‖ ≤
      ∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st,
        if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns st o k z ∧ keep st z then
          ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta o k st z‖ *
          ‖F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z)‖ else 0)
    (X : Output) :
    physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu X *
      ‖fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X‖ ≤
    ∑ Y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      sourceOriginalUnfilteredEdgePlainPair434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k X Y * ‖F Y‖ := by
  let s := sourceOriginalMemorySectorDensity434 SP sm BP bm J ell V
  let M := physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu X*s X
  let N := ∑ st : State,if physicalFockProjection SP sm BP bm (J+ell) cap st=X then
    (sourceOriginalMemoryFullDensityMass434 SP sm BP bm J ell cap Vs V mu st:ℂ)*f st else 0
  have hM : 0 ≤ M := source_original_memory_FULL_density_orbit_nonneg434
    SP sm BP bm J ell cap Vs V mu hVs hV hmu X
  have hs : 0 < s X := source_original_memory_sector_density_pos434 SP sm BP bm J ell V hV X
  have ha : fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X=N/(M:ℂ) := by
    rw [←source_original_memory_sector_density_orbit_average434 SP sm BP bm J ell cap Vs V hV mu]
    unfold sourceOriginalMemoryDensityOrbitAverage434
    simp only [Finset.sum_filter]
    congr 1
    apply Finset.sum_congr rfl
    intro st _
    by_cases hx : physicalFockProjection SP sm BP bm (J+ell) cap st=X
    · simp only [hx,ite_true,sourceOriginalMemoryFullDensityMass434]
    · simp only [hx,ite_false]
  have ht : ‖N‖ ≤ ∑ Y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      sourceOriginalMemoryOriginalFilteredDensityPair434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k X Y * ‖F Y‖ := by
    rw [source_original_memory_FILTERED_pair_target_weighted434]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro st _
    have hw := source_original_memory_FULL_density_mass_nonneg434
      SP sm BP bm J ell cap Vs V mu hVs hV hmu st
    by_cases hx : physicalFockProjection SP sm BP bm (J+ell) cap st=X
    · rw [if_pos hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw]
      simp only [hx,true_and]
      exact mul_le_mul_of_nonneg_left (hf st) hw
    · simp only [hx,false_and,ite_false,norm_zero,Finset.sum_const_zero,mul_zero,le_refl]
  have hb : M*‖fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X‖ ≤
      ∑ Y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        sourceOriginalMemoryOriginalFilteredDensityPair434 SP sm BP bm J ell m cap patterns
          keep q rho Vs V mu K zeta theta o k X Y * ‖F Y‖ := by
    rw [ha,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM]
    by_cases hz : M=0
    · rw [hz,zero_mul]
      exact (norm_nonneg N).trans ht
    · calc
        _ = ‖N‖ := by field_simp
        _ ≤ _ := ht
  apply le_of_mul_le_mul_left (a:=s X) ?_ hs
  calc
    _ = M*‖fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X‖ := by dsimp [M]; ring
    _ ≤ _ := hb
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y _
      rw [←mul_assoc,source_original_edge_PAIR_SECTOR434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEdgeEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Exact complete column budget; the damping factor remains the full SUM. -/
def sourceOriginalUnfilteredEdgeBudget434
    {SG BG Nu : Type} [Fintype SG] [Fintype BG] [Fintype Nu]
    (ell m : ℕ) (q rho R : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (Kcap : Nu → ℝ) : ℝ :=
  (∑ nu : Nu,Kcap nu)*(∏ g : SG,memorySmallRowConstant q (Vs g) ell)*
    (∏ g : BG,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
      ((max 1 (V g)⁻¹)^(ell+m)*R^(ell+m))))

theorem source_original_edge_BUDGET_NONNEG434
    {SG BG Nu : Type} [Fintype SG] [Fintype BG] [Fintype Nu]
    (ell m : ℕ) (q rho R : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (Kcap : Nu → ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr1 : rho < 1) (hR : 0 ≤ R)
    (hVs : ∀ g,0 < Vs g) (hK : ∀ nu,0 ≤ Kcap nu) :
    0 ≤ sourceOriginalUnfilteredEdgeBudget434 ell m q rho R Vs V Kcap := by
  have hsq : 0 < 1-Real.sqrt q := by
    nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
  have hd : 0 ≤ memoryPromotionDampingConstant rho (ell+m) := by
    have hh : 0 < 1-rho := sub_pos.mpr hr1
    unfold memoryPromotionDampingConstant
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  unfold sourceOriginalUnfilteredEdgeBudget434
  apply mul_nonneg
  · apply mul_nonneg (Finset.sum_nonneg (fun nu _ => hK nu))
    apply Finset.prod_nonneg
    intro g _
    have hv := hVs g
    unfold memorySmallRowConstant
    positivity
  · apply Finset.prod_nonneg
    intro g _
    positivity

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Absolute full E bound in the literal plain physical energy, with
arbitrary witness restrictions and arbitrary unit-ball witness phases.
No row, column, analytic norm or saving premise is assumed. -/
theorem source_original_edge_PHASED_FULL_ENERGY434
    (keep : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (phase : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → ℂ)
    (hphase : ∀ st z,‖phase st z‖ ≤ 1)
    (q rho R : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < rho) (hr1 : rho < 1)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (hR : 1 ≤ R) (hMass : ∀ g,∑ p : BP g,mu g p ≤ R)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
    (Rv : ℝ) (hRv : 1 ≤ Rv) (hVR : ∀ g,V g ≤ Rv) (hiR : ∀ g,(V g)⁻¹ ≤ Rv)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu,0 ≤ Kcap nu)
    (hK : ∀ nu aux s t,‖K nu aux s t‖ ≤ Kcap nu) (F : Output → ℂ) :
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
        (sourceOriginalUnfilteredEdgePhasedLocal434 SP sm BP bm J ell m cap patterns
          keep phase q rho Vs V mu K zeta theta o k F)) ≤
    (sourceOriginalUnfilteredEdgeBudget434 ell m q rho R Vs V Kcap)^2 *
      Rv^((ell+m)*Fintype.card BG)*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  let C := sourceOriginalUnfilteredEdgeBudget434 ell m q rho R Vs V Kcap
  let D := Rv^((ell+m)*Fintype.card BG)
  let S := physicalFockOrbitSupport SP sm BP bm (J+ell) cap
  let M := physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu
  let A := sourceOriginalUnfilteredEdgePlainPair434 SP sm BP bm J ell m cap patterns
    (fun _ _ => True) q rho Vs V mu K zeta theta o k
  have hC : 0 ≤ C := source_original_edge_BUDGET_NONNEG434 ell m q rho R Vs V Kcap
    hq hq1 hr1 (le_trans zero_le_one hR) hVs hK0
  have hM (X) : 0 ≤ M X := Finset.sum_nonneg
    (fun st _ => (fullPhysicalMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu st).le)
  have hA (X Y) : 0 ≤ A X Y := source_original_edge_PAIR_NONNEG434 SP sm BP bm J ell m cap
    patterns (fun _ _ => True) q rho Vs V mu hVs hmu K zeta theta o k X Y
  have hrow (X) (_ : X ∈ S) : (∑ Y ∈ S,A X Y) ≤ C*M X :=
    source_original_edge_FILTERED_PLAIN_ROW434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True) q rho R Vs V mu hq hq1 hr hr1 hVs hV hmu hR hMass hHarmonic
      K zeta theta o k Kcap hK0 hK X
  have hcol (Y) (_ : Y ∈ S) : (∑ X ∈ S,A X Y) ≤ (C*D)*M Y := by
    dsimp only [A,S]
    rw [source_original_edge_PAIR_SOURCE_SUM434]
    exact source_original_edge_FULL_PLAIN_COLUMN434 SP sm BP bm J ell m cap patterns
      q rho R Vs V mu hq hq1 hr hr1 hVs hV hmu hR hMass hHarmonic
      Rv hRv hVR hiR K zeta theta o k Kcap hK0 hK Y
  have ht (X) (_ : X ∈ S) := source_original_edge_ORBIT_DOMINATION434
    SP sm BP bm J ell m cap patterns (fun _ _ => True) q rho Vs V mu hVs hV hmu
    K zeta theta o k F
    (sourceOriginalUnfilteredEdgePhasedLocal434 SP sm BP bm J ell m cap patterns
      keep phase q rho Vs V mu K zeta theta o k F)
    (source_original_edge_PHASED_LOCAL_DOMINATION434 SP sm BP bm J ell m cap patterns
      keep (fun _ _ => True) (fun _ _ _ => trivial) phase hphase q rho Vs V mu K zeta theta o k F) X
  have he := source_original_finite_density_kernel_energy434 S M hM A hA C (C*D) hC
    hrow hcol F _ ht
  exact he.trans_eq (by dsimp only [sourceOriginalUnfilteredIdealOrbitEnergy434,C,D,S,M]; ring)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEdgeBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Fixed AFTER m and precisions; no J occurs. -/
def sourceOriginalUnfilteredEdgeExponent434
    (ell m Cq Cxi : ℕ) (q rho v C0 Rv : ℝ) : ℝ :=
  ((m:ℝ)*C0*Real.log 2+((4*Cq+2*Cxi:ℕ):ℝ)+1) +
  sourceOriginalB26SmallNormExponent434 ell (Real.sqrt q) v C0 +
  C0*Real.log (sourceOriginalMemoryBigRowBase434 rho v 2 (ell+m)) +
  (((ell+m:ℕ):ℝ)*C0*Real.log Rv)/2

theorem source_original_edge_RATIO_POLYNOMIAL434
    (L Rv C0 : ℝ) (t n : ℕ) (hL : 1 ≤ L) (hRv : 1 ≤ Rv)
    (hn : (n:ℝ) ≤ C0*Real.log L) :
    Rv^(t*n) ≤ L^((t:ℝ)*C0*Real.log Rv) := by
  have hRp : 0 < Rv := zero_lt_one.trans_le hRv
  have hLp : 0 < L := zero_lt_one.trans_le hL
  calc
    _ = Real.exp (Real.log Rv*((t:ℝ)*(n:ℝ))) := by
      rw [←Real.rpow_natCast,Real.rpow_def_of_pos hRp,Nat.cast_mul]
    _ ≤ Real.exp (Real.log Rv*((t:ℝ)*(C0*Real.log L))) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)) (Real.log_nonneg hRv))
    _ = _ := by rw [Real.rpow_def_of_pos hLp]; congr 1; ring

/-- Complete RAW-none+comparison finite polynomial budget, with arbitrary
fixed m, exact damping SUM, and an exponent independent of J. -/
theorem source_original_edge_CANONICAL_BUDGET_POLYNOMIAL434
    {SG G : Type} [Fintype SG] [Fintype G] [DecidableEq G]
    (blockA blockB : Finset G) (ell m Cq Cxi Q : ℕ)
    (q rho v C0 Rv L xi : ℝ) (Vs : SG → ℝ) (V : G → ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < rho) (hr1 : rho < 1)
    (hv : 0 < v) (hC0 : 0 ≤ C0) (hRv : 1 ≤ Rv) (hL : 2 ≤ L) (hxi : 0 < xi)
    (hVs : ∀ g,v ≤ Vs g) (hV : ∀ g,v ≤ V g)
    (hSmall : (Fintype.card SG:ℝ) ≤ C0*Real.log L)
    (hBig : (Fintype.card G:ℝ) ≤ C0*Real.log L)
    (hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤ C0*Real.log L)
    (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi) :
    (sourceOriginalUnfilteredEdgeBudget434 ell m q rho 2 Vs V
      (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi))^2 *
        Rv^((ell+m)*Fintype.card G) ≤
      L^(2*sourceOriginalUnfilteredEdgeExponent434 ell m Cq Cxi q rho v C0 Rv) := by
  let A : ℝ := (m:ℝ)*C0*Real.log 2+((4*Cq+2*Cxi:ℕ):ℝ)+1
  let B := sourceOriginalB26SmallNormExponent434 ell (Real.sqrt q) v C0
  let E := C0*Real.log (sourceOriginalMemoryBigRowBase434 rho v 2 (ell+m))
  let C := sourceOriginalUnfilteredEdgeBudget434 ell m q rho 2 Vs V
    (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi)
  have hL1 : 1 ≤ L := le_trans (by norm_num) hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hK := source_original_memory_RAW_COMPARISON_cap_budget434 blockA blockB m Q
    L C0 xi Cq Cxi hL hC0 hxi hGroups hQ hXi
  have hs := source_original_memory_SMALL_absolute_row_polynomial434 ell q v C0 L
    hq hq1 hv hC0 hL1 Vs hVs hSmall
  have hb := source_original_memory_BIG_row_factor_polynomial434 rho v 2 C0 L (ell+m)
    hr hr1 hv (by norm_num) hL1 V hV hBig
  have hs0 : 0 ≤ ∏ g : SG,memorySmallRowConstant q (Vs g) ell := by
    have hsq : 0 < 1-Real.sqrt q := by
      nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
    apply Finset.prod_nonneg
    intro g _
    have hh := hv.trans_le (hVs g)
    unfold memorySmallRowConstant
    positivity
  have hb0 : 0 ≤ ∏ g : G,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
      ((max 1 (V g)⁻¹)^(ell+m)*2^(ell+m))) := by
    have hd : 0 ≤ memoryPromotionDampingConstant rho (ell+m) := by
      have hh := sub_pos.mpr hr1
      unfold memoryPromotionDampingConstant
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    apply Finset.prod_nonneg
    intro g _
    positivity
  have hC0' : 0 ≤ C := source_original_edge_BUDGET_NONNEG434 ell m q rho 2 Vs V _
    hq hq1 hr1 (by norm_num) (fun g => hv.trans_le (hVs g))
    (source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi)
  have hC : C ≤ L^(A+B+E) := by
    have hh := mul_le_mul
      (mul_le_mul hK hs hs0 (Real.rpow_nonneg hLp.le _)) hb hb0
      (mul_nonneg (Real.rpow_nonneg hLp.le _) (Real.rpow_nonneg hLp.le _))
    apply hh.trans_eq
    rw [←Real.rpow_add hLp,←Real.rpow_add hLp]
  have hD := source_original_edge_RATIO_POLYNOMIAL434 L Rv C0 (ell+m) (Fintype.card G) hL1 hRv hBig
  calc
    _ ≤ (L^(A+B+E))^2*L^(((ell+m:ℕ):ℝ)*C0*Real.log Rv) :=
      mul_le_mul (pow_le_pow_left₀ hC0' hC 2) hD
        (pow_nonneg (zero_le_one.trans hRv) _) (sq_nonneg _)
    _ = _ := by
      rw [←Real.rpow_two,←Real.rpow_mul hLp.le,←Real.rpow_add hLp]
      congr 1
      dsimp only [sourceOriginalUnfilteredEdgeExponent434,A,B,E]
      ring

/-- The sharp enough ell=1 rarity budget, retaining the ceil and the
factor 8. J is chosen after kappa, independently of L. -/
theorem source_original_edge_DIRTY_SCALAR_BUDGET434
    (L H kappa c0 C D : ℝ) (J ns : ℕ)
    (hL : 8 ≤ L) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hPoly : C^2*D ≤ L^(2*kappa))
    (hSmall : c0*Real.log L ≤ (ns:ℝ))
    (hJ : 2*H+2*kappa+3 ≤ c0*Real.log ((J+1:ℕ):ℝ)) :
    4*C^2*D*((Nat.ceil (L^2):ℝ)/((J+1:ℕ):ℝ)^ns) ≤ L^(-(2*H)) := by
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hJ1 : (1:ℝ) ≤ ((J+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le J)
  have hJp : (0:ℝ) < ((J+1:ℕ):ℝ) := zero_lt_one.trans_le hJ1
  have hden : L^(c0*Real.log ((J+1:ℕ):ℝ)) ≤ ((J+1:ℕ):ℝ)^ns := by
    calc
      _ = Real.exp (Real.log ((J+1:ℕ):ℝ)*(c0*Real.log L)) := by
        rw [Real.rpow_def_of_pos hLp]; congr 1; ring
      _ ≤ Real.exp (Real.log ((J+1:ℕ):ℝ)*(ns:ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hSmall (Real.log_nonneg hJ1))
      _ = _ := by rw [←Real.rpow_natCast,Real.rpow_def_of_pos hJp]
  have hT : (Nat.ceil (L^2):ℝ) ≤ 2*L^2 := by
    have hh := (Nat.ceil_lt_add_one (sq_nonneg L)).le
    have hs := one_le_pow₀ (n:=2) hL1
    linarith
  have heps : (Nat.ceil (L^2):ℝ)/((J+1:ℕ):ℝ)^ns ≤
      2*L^(2-c0*Real.log ((J+1:ℕ):ℝ)) := by
    calc
      _ ≤ (2*L^2)/((J+1:ℕ):ℝ)^ns :=
        div_le_div_of_nonneg_right hT (pow_nonneg hJp.le _)
      _ ≤ (2*L^2)/L^(c0*Real.log ((J+1:ℕ):ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hLp _) hden
      _ = _ := by rw [Real.rpow_sub hLp,Real.rpow_two]; ring
  have heps0 : 0 ≤ (Nat.ceil (L^2):ℝ)/((J+1:ℕ):ℝ)^ns := by positivity
  calc
    _ = 4*(C^2*D)*((Nat.ceil (L^2):ℝ)/((J+1:ℕ):ℝ)^ns) := by ring
    _ ≤ 4*L^(2*kappa)*(2*L^(2-c0*Real.log ((J+1:ℕ):ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hPoly (by norm_num)) heps heps0
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hLp.le _))
    _ = 8*L^(2*kappa+2-c0*Real.log ((J+1:ℕ):ℝ)) := by
      rw [show 2*kappa+2-c0*Real.log ((J+1:ℕ):ℝ) =
        2*kappa+(2-c0*Real.log ((J+1:ℕ):ℝ)) by ring,Real.rpow_add hLp]
      ring
    _ ≤ 8*L^(-(2*H)-1) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hJ])) (by norm_num)
    _ ≤ L*L^(-(2*H)-1) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hLp.le _)
    _ = L^(-(2*H)) := by
      conv_lhs => lhs; rw [←Real.rpow_one L]
      rw [←Real.rpow_add hLp]
      congr 1
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEdgeLiteral -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2400000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu] (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- All literal source/target OLD gates and the numerical birth LIST
filter; the full joint orientation is in the coefficient, not in this mask. -/
def sourceOriginalUnfilteredEdgeLiteralKeep434 (T : ℕ) (o k : ℤ)
    (st : State) (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st) : Prop :=
  sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
    (physicalFockProjection SP sm BP bm (J+ell) cap st) ∧
  (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup ∧
  sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
    (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z)

/-- A literal phased extension for FULL or any witness-defined part.
Use part=True for FULL and part=not-CLEAN for DIRTY. -/
def sourceOriginalUnfilteredEdgeSeenErasedPhase434
    (part : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (phase : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → ℂ)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (T : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F : Output → ℂ) (X : Output) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
    (sourceOriginalUnfilteredEdgePhasedLocal434 SP sm BP bm J ell m cap patterns
      (fun st z => sourceOriginalUnfilteredEdgeLiteralKeep434 SP sm BP bm J ell m cap patterns
        T o k st z ∧ part st z) phase q rho Vs V mu
      (memoryOrientationK BP J ell m patterns K o) zeta theta o k F) X

theorem source_original_edge_PHASE_ONE_FULL434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (T : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F : Output → ℂ) (X : Output) :
    sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True) (fun _ _ => 1) q rho Vs V mu K T zeta theta o k F X =
    sourceOriginalUnfilteredEvolutionSeenErasedFull434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K T zeta theta o k F X := by
  unfold sourceOriginalUnfilteredEdgeSeenErasedPhase434 sourceOriginalUnfilteredEvolutionSeenErasedFull434
  apply congrArg (fun f : State → ℂ => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext st
  by_cases hs : sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
      (physicalFockProjection SP sm BP bm (J+ell) cap st)
  · simp only [hs,ite_true,sourceOriginalUnfilteredEdgePhasedLocal434,
      sourceOriginalUnfilteredEvolutionLocalFull434,sourceOrientedPhysicalChoices,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hl : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns st o k z <;>
      by_cases hn : (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup <;>
      by_cases ht : sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
        (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z) <;>
      simp [sourceOriginalUnfilteredEdgeLiteralKeep434,hs,hl,hn,ht]
  · simp [sourceOriginalUnfilteredEdgePhasedLocal434,sourceOriginalUnfilteredEdgeLiteralKeep434,hs]

theorem source_original_edge_PHASE_ONE_DIRTY434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (T : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F : Output → ℂ) (X : Output) :
    sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
      (fun st z => ¬memorySourceCleanChoice SP sm BP bm J ell m cap patterns st z)
      (fun _ _ => 1) q rho Vs V mu K T zeta theta o k F X =
    sourceOriginalUnfilteredEvolutionSeenErasedDirty434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K T zeta theta o k F X := by
  unfold sourceOriginalUnfilteredEdgeSeenErasedPhase434 sourceOriginalUnfilteredEvolutionSeenErasedDirty434
  apply congrArg (fun f : State → ℂ => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext st
  by_cases hs : sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
      (physicalFockProjection SP sm BP bm (J+ell) cap st)
  · simp only [hs,ite_true,sourceOriginalUnfilteredEdgePhasedLocal434,
      sourceOriginalUnfilteredEvolutionLocalDirty434,sourceOrientedPhysicalChoices,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hl : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns st o k z <;>
      by_cases hn : (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup <;>
      by_cases ht : sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
        (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns st o k z) <;>
      by_cases hc : memorySourceCleanChoice SP sm BP bm J ell m cap patterns st z <;>
      simp [sourceOriginalUnfilteredEdgeLiteralKeep434,hs,hl,hn,ht,hc]
  · simp [sourceOriginalUnfilteredEdgePhasedLocal434,sourceOriginalUnfilteredEdgeLiteralKeep434,hs]

/-- The existing full joint orientation obeys the same absolute cap. -/
theorem source_original_edge_ORIENTATION_CAP434
    (K : SourcePatternK BP J ell m patterns) (Kcap : Nu → ℝ)
    (hK : ∀ nu aux s t,‖K nu aux s t‖ ≤ Kcap nu) (o : ℤ) :
    ∀ nu aux s t,‖memoryOrientationK BP J ell m patterns K o nu aux s t‖ ≤ Kcap nu := by
  intro nu aux s t
  unfold memoryOrientationK
  split_ifs
  · exact hK nu aux s t
  · exact hK nu aux t s

/-- The complete literal original FULL family with both OLD gates and
numerical LIST Nodup, for arbitrary unit-ball phases on original witnesses.
The full memoryOrientationK is passed to the original coefficient. -/
theorem source_original_edge_LITERAL_PHASED_ENERGY434
    (part : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (phase : (st : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → ℂ)
    (hphase : ∀ st z,‖phase st z‖ ≤ 1)
    (q rho R : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < rho) (hr1 : rho < 1)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (hR : 1 ≤ R) (hMass : ∀ g,∑ p : BP g,mu g p ≤ R)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
    (Rv : ℝ) (hRv : 1 ≤ Rv) (hVR : ∀ g,V g ≤ Rv) (hiR : ∀ g,(V g)⁻¹ ≤ Rv)
    (K : SourcePatternK BP J ell m patterns) (T : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu,0 ≤ Kcap nu)
    (hK : ∀ nu aux s t,‖K nu aux s t‖ ≤ Kcap nu) (F : Output → ℂ) :
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
        part phase q rho Vs V mu K T zeta theta o k F) ≤
    (sourceOriginalUnfilteredEdgeBudget434 ell m q rho R Vs V Kcap)^2 *
      Rv^((ell+m)*Fintype.card BG)*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  exact source_original_edge_PHASED_FULL_ENERGY434 SP sm BP bm J ell m cap patterns
    _ phase hphase q rho R Vs V mu hq hq1 hr hr1 hVs hV hmu hR hMass hHarmonic
    Rv hRv hVR hiR (memoryOrientationK BP J ell m patterns K o) zeta theta o k
    Kcap hK0 (source_original_edge_ORIENTATION_CAP434 BP J ell m patterns K Kcap hK o) F
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootActualPhase -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Phase-universal finite expansion of the actual G row, with a newly
sampled representative and its original conditional weight at this visit.
The phase is inside the row; it is not a quotient-state multiplier. -/
theorem source_original_root_ACTUAL_G_PHASE_FLAT434
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (phase : (x : State) → FullGhostWitness SP sm BP bm (J+ell) cap x → ℂ)
    (F : Output → ℂ) (X : Output) :
    sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap
      q rho N i Vs V mu phase F X =
    ∑ z : SourceOriginalForestGIndex434 SP sm BP bm J ell cap,
      sourceOriginalForestGFlatCoefficient434 SP sm BP bm J ell cap
        q rho N i Vs V mu X z *
      phase z.1 z.2.2 *
      F (physicalFockProjection SP sm BP bm (J+ell) cap z.2.1) := by
  unfold sourceOriginalUnfilteredEvolutionSeenErasedG434
  rw [source_original_forest_ORBIT_FLAT434]
  conv_rhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  dsimp only [sourceOriginalForestGFlatCoefficient434]
  by_cases hb : (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup
  · simp only [if_pos hb]
    ring
  · simp only [if_neg hb,mul_zero,zero_mul]

/-- Both actual OLD boundaries are included as witness masks. The listed
flat coefficient takes the already-oriented K; the phased operator takes
the original K and orients it internally, exactly once. -/
def sourceOriginalRootEGuardedCoefficient434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (T : ℕ) (zeta theta : ℝ) (o k : ℤ) (X : Output)
    (z : SourceOriginalForestEIndex434 SP sm BP bm J ell m cap patterns) : ℂ :=
  if sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
      (physicalFockProjection SP sm BP bm (J+ell) cap z.1) ∧
    sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
      (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns z.1 o k z.2) then
    sourceOriginalForestEFlatCoefficient434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu (memoryOrientationK BP J ell m patterns K o) zeta theta o k X z
  else 0

/-- Phase-universal finite expansion of the literal full E operator. Both
OLD gates, full joint K, local numerical ND and zero-mass orbit semantics
remain unchanged. No phase-invariance premise is used. -/
theorem source_original_root_ACTUAL_E_PHASE_FLAT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (T : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (phase : (x : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → ℂ)
    (F : Output → ℂ) (X : Output) :
    sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True) phase q rho Vs V mu K T zeta theta o k F X =
    ∑ z : SourceOriginalForestEIndex434 SP sm BP bm J ell m cap patterns,
      sourceOriginalRootEGuardedCoefficient434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K T zeta theta o k X z *
      phase z.1 z.2 *
      F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns z.1 o k z.2) := by
  unfold sourceOriginalUnfilteredEdgeSeenErasedPhase434
  rw [source_original_forest_ORBIT_FLAT434]
  conv_rhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x hx
  unfold sourceOriginalUnfilteredEdgePhasedLocal434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  dsimp only [sourceOriginalRootEGuardedCoefficient434, sourceOriginalForestEFlatCoefficient434]
  by_cases hi : sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
      (physicalFockProjection SP sm BP bm (J+ell) cap x) <;>
    by_cases ht : sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
      (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z) <;>
    by_cases hl : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z <;>
    by_cases hn : (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup <;>
    simp [sourceOriginalUnfilteredEdgeLiteralKeep434,hi,ht,hl,hn] <;> ring

/-- Initial local ND is an exact extra mask of the original listed chain,
even for initial ordered active arrays with repetitions. -/
theorem source_original_root_LISTED_INITIAL_MASK434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T n start : ℕ) (F : Output → ℂ) (Y : Output) (H : List ℕ) :
    sourceOriginalForestListedGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F Y H =
    if H.Nodup then
      sourceOriginalForestListedGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n start F Y H
    else 0 := by
  by_cases hH : H.Nodup
  · simp only [if_pos hH]
  · rw [if_neg hH, source_original_forest_LISTED_CHAIN_EXACT434, if_neg hH]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootActualLabels -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Potential E address is the CANONICAL slot before tau, with its actual
numeric label read after tau. Selected address sets therefore remain fixed
outside every original endpoint permutation sum. -/
def sourceOriginalRootELabel434
    (x : State) (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (g : BG) (i : Fin (J+ell)) : Option ℕ :=
  if i ∈ orientedFresh (J+ell) (sourceBigShared J ell m (patterns z.1) g)
      ((z.2.2.1.bigChoice g).2.2.1) then
    some (bm g ((z.2.2.1.bigChoice g).1 (z.2.2.1.tauBig g i)))
  else none

theorem source_original_root_E_LABEL_PIN_EXACT434
    (x : State) (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (Q : BG → Finset (Fin (J+ell))) (pin : BG → Fin (J+ell) → ℕ) :
    (∀ g,∀ i ∈ Q g, sourceOriginalRootELabel434 SP sm BP bm J ell m cap patterns
      x z g i = some (pin g i)) ↔
    sourceOriginalForestBigFramePins434 BP bm (J+ell) cap x.2
      (sourceBigShared J ell m (patterns z.1)) Q z.2.2.1.tauBig pin z.2.2.1.bigChoice := by
  constructor
  · intro h g
    constructor
    · intro i hi
      have hh := h g i hi
      by_contra hn
      simp [sourceOriginalRootELabel434,hn] at hh
    · intro i hi
      have hh := h g i hi
      by_cases hn : i ∈ orientedFresh (J+ell)
          (sourceBigShared J ell m (patterns z.1) g) ((z.2.2.1.bigChoice g).2.2.1)
      · simpa [sourceOriginalRootELabel434,hn] using hh
      · simp [sourceOriginalRootELabel434,hn] at hh
  · intro h g i hi
    simp [sourceOriginalRootELabel434,(h g).1 hi,(h g).2 i hi]

/-- Actual ordered fresh position. The finite padded address uses only
j<T; outside the performed fresh length the value is inactive. -/
def sourceOriginalRootGLabel434
    (x : State) (z : FullGhostWitness SP sm BP bm (J+ell) cap x)
    (g : BG) (j : ℕ) : Option ℕ :=
  if h : j < (z g).2.1.val then some (bm g ((z g).2.2 ⟨j,h⟩).1) else none

theorem source_original_root_G_LABEL_PIN_EXACT434
    (x : State) (z : FullGhostWitness SP sm BP bm (J+ell) cap x)
    (Q : BG → Finset ℕ) (pin : BG → ℕ → ℕ) :
    (∀ g,∀ j ∈ Q g,sourceOriginalRootGLabel434 SP sm BP bm J ell cap x z g j =
      some (pin g j)) ↔
    (∀ g,Q g ⊆ Finset.range (z g).2.1.val ∧
      (∀ j : Fin (z g).2.1.val,j.val ∈ Q g → bm g ((z g).2.2 j).1=pin g j.val)) := by
  constructor
  · intro h g
    constructor
    · intro j hj
      have hh := h g j hj
      by_contra hn
      have hn' : ¬j < (z g).2.1.val := by simpa only [Finset.mem_range] using hn
      simp [sourceOriginalRootGLabel434,hn'] at hh
    · intro j hj
      have hh := h g j.val hj
      simpa [sourceOriginalRootGLabel434,j.isLt] using hh
  · intro h g j hj
    have hj' : j < (z g).2.1.val := Finset.mem_range.mp ((h g).1 hj)
    simpa [sourceOriginalRootGLabel434,hj'] using (h g).2 ⟨j,hj'⟩ hj

/-- Private-sentinel equality at different addresses is exactly equality
of two performed numeric labels. An arbitrary option register cannot store
a foreign sentinel. -/
theorem source_original_root_DECODE_EQUALITY434
    {Addr Num : Type} [DecidableEq Addr] (a b : Addr) (hab : a ≠ b)
    (x y : Option Num) :
    (x.elim (Sum.inr a) Sum.inl : Num ⊕ Addr) =
      y.elim (Sum.inr b) Sum.inl ↔
    ∃ p : Num,x=some p ∧ y=some p := by
  cases x <;> cases y <;> simp [hab,eq_comm]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootPaddingLists -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

def sourceOriginalRootPadPrefix434 {A : Type} (T b : ℕ) (f : Fin b → A) : List (Option A) :=
  List.ofFn (fun i : Fin T => if h : i.val<b then some (f ⟨i.val,h⟩) else none)

/-- Width-T padding deletes exactly the inactive suffix, even when the
performed numeric tuple has repetitions. -/
theorem source_original_root_PAD_PREFIX_FILTER434
    {A : Type} (T b : ℕ) (hb : b≤T) (f : Fin b → A) :
    (sourceOriginalRootPadPrefix434 T b f).filterMap id=List.ofFn f := by
  induction T generalizing b with
  | zero =>
    have hb0 : b=0 := by omega
    subst b
    simp [sourceOriginalRootPadPrefix434]
  | succ T ih =>
    cases b with
    | zero => simp [sourceOriginalRootPadPrefix434]
    | succ b =>
      unfold sourceOriginalRootPadPrefix434
      rw [List.ofFn_succ,List.ofFn_succ]
      change List.filterMap id (some (f 0) :: List.ofFn
        (fun i : Fin T => if h : i.succ.val < b+1 then some (f ⟨i.succ.val,h⟩) else none)) =
        f 0 :: List.ofFn (fun i : Fin b => f i.succ)
      simp only [List.filterMap_cons,id_eq]
      congr 1
      have he :
          (fun i : Fin T => if h : i.succ.val < b+1 then some (f ⟨i.succ.val,h⟩) else none) =
          (fun i : Fin T => if h : i.val < b then some (f (⟨i.val,h⟩ : Fin b).succ) else none) := by
        funext i
        by_cases hi : i.val<b
        · simp [hi,Fin.val_succ,Nat.succ_lt_succ_iff]
        · simp [hi,Fin.val_succ,Nat.succ_lt_succ_iff]
      rw [he]
      exact ih b (by omega) (fun i => f i.succ)

theorem source_original_root_FILTERMAP_FLATMAP434
    {A B C : Type} (l : List A) (f : A → List B) (g : B → Option C) :
    (l.flatMap f).filterMap g=l.flatMap (fun a => (f a).filterMap g) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem source_original_root_FILTERMAP_MASK434
    {A B : Type} (l : List A) (p : A → Prop) [DecidablePred p] (f : A → B) :
    (l.map (fun a => if p a then some (f a) else none)).filterMap id =
      (l.filter (fun a => decide (p a))).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : p a
    · simpa [ha] using congrArg (List.cons (f a)) ih
    · simpa [ha] using ih

/-- Filtering a fixed full potential-slot enumeration recovers the actual
finite selected-slot enumeration up to permutation, with multiplicities
preserved after applying a possibly noninjective numeric readout. -/
theorem source_original_root_PAD_FINSET_FILTER_PERM434
    {A B : Type} [Fintype A] [DecidableEq A] (s : Finset A) (f : A → B) :
    (((Finset.univ : Finset A).toList.map
      (fun a => if a∈s then some (f a) else none)).filterMap id).Perm (s.toList.map f) := by
  rw [source_original_root_FILTERMAP_MASK434]
  have hp : (((Finset.univ : Finset A).toList.filter (fun a => decide (a∈s)))).Perm s.toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact (Finset.nodup_toList _).filter _
    · exact Finset.nodup_toList _
    · ext a
      simp
  exact hp.map f
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootActualPadding -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

def sourceOriginalRootGPad434 (T : ℕ) (x : State)
    (z : FullGhostWitness SP sm BP bm (J+ell) cap x) : List (Option ℕ) :=
  (Finset.univ : Finset BG).toList.flatMap (fun g =>
    sourceOriginalRootPadPrefix434 T (z g).2.1.val (fun j => bm g ((z g).2.2 j).1))

def sourceOriginalRootEPad434 (x : State)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) : List (Option ℕ) :=
  (Finset.univ : Finset BG).toList.flatMap (fun g =>
    (Finset.univ : Finset (Fin (J+ell))).toList.map
      (sourceOriginalRootELabel434 SP sm BP bm J ell m cap patterns x z g))

theorem source_original_root_G_PAD_LENGTH434 (T : ℕ) (x : State)
    (z : FullGhostWitness SP sm BP bm (J+ell) cap x) :
    (sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z).length =
      Fintype.card BG*T := by
  simp [sourceOriginalRootGPad434,sourceOriginalRootPadPrefix434,List.length_flatMap,
    Nat.mul_comm]

theorem source_original_root_E_PAD_LENGTH434 (x : State)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    (sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z).length =
      Fintype.card BG*(J+ell) := by
  simp [sourceOriginalRootEPad434,List.length_flatMap,Nat.mul_comm]

/-- G padding recovers the TRUE ordered numerical birth list exactly.
Only the already justified b<=T support condition is used. -/
theorem source_original_root_G_PAD_BIRTHS434 (T : ℕ) (x : State)
    (z : FullGhostWitness SP sm BP bm (J+ell) cap x) (hz : ∀ g,(z g).2.1.val≤T) :
    (sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z).filterMap id =
      physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z := by
  unfold sourceOriginalRootGPad434 physicalGhostFreshBirths
  rw [source_original_root_FILTERMAP_FLATMAP434]
  apply congrArg (fun f : BG → List ℕ => (Finset.univ : Finset BG).toList.flatMap f)
  funext g
  rw [source_original_root_PAD_PREFIX_FILTER434 T _ (hz g)]
  simp only [List.map_ofFn,Function.comp_def]

/-- The fixed potential E slots recover its ACTUAL fresh list after tau,
up to harmless enumeration permutation. No numeric injectivity is used. -/
theorem source_original_root_E_PAD_BIRTHS434 (x : State)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    ((sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z).filterMap id).Perm
      (orientedEFreshBirths SP sm BP bm J ell m cap patterns z) := by
  unfold sourceOriginalRootEPad434 orientedEFreshBirths
  rw [source_original_root_FILTERMAP_FLATMAP434]
  apply List.Perm.flatMap (List.Perm.refl _)
  intro g hg
  exact source_original_root_PAD_FINSET_FILTER_PERM434
    (orientedFresh (J+ell) (sourceBigShared J ell m (patterns z.1) g)
      (z.2.2.1.bigChoice g).2.2.1)
    (fun i => bm g ((z.2.2.1.bigChoice g).1 (z.2.2.1.tauBig g i)))

/-- The already-identified original listed suffix is insensitive to a
permutation of its prior numeric list. This does not alter its measure. -/
theorem source_original_root_LISTED_CHAIN_PERM434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T n start : ℕ) (F : Output → ℂ) (Y : Output) (H H' : List ℕ)
    (h : H.Perm H') :
    sourceOriginalForestListedGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F Y H =
    sourceOriginalForestListedGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F Y H' := by
  rw [source_original_forest_LISTED_CHAIN_EXACT434,source_original_forest_LISTED_CHAIN_EXACT434]
  have he : H.toFinset=H'.toFinset := by
    ext a
    simp only [List.mem_toFinset]
    exact h.mem_iff
  by_cases hn : H.Nodup
  · rw [if_pos hn,if_pos (h.nodup_iff.mp hn),he]
  · rw [if_neg hn,if_neg (fun hh => hn (h.nodup_iff.mpr hh))]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootGhostPadSublist -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE List
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Even an oversized G draw has a padded readout which is a sublist of
its actual births. This is a readout statement, never a signed truncation. -/
theorem source_original_root_PAD_PREFIX_SUBLIST434
    {A : Type} (T b : ℕ) (f : Fin b → A) :
    (sourceOriginalRootPadPrefix434 T b f).filterMap id <+ List.ofFn f := by
  induction T generalizing b with
  | zero => simp [sourceOriginalRootPadPrefix434]
  | succ T ih =>
    cases b with
    | zero => simp [sourceOriginalRootPadPrefix434]
    | succ b =>
      unfold sourceOriginalRootPadPrefix434
      rw [List.ofFn_succ,List.ofFn_succ]
      change List.filterMap id (some (f 0) :: List.ofFn
        (fun i : Fin T => if h : i.succ.val < b+1 then some (f ⟨i.succ.val,h⟩) else none)) <+
        f 0 :: List.ofFn (fun i : Fin b => f i.succ)
      simp only [List.filterMap_cons,id_eq]
      apply List.Sublist.cons_cons
      have he :
          (fun i : Fin T => if h : i.succ.val < b+1 then some (f ⟨i.succ.val,h⟩) else none) =
          (fun i : Fin T => if h : i.val < b then some (f (⟨i.val,h⟩ : Fin b).succ) else none) := by
        funext i
        by_cases hi : i.val < b
        · simp [hi,Fin.val_succ,Nat.succ_lt_succ_iff]
        · simp [hi,Fin.val_succ,Nat.succ_lt_succ_iff]
      rw [he]
      exact ih b (fun i => f i.succ)

theorem source_original_root_FLATMAP_POINTWISE_SUBLIST434
    {A B : Type} (l : List A) (f g : A → List B) (h : ∀ a,f a <+ g a) :
    l.flatMap f <+ l.flatMap g := by
  induction l with
  | nil => exact List.Sublist.refl []
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact (h a).append ih

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap

theorem source_original_root_G_PAD_SUBLIST434 (T : ℕ) (x : State)
    (z : FullGhostWitness SP sm BP bm (J+ell) cap x) :
    (sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z).filterMap id <+
      physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z := by
  unfold sourceOriginalRootGPad434 physicalGhostFreshBirths
  rw [source_original_root_FILTERMAP_FLATMAP434]
  apply source_original_root_FLATMAP_POINTWISE_SUBLIST434
  intro g
  simpa only [List.map_ofFn,Function.comp_def] using
    source_original_root_PAD_PREFIX_SUBLIST434 T (z g).2.1.val
      (fun j => bm g ((z g).2.2 j).1)

theorem source_original_root_G_PAD_NODUP434 (T : ℕ) (x : State)
    (z : FullGhostWitness SP sm BP bm (J+ell) cap x)
    (h : (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup) :
    ((sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z).filterMap id).Nodup :=
  h.sublist (source_original_root_G_PAD_SUBLIST434 SP sm BP bm J ell cap T x z)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootListPhase -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

def sourceOriginalRootListPhase434 {A : Type} (phi : ℕ → A → ℂ) :
    ℕ → List A → ℂ
  | _,[] => 1
  | o,a::l => phi o a * sourceOriginalRootListPhase434 phi (o+1) l

theorem source_original_root_LIST_PHASE_APPEND434
    {A : Type} (phi : ℕ → A → ℂ) (o : ℕ) (H B : List A) :
    sourceOriginalRootListPhase434 phi o (H++B) =
      sourceOriginalRootListPhase434 phi o H *
        sourceOriginalRootListPhase434 phi (o+H.length) B := by
  induction H generalizing o with
  | nil => simp [sourceOriginalRootListPhase434]
  | cons a H ih =>
    simp only [List.cons_append,sourceOriginalRootListPhase434,List.length_cons,ih]
    simp only [mul_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem source_original_root_LIST_PHASE_UNIT434
    {A : Type} (phi : ℕ → A → ℂ) (hphi : ∀ i a,‖phi i a‖=1)
    (o : ℕ) (H : List A) :
    ‖sourceOriginalRootListPhase434 phi o H‖=1 := by
  induction H generalizing o with
  | nil => simp [sourceOriginalRootListPhase434]
  | cons a H ih => simp only [sourceOriginalRootListPhase434,norm_mul,hphi,ih,one_mul]

theorem source_original_root_LIST_PHASE_ONE434
    {A : Type} (o : ℕ) (H : List A) :
    sourceOriginalRootListPhase434 (fun _ (_ : A) => 1) o H=1 := by
  induction H generalizing o with
  | nil => rfl
  | cons a H ih => simp [sourceOriginalRootListPhase434,ih]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootPaddedDistinct -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Deleting inactive slots retains precisely numerical distinctness.
The values at performed slots need not be injective a priori. -/
theorem source_original_root_FILTER_OF_FN_NODUP434
    {A : Type} {n : ℕ} (v : Fin n → Option A) :
    ((List.ofFn v).filterMap id).Nodup ↔
      ∀ i j p,v i=some p → v j=some p → i=j := by
  change ((List.ofFn v).filterMap id).Pairwise (fun a b => a≠b) ↔ _
  rw [List.pairwise_filterMap,List.pairwise_ofFn]
  simp only [id_eq,Option.mem_def]
  constructor
  · intro h i j p hi hj
    rcases lt_trichotomy i j with hij|hij|hij
    · exact False.elim (h hij p hi p hj rfl)
    · exact hij
    · exact False.elim (h hij p hj p hi rfl)
  · intro h i j hij p hp q hq hpq
    subst q
    exact (ne_of_lt hij) (h i j p hp hq)

theorem source_original_root_PADDED_LIST_NODUP434
    {A : Type} {n : ℕ} (v : Fin n → Option A) :
    ((List.ofFn v).filterMap id).Nodup ↔
      Function.Injective (fun i : Fin n => (v i).elim (Sum.inr i) Sum.inl : Fin n → A ⊕ Fin n) := by
  rw [source_original_root_FILTER_OF_FN_NODUP434,source_original_root_PADDED_INJECTIVE434]

def sourceOriginalRootPaddedLabel434 {A : Type} {n : ℕ}
    (v : Fin n → Option A) (j : ℕ) : A ⊕ ℕ :=
  if h : j<n then (v ⟨j,h⟩).elim (Sum.inr j) Sum.inl else Sum.inr j

theorem source_original_root_PADDED_PREFIX434
    {A : Type} {n : ℕ} (v : Fin n → Option A) :
    ((List.ofFn v).filterMap id).Nodup ↔
      sourceOriginalRootPrefixDistinct434 n (sourceOriginalRootPaddedLabel434 v) := by
  rw [source_original_root_FILTER_OF_FN_NODUP434]
  constructor
  · intro h i hi j hj he
    simp only [sourceOriginalRootPaddedLabel434,dif_pos hi,dif_pos hj] at he
    cases hvi : v ⟨i,hi⟩ with
    | none =>
      cases hvj : v ⟨j,hj⟩ with
      | none => simpa [hvi,hvj] using he
      | some q => simp [hvi,hvj] at he
    | some p =>
      cases hvj : v ⟨j,hj⟩ with
      | none => simp [hvi,hvj] at he
      | some q =>
        have hpq : p=q := by simpa [hvi,hvj] using he
        subst q
        exact congrArg Fin.val (h ⟨i,hi⟩ ⟨j,hj⟩ p hvi hvj)
  · intro h i j p hi hj
    apply Fin.ext
    apply h i.val i.isLt j.val j.isLt
    simp [sourceOriginalRootPaddedLabel434,i.isLt,j.isLt,hi,hj]

/-- Exact increasing-forest expansion for Option-valued potential
addresses, with a private sentinel at every inactive address. -/
theorem source_original_root_PADDED_FOREST_EXPANSION434
    {A : Type} {n : ℕ} (v : Fin n → Option A) :
    (if ((List.ofFn v).filterMap id).Nodup then (1:ℂ) else 0) =
      ∑ p : SourceOriginalRootForest434 n,
        (-1:ℂ)^(sourceOriginalRootForestRank434 p) *
        sourceOriginalRootForestEquality434 p (sourceOriginalRootPaddedLabel434 v) := by
  simp only [source_original_root_PADDED_PREFIX434]
  exact source_original_root_FOREST_EXPANSION434 n (sourceOriginalRootPaddedLabel434 v)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootListForest -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

def sourceOriginalRootListLabel434 (H : List (Option ℕ)) (j : ℕ) : ℕ ⊕ ℕ :=
  (H.getD j none).elim (Sum.inr j) Sum.inl

def sourceOriginalRootListForestTerm434 {A : ℕ}
    (p : SourceOriginalRootForest434 A) (H : List (Option ℕ)) : ℂ :=
  (-1:ℂ)^(sourceOriginalRootForestRank434 p) *
    sourceOriginalRootForestEquality434 p (sourceOriginalRootListLabel434 H)

/-- The exact forest expansion at a prescribed potential length.
Natural numeric equality and private sentinels keep their original meaning. -/
theorem source_original_root_LIST_FOREST_EXPANSION434
    (A : ℕ) (H : List (Option ℕ)) (hH : H.length=A) :
    (if (H.filterMap id).Nodup then (1:ℂ) else 0) =
      ∑ p : SourceOriginalRootForest434 A,sourceOriginalRootListForestTerm434 p H := by
  subst A
  let v : Fin H.length → Option ℕ := fun i => H.getD i.val none
  have hv : List.ofFn v=H := by
    have he : v=H.get := by
      funext i
      exact List.getD_eq_getElem H none i.isLt
    rw [he,List.ofFn_get]
  have hh := source_original_root_PADDED_FOREST_EXPANSION434 v
  rw [hv] at hh
  calc
    _ = ∑ p : SourceOriginalRootForest434 H.length,
        (-1:ℂ)^sourceOriginalRootForestRank434 p *
          sourceOriginalRootForestEquality434 p (sourceOriginalRootPaddedLabel434 v) := by
      by_cases hd : (H.filterMap id).Nodup <;>
        simpa only [hd,ite_true,ite_false] using hh
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold sourceOriginalRootListForestTerm434
      congr 1
      unfold sourceOriginalRootForestEquality434
      apply Finset.prod_congr rfl
      intro i hi
      cases he : p i with
      | none => simp [he]
      | some j =>
        simp only [he,Option.elim]
        have hj : j.val<H.length := lt_trans j.isLt i.isLt
        simp [sourceOriginalRootPaddedLabel434,sourceOriginalRootListLabel434,v,i.isLt,hj]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootFiniteAlphabet -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

def sourceOriginalRootAlphabetEncode434 (S : Finset ℕ) {A : ℕ}
    (a : Fin A) : Option ℕ → S ⊕ Fin A
  | none => Sum.inr a
  | some p => if hp : p∈S then Sum.inl ⟨p,hp⟩ else Sum.inr a

theorem source_original_root_ALPHABET_EQUALITY434
    (S : Finset ℕ) {A : ℕ} (a b : Fin A) (x y : Option ℕ)
    (hx : ∀ p,x=some p → p∈S) (hy : ∀ p,y=some p → p∈S) :
    sourceOriginalRootAlphabetEncode434 S a x=sourceOriginalRootAlphabetEncode434 S b y ↔
      (x.elim (Sum.inr a.val) Sum.inl : ℕ ⊕ ℕ)=y.elim (Sum.inr b.val) Sum.inl := by
  cases x with
  | none =>
    cases y with
    | none => simp [sourceOriginalRootAlphabetEncode434,Fin.ext_iff]
    | some q => simp [sourceOriginalRootAlphabetEncode434,hy q rfl]
  | some p =>
    cases y with
    | none => simp [sourceOriginalRootAlphabetEncode434,hx p rfl]
    | some q => simp [sourceOriginalRootAlphabetEncode434,hx p rfl,hy q rfl]

variable {E : Type} [Fintype E]

/-- Total extension to every numeric value and every natural address.
Only actual finite-alphabet values are needed for the equality identity;
unit modulus holds even outside them. -/
def sourceOriginalRootNumericSlotPhase434
    (S : Finset ℕ) {A : ℕ} (left right : E → Fin A)
    (h : E → (S ⊕ Fin A) → Bool) (j : ℕ) (v : Option ℕ) : ℂ :=
  if hj : j<A then
    sourceOriginalRootCenteredSlot434 left right Sum.inr h ⟨j,hj⟩
      (sourceOriginalRootAlphabetEncode434 S ⟨j,hj⟩ v) else 1

theorem source_original_root_NUMERIC_SLOT_UNIT434
    (S : Finset ℕ) {A : ℕ} (left right : E → Fin A)
    (h : E → (S ⊕ Fin A) → Bool) (j : ℕ) (v : Option ℕ) :
    ‖sourceOriginalRootNumericSlotPhase434 S left right h j v‖=1 := by
  unfold sourceOriginalRootNumericSlotPhase434
  split_ifs <;> simp [source_original_root_CENTERED_SLOT_UNIT434]

theorem source_original_root_NUMERIC_SLOT_INACTIVE434
    (S : Finset ℕ) {A : ℕ} (left right : E → Fin A)
    (h : E → (S ⊕ Fin A) → Bool) (j : ℕ) :
    sourceOriginalRootNumericSlotPhase434 S left right h j none=1 := by
  unfold sourceOriginalRootNumericSlotPhase434
  split_ifs <;> simp [sourceOriginalRootAlphabetEncode434,
    source_original_root_CENTERED_SLOT_INACTIVE434]

theorem source_original_root_LIST_PHASE_OF_FN434
    {B : Type} {n : ℕ} (phi : ℕ → B → ℂ) (o : ℕ) (v : Fin n → B) :
    sourceOriginalRootListPhase434 phi o (List.ofFn v) =
      ∏ i : Fin n,phi (o+i.val) (v i) := by
  induction n generalizing o with
  | zero => simp [sourceOriginalRootListPhase434]
  | succ n ih =>
    rw [List.ofFn_succ,sourceOriginalRootListPhase434,Fin.prod_univ_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem source_original_root_NUMERIC_SLOT_PRODUCT434
    (S : Finset ℕ) {A : ℕ} (left right : E → Fin A)
    (h : E → (S ⊕ Fin A) → Bool) (H : List (Option ℕ)) (hH : H.length=A) :
    sourceOriginalRootListPhase434 (sourceOriginalRootNumericSlotPhase434 S left right h) 0 H =
      ∏ a : Fin A,sourceOriginalRootCenteredSlot434 left right Sum.inr h a
        (sourceOriginalRootAlphabetEncode434 S a (H.getD a.val none)) := by
  subst A
  have he : List.ofFn (fun a : Fin H.length => H.getD a.val none)=H := by
    have hf : (fun a : Fin H.length => H.getD a.val none)=H.get := by
      funext a
      exact List.getD_eq_getElem H none a.isLt
    rw [hf,List.ofFn_get]
  have hh := source_original_root_LIST_PHASE_OF_FN434
    (sourceOriginalRootNumericSlotPhase434 S left right h) 0
    (fun a : Fin H.length => H.getD a.val none)
  rw [he] at hh
  apply hh.trans
  apply Finset.prod_congr rfl
  intro a ha
  simp only [Nat.zero_add,sourceOriginalRootNumericSlotPhase434,dif_pos a.isLt]

/-- Independent-edge equality on the actual numerical labels, represented
by finite random fields and unit phases extended to all source witnesses. -/
theorem source_original_root_NUMERIC_EDGE_AVERAGE434
    (S : Finset ℕ) {A : ℕ} (left right : E → Fin A)
    (H : List (Option ℕ)) (hH : H.length=A)
    (hvalid : ∀ a : Fin A,∀ p,H.getD a.val none=some p → p∈S) :
    (∑ h : E → (S ⊕ Fin A) → Bool,
      (∏ e : E,sourceOriginalRootSign434 (h e (Sum.inr (left e))) *
        sourceOriginalRootSign434 (h e (Sum.inr (right e)))) *
      sourceOriginalRootListPhase434 (sourceOriginalRootNumericSlotPhase434 S left right h) 0 H) /
      (Fintype.card (E → (S ⊕ Fin A) → Bool):ℂ) =
      ∏ e : E,if sourceOriginalRootListLabel434 H (left e).val =
        sourceOriginalRootListLabel434 H (right e).val then (1:ℂ) else 0 := by
  simp_rw [source_original_root_NUMERIC_SLOT_PRODUCT434 S left right _ H hH]
  rw [source_original_root_CENTERED_SLOT_AVERAGE434]
  apply Finset.prod_congr rfl
  intro e he
  have hh := source_original_root_ALPHABET_EQUALITY434 S (left e) (right e)
    (H.getD (left e).val none) (H.getD (right e).val none)
    (hvalid (left e)) (hvalid (right e))
  exact if_congr hh rfl rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootForestOnline -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

def sourceOriginalRootForestEdge434 {A : ℕ} (p : SourceOriginalRootForest434 A)
    (H : List (Option ℕ)) (i : Fin A) : ℂ :=
  (p i).elim 1 (fun j =>
    if sourceOriginalRootListLabel434 H i.val=sourceOriginalRootListLabel434 H j.val then 1 else 0)

def sourceOriginalRootForestPrefix434 {A : ℕ} (p : SourceOriginalRootForest434 A)
    (H : List (Option ℕ)) : ℂ :=
  ∏ i : Fin A,if i.val < H.length then sourceOriginalRootForestEdge434 p H i else 1

def sourceOriginalRootForestBatch434 {A : ℕ} (p : SourceOriginalRootForest434 A)
    (offset : ℕ) (H : List (Option ℕ)) : ℂ :=
  ∏ i : Fin A,if offset ≤ i.val ∧ i.val < H.length then sourceOriginalRootForestEdge434 p H i else 1

theorem source_original_root_FOREST_EDGE_APPEND434 {A : ℕ}
    (p : SourceOriginalRootForest434 A) (H B : List (Option ℕ))
    (i : Fin A) (hi : i.val < H.length) :
    sourceOriginalRootForestEdge434 p (H++B) i=sourceOriginalRootForestEdge434 p H i := by
  unfold sourceOriginalRootForestEdge434
  cases hp : p i with
  | none => rfl
  | some j =>
    have hj : j.val < H.length := j.isLt.trans hi
    simp only [Option.elim,sourceOriginalRootListLabel434,
      List.getD_append H B none i.val hi,List.getD_append H B none j.val hj]
    exact congrArg (fun d : Decidable (sourceOriginalRootListLabel434 H i.val=
      sourceOriginalRootListLabel434 H j.val) => @ite ℂ _ d 1 0) (Subsingleton.elim _ _)

/-- Terminal forest constraints move to exactly their child's batch.
This identity has no injectivity or positivity premise. -/
theorem source_original_root_FOREST_PREFIX_WRITE434 {A : ℕ}
    (p : SourceOriginalRootForest434 A) (H B : List (Option ℕ)) :
    sourceOriginalRootForestPrefix434 p (H++B)=
      sourceOriginalRootForestPrefix434 p H*
        sourceOriginalRootForestBatch434 p H.length (H++B) := by
  unfold sourceOriginalRootForestPrefix434 sourceOriginalRootForestBatch434
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hOld : i.val < H.length
  · have hNew : i.val < (H++B).length := by simp only [List.length_append]; omega
    have hn : ¬(H.length ≤ i.val ∧ i.val < (H++B).length) := by omega
    rw [if_pos hNew,if_pos hOld,if_neg hn,mul_one,
      source_original_root_FOREST_EDGE_APPEND434 p H B i hOld]
  · by_cases hNew : i.val < (H++B).length
    · have hb : H.length ≤ i.val ∧ i.val < (H++B).length := by omega
      rw [if_pos hNew,if_neg hOld,if_pos hb,one_mul]
    · have hb : ¬(H.length ≤ i.val ∧ i.val < (H++B).length) := by omega
      rw [if_neg hNew,if_neg hOld,if_neg hb,one_mul]

theorem source_original_root_FOREST_PREFIX_FULL434 {A : ℕ}
    (p : SourceOriginalRootForest434 A) (H : List (Option ℕ)) (hH : A ≤ H.length) :
    sourceOriginalRootForestPrefix434 p H=
      sourceOriginalRootForestEquality434 p (sourceOriginalRootListLabel434 H) := by
  unfold sourceOriginalRootForestPrefix434 sourceOriginalRootForestEquality434
  apply Finset.prod_congr rfl
  intro i hi
  rw [if_pos (i.isLt.trans_le hH)]
  unfold sourceOriginalRootForestEdge434
  cases hp : p i <;> simp only [Option.elim]
  split_ifs <;> rfl

/-- Inactive parents yield zero; there is no conditional normalization. -/
theorem source_original_root_FOREST_EDGE_PARENT_NONE434 {A : ℕ}
    (p : SourceOriginalRootForest434 A) (H : List (Option ℕ))
    (i : Fin A) (j : Fin i.val) (hp : p i=some j) (hj : H.getD j.val none=none) :
    sourceOriginalRootForestEdge434 p H i=0 := by
  have hij : i.val ≠ j.val := ne_of_gt j.isLt
  have he : sourceOriginalRootListLabel434 H i.val ≠ sourceOriginalRootListLabel434 H j.val := by
    unfold sourceOriginalRootListLabel434
    rw [hj]
    cases hh : H.getD i.val none  <;> simp [Option.elim,hij]
  simp [sourceOriginalRootForestEdge434,hp,he]

theorem source_original_root_FOREST_EDGE_NUMERIC434 {A : ℕ}
    (p : SourceOriginalRootForest434 A) (H : List (Option ℕ))
    (i : Fin A) (j : Fin i.val) (hp : p i=some j) (v : ℕ)
    (hj : H.getD j.val none=some v) :
    sourceOriginalRootForestEdge434 p H i=
      if H.getD i.val none=some v then 1 else 0 := by
  unfold sourceOriginalRootForestEdge434
  rw [hp]
  simp only [Option.elim,sourceOriginalRootListLabel434,hj]
  cases hh : H.getD i.val none  <;> simp [Option.elim]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootBatchElimination -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem source_original_root_OPTION_ND_GETD434
    (B : List (Option ℕ)) (hB : (B.filterMap id).Nodup)
    (i j v : ℕ) (hi : i < B.length) (hj : j < B.length)
    (hvi : B.getD i none=some v) (hvj : B.getD j none=some v) : i=j := by
  let f : Fin B.length → Option ℕ := fun k => B.getD k.val none
  have hf : List.ofFn f=B := by
    have he : f=B.get := by
      funext k
      exact List.getD_eq_getElem B none k.isLt
    rw [he,List.ofFn_get]
  have hnd : ((List.ofFn f).filterMap id).Nodup := by rw [hf]; exact hB
  have hh := (source_original_root_FILTER_OF_FN_NODUP434 f).mp hnd
    ⟨i,hi⟩ ⟨j,hj⟩ v hvi hvj
  exact congrArg Fin.val hh

/-- A same-batch edge is zero under the RETAINED numerical local ND.
Neither inactive padding nor repeated numeric arrays are assumed injective. -/
theorem source_original_root_SAME_BATCH_EDGE_ZERO434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (H B : List (Option ℕ)) (hB : (B.filterMap id).Nodup)
    (i : Fin A) (j : Fin i.val) (hp : p i=some j)
    (hj : H.length ≤ j.val) (hi : i.val < (H++B).length) :
    sourceOriginalRootForestEdge434 p (H++B) i=0 := by
  have hi0 : H.length ≤ i.val := hj.trans j.isLt.le
  have hbi : i.val-H.length < B.length := by simp only [List.length_append] at hi; omega
  have hbj : j.val-H.length < B.length := by simp only [List.length_append] at hi; omega
  have he : sourceOriginalRootListLabel434 (H++B) i.val ≠
      sourceOriginalRootListLabel434 (H++B) j.val := by
    intro heq
    have hh := (source_original_root_DECODE_EQUALITY434 i.val j.val
      (ne_of_gt j.isLt) ((H++B).getD i.val none) ((H++B).getD j.val none)).mp heq
    obtain ⟨v,hv1,hv2⟩ := hh
    rw [List.getD_append_right H B none i.val hi0] at hv1
    rw [List.getD_append_right H B none j.val hj] at hv2
    have hsub := source_original_root_OPTION_ND_GETD434 B hB _ _ v hbi hbj hv1 hv2
    omega
  simp [sourceOriginalRootForestEdge434,hp,he]

theorem source_original_root_SAME_BATCH_ZERO434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (H B : List (Option ℕ)) (hB : (B.filterMap id).Nodup)
    (i : Fin A) (j : Fin i.val) (hp : p i=some j)
    (hj : H.length ≤ j.val) (hi : i.val < (H++B).length) :
    sourceOriginalRootForestBatch434 p H.length (H++B)=0 := by
  unfold sourceOriginalRootForestBatch434
  apply Finset.prod_eq_zero_iff.mpr
  refine ⟨i,Finset.mem_univ _,?_⟩
  rw [if_pos (And.intro (hj.trans j.isLt.le) hi)]
  exact source_original_root_SAME_BATCH_EDGE_ZERO434 p H B hB i j hp hj hi

/-- Initial local ND was explicitly inserted at the original boundary.
Consequently any selected initial child annihilates that boundary. -/
theorem source_original_root_INITIAL_FOREST_ZERO434
    {A : ℕ} (p : SourceOriginalRootForest434 A)
    (H : List (Option ℕ)) (hH : (H.filterMap id).Nodup)
    (i : Fin A) (j : Fin i.val) (hp : p i=some j) (hi : i.val < H.length) :
    sourceOriginalRootForestPrefix434 p H=0 := by
  unfold sourceOriginalRootForestPrefix434
  apply Finset.prod_eq_zero_iff.mpr
  refine ⟨i,Finset.mem_univ _,?_⟩
  rw [if_pos hi]
  simpa only [List.nil_append] using
    source_original_root_SAME_BATCH_EDGE_ZERO434 p [] H hH i j hp (Nat.zero_le _) hi
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootPaddedRows -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Padding is solely a register readout. The FULL signed G row is kept,
including all b>T witnesses; only adjacent original gates kill them. -/
def sourceOriginalRootPaddedG434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List (Option ℕ))
    (F : Output → List (Option ℕ) → ℂ) (X : Output) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
    (fun x => ∑ y : State,∑ z : FullGhostWitness SP sm BP bm (J+ell) cap x,
      if (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup then
        physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z *
          F (physicalFockProjection SP sm BP bm (J+ell) cap y)
            (H++sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z)
      else 0) X

def sourceOriginalRootPaddedE434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (H : List (Option ℕ))
    (F : Output → List (Option ℕ) → ℂ) (X : Output) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
    (fun x => ∑ z ∈ sourceOrientedPhysicalChoices SP sm BP bm J ell m cap patterns x o k,
      if (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup then
        sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k x z *
          F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
            (H++sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z)
      else 0) X

theorem source_original_root_PADDED_E_EXACT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (H : List (Option ℕ))
    (F : Output → List ℕ → ℂ)
    (hF : ∀ Y H₁ H₂,H₁.Perm H₂ → F Y H₁=F Y H₂) (X : Output) :
    sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k H (fun Y H' => F Y (H'.filterMap id)) X =
    sourceOriginalForestListedE434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k (H.filterMap id) F X := by
  unfold sourceOriginalRootPaddedE434 sourceOriginalForestListedE434
  apply congrArg (fun f : State → ℂ =>
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext x
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hn : (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup
  · simp only [if_pos hn,List.filterMap_append]
    rw [hF _ _ _ ((List.Perm.refl _).append
      (source_original_root_E_PAD_BIRTHS434 SP sm BP bm J ell m cap patterns x z))]
  · simp only [if_neg hn]

/-- Pointwise support adapter: a nonzero actual G witness whose output
passes the next E input gate lies within the fixed potential width. -/
theorem source_original_root_G_PAD_GOOD434
    (q rho : ℝ) (N i T : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : State) (z : FullGhostWitness SP sm BP bm (J+ell) cap x)
    (hn : physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z ≠ 0)
    (ht : (∑ g,((physicalFockProjection SP sm BP bm (J+ell) cap y).2 g).2.card)≤T) :
    ∀ g,(z g).2.1.val≤T := by
  intro g
  have hb := source_original_forest_G_BIRTHS_LE_OLD434 SP sm BP bm J ell cap
    q rho N i V mu x y z hn g
  have hs : (y.2 g).2.1.val ≤ ∑ a : BG,(y.2 a).2.1.val :=
    Finset.single_le_sum (f := fun a : BG => (y.2 a).2.1.val)
      (fun a _ => Nat.zero_le _) (Finset.mem_univ g)
  have ht' : (∑ a : BG,(y.2 a).2.1.val)≤T := by
    simpa [physicalFockProjection,Green64Fock.fockMultiset] using ht
  exact hb.trans (hs.trans ht')

theorem source_original_root_PADDED_G_OLD_EXACT434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List (Option ℕ))
    (F : Output → List ℕ → ℂ) (X : Output) :
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
      (fun Y H' => if (∑ g,(Y.2 g).2.card)≤T then F Y (H'.filterMap id) else 0) X =
    sourceOriginalForestListedG434 SP sm BP bm J ell cap q rho N i Vs V mu
      (H.filterMap id) (fun Y H' => if (∑ g,(Y.2 g).2.card)≤T then F Y H' else 0) X := by
  unfold sourceOriginalRootPaddedG434 sourceOriginalForestListedG434
  apply congrArg (fun f : State → ℂ =>
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext x
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hnd : (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup
  · simp only [if_pos hnd]
    by_cases hn : physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z=0
    · simp only [hn,zero_mul]
    · by_cases ht : (∑ g,((physicalFockProjection SP sm BP bm (J+ell) cap y).2 g).2.card)≤T
      · have hg := source_original_root_G_PAD_GOOD434 SP sm BP bm J ell cap q rho N i T V mu x y z hn ht
        simp only [if_pos ht,List.filterMap_append,
          source_original_root_G_PAD_BIRTHS434 SP sm BP bm J ell cap T x z hg]
      · simp only [if_neg ht,mul_zero]
  · simp only [if_neg hnd]

theorem source_original_root_PADDED_G_TERMINAL_EXACT434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List (Option ℕ)) (X : Output) :
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
      (fun Y H' => if (H'.filterMap id).Nodup then physicalVacuum SP sm BP bm J ell Y else 0) X =
    sourceOriginalForestListedG434 SP sm BP bm J ell cap q rho N i Vs V mu
      (H.filterMap id) (fun Y H' => if H'.Nodup then physicalVacuum SP sm BP bm J ell Y else 0) X := by
  unfold sourceOriginalRootPaddedG434 sourceOriginalForestListedG434
  apply congrArg (fun f : State → ℂ =>
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext x
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hnd : (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup
  · simp only [if_pos hnd]
    by_cases hn : physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z=0
    · simp only [hn,zero_mul]
    · by_cases hv : physicalVacuum SP sm BP bm J ell
          (physicalFockProjection SP sm BP bm (J+ell) cap y)=0
      · simp only [hv,ite_self,mul_zero]
      · have hg : ∀ g,(z g).2.1.val≤T := by
          intro g
          rw [source_original_forest_TERMINAL_G_NO_BIRTH434 SP sm BP bm J ell cap
            q rho N i V mu x y z hn hv g]
          exact Nat.zero_le _
        simp only [List.filterMap_append,
          source_original_root_G_PAD_BIRTHS434 SP sm BP bm J ell cap T x z hg]
  · simp only [if_neg hnd]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootActualListPhase -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

theorem source_original_root_ORBIT_SCALE434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (c : ℂ) (F : State → ℂ) (X : Output) :
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu (fun x => c*F x) X =
      c*fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu F X := by
  unfold fullPhysicalOrbitAverage
  rw [←mul_div_assoc,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem source_original_root_ORBIT_INPUT_MASK434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (P : Output → Prop) (F : State → ℂ) (X : Output) :
    (if P X then fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu F X else 0) =
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
      (fun x => if P (physicalFockProjection SP sm BP bm (J+ell) cap x) then F x else 0) X := by
  by_cases hp : P X
  · rw [if_pos hp]
    unfold fullPhysicalOrbitAverage
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    dsimp only
    rw [(Finset.mem_filter.mp hx).2,if_pos hp]
  · rw [if_neg hp]
    unfold fullPhysicalOrbitAverage
    have hz :
        (∑ x ∈ (Finset.univ : Finset State) with
          physicalFockProjection SP sm BP bm (J+ell) cap x=X,
          (fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x:ℂ) *
            (if P (physicalFockProjection SP sm BP bm (J+ell) cap x) then F x else 0))=0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [(Finset.mem_filter.mp hx).2,if_neg hp,mul_zero]
    rw [hz,zero_div]

/-- Exact G localization of fixed-address slot phases. The phase is
inside every original representative sum, on the full untruncated G. -/
theorem source_original_root_PADDED_G_PHASE434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (phi : ℕ → Option ℕ → ℂ)
    (H : List (Option ℕ)) (F : Output → ℂ) (X : Output) :
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
      (fun Y H' => sourceOriginalRootListPhase434 phi 0 H' * F Y) X =
    sourceOriginalRootListPhase434 phi 0 H *
      sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap
        q rho N i Vs V mu
        (fun x z => sourceOriginalRootListPhase434 phi H.length
          (sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z)) F X := by
  unfold sourceOriginalRootPaddedG434 sourceOriginalUnfilteredEvolutionSeenErasedG434
  rw [←source_original_root_ORBIT_SCALE434]
  apply congrArg (fun f : State → ℂ =>
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext x
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hn : (physicalGhostFreshBirths SP sm BP bm (J+ell) cap x z).Nodup
  · simp only [if_pos hn,source_original_root_LIST_PHASE_APPEND434,Nat.zero_add]
    ring
  · simp only [if_neg hn,mul_zero]

/-- Exact localization into the actual phased FULL E, with original K
oriented once, fixed zeta, local ND and BOTH physical OLD gates. -/
theorem source_original_root_PADDED_E_PHASE434
    (q rho : ℝ) (T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (phi : ℕ → Option ℕ → ℂ)
    (H : List (Option ℕ)) (F : Output → ℂ) (X : Output) :
    (if sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T X then
      sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu (memoryOrientationK BP J ell m patterns K o) zeta theta o k H
        (fun Y H' => if sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T Y then
          sourceOriginalRootListPhase434 phi 0 H' * F Y else 0) X else 0) =
    sourceOriginalRootListPhase434 phi 0 H *
      sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
        (fun _ _ => True)
        (fun x z => sourceOriginalRootListPhase434 phi H.length
          (sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z))
        q rho Vs V mu K T zeta theta o k F X := by
  unfold sourceOriginalRootPaddedE434 sourceOriginalUnfilteredEdgeSeenErasedPhase434
  rw [source_original_root_ORBIT_INPUT_MASK434,←source_original_root_ORBIT_SCALE434]
  apply congrArg (fun f : State → ℂ =>
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext x
  unfold sourceOriginalUnfilteredEdgePhasedLocal434
  by_cases hs : sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
      (physicalFockProjection SP sm BP bm (J+ell) cap x)
  · simp only [if_pos hs,sourceOrientedPhysicalChoices,Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hl : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z <;>
      by_cases hn : (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup <;>
      by_cases ht : sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
        (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z) <;>
      simp [sourceOriginalUnfilteredEdgeLiteralKeep434,hs,hl,hn,ht,
        source_original_root_LIST_PHASE_APPEND434] <;> ring
  · simp [sourceOriginalUnfilteredEdgeLiteralKeep434,hs]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootPaddedChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- The actual chronological source chain with fixed-width Option readouts.
The full original G sums, both OLD gates and final G/vacuum are retained. -/
def sourceOriginalRootPaddedGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ) :
    (remaining start : ℕ) → Output → List (Option ℕ) → ℂ
  | 0,start => fun Y H =>
      sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N start T Vs V mu H
        (fun out H' => if (H'.filterMap id).Nodup then physicalVacuum SP sm BP bm J ell out else 0) Y
  | n+1,start => fun Y H =>
      sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N start T Vs V mu H
        (fun yg hg => if (∑ g : BG,(yg.2 g).2.card) ≤ T then
          sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k hg
            (fun out ht => if (∑ g : BG,(out.2 g).2.card) ≤ T then
              sourceOriginalRootPaddedGEChain434 q rho Vs V mu K zeta theta k N T
                n (start+1) out ht else 0) yg
        else 0) Y

/-- Literal source identification: Option padding changes no scalar,
including repeated prior labels and zero-mass physical fibres. -/
theorem source_original_root_PADDED_CHAIN_EXACT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (n start : ℕ) (Y : Output) (H : List (Option ℕ)) :
    sourceOriginalRootPaddedGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start Y H =
    sourceOriginalForestListedGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start
      (physicalVacuum SP sm BP bm J ell) Y (H.filterMap id) := by
  induction n generalizing start Y H with
  | zero =>
    exact source_original_root_PADDED_G_TERMINAL_EXACT434
      SP sm BP bm J ell cap q rho N start T Vs V mu H Y
  | succ n ih =>
    let K' := memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start)
    let C := fun (out : Output) (ht : List ℕ) =>
      if (∑ g : BG,(out.2 g).2.card) ≤ T then
        sourceOriginalForestListedGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T n (start+1)
          (physicalVacuum SP sm BP bm J ell) out ht else 0
    have hC : ∀ out H₁ H₂,H₁.Perm H₂ → C out H₁=C out H₂ := by
      intro out H₁ H₂ hp
      dsimp only [C]
      rw [source_original_root_LISTED_CHAIN_PERM434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n (start+1)
        (physicalVacuum SP sm BP bm J ell) out H₁ H₂ hp]
    have hE (yg : Output) (hg : List (Option ℕ)) :
        sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K' zeta theta (physicalAlternatingSign start) k hg
          (fun out ht => if (∑ g : BG,(out.2 g).2.card) ≤ T then
            sourceOriginalRootPaddedGEChain434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu K zeta theta k N T n (start+1) out ht else 0) yg =
        sourceOriginalForestListedE434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K' zeta theta (physicalAlternatingSign start) k (hg.filterMap id) C yg := by
      have hf :
          (fun (out : Output) (ht : List (Option ℕ)) => if (∑ g : BG,(out.2 g).2.card) ≤ T then
            sourceOriginalRootPaddedGEChain434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu K zeta theta k N T n (start+1) out ht else 0) =
          (fun out ht => C out (ht.filterMap id)) := by
        funext out ht
        dsimp only [C]
        rw [ih]
      rw [hf]
      exact source_original_root_PADDED_E_EXACT434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K' zeta theta (physicalAlternatingSign start) k hg C hC yg
    simp only [sourceOriginalRootPaddedGEChain434,sourceOriginalForestListedGEChain434]
    calc
      _ = sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N start T Vs V mu H
          (fun yg hg => if (∑ g : BG,(yg.2 g).2.card) ≤ T then
            sourceOriginalForestListedE434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu K' zeta theta (physicalAlternatingSign start) k (hg.filterMap id) C yg else 0) Y := by
        apply congrArg (fun f : Output → List (Option ℕ) → ℂ =>
          sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N start T Vs V mu H f Y)
        funext yg hg
        rw [hE]
      _ = _ := source_original_root_PADDED_G_OLD_EXACT434
        SP sm BP bm J ell cap q rho N start T Vs V mu H
        (fun yg hg => sourceOriginalForestListedE434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K' zeta theta (physicalAlternatingSign start) k hg C yg) Y

def sourceOriginalRootPaddedRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N:ℂ)*
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y:ℂ)*
      star (physicalVacuum SP sm BP bm J ell y)*
      sourceOriginalRootPaddedGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T N 0 y
        ((physicalOutputInitialBirths SP sm BP bm J ell y).map some)

/-- Fixed potential padding identifies the EXISTING original projected
root, not a modified representative-path or independent-residue process. -/
theorem source_original_root_PADDED_ROOT_EXACT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    sourceOriginalRootPaddedRoot434 SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T =
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T := by
  rw [←source_original_forest_LISTED_ROOT_EXACT434]
  unfold sourceOriginalRootPaddedRoot434 sourceOriginalForestListedRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  rw [source_original_root_PADDED_CHAIN_EXACT434]
  simp
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootFunctionalChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

theorem source_original_root_PADDED_G_LENGTH_CONSTANT434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List (Option ℕ))
    (F : ℕ → Output → List (Option ℕ) → ℂ) (X : Output) :
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
      (fun Y H' => F H'.length Y H') X =
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H
      (F (H.length+Fintype.card BG*T)) X := by
  simp only [sourceOriginalRootPaddedG434,List.length_append,source_original_root_G_PAD_LENGTH434]

theorem source_original_root_PADDED_E_LENGTH_CONSTANT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (H : List (Option ℕ))
    (F : ℕ → Output → List (Option ℕ) → ℂ) (X : Output) :
    sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta o k H (fun Y H' => F H'.length Y H') X =
    sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta o k H (F (H.length+Fintype.card BG*(J+ell))) X := by
  simp only [sourceOriginalRootPaddedE434,List.length_append,source_original_root_E_PAD_LENGTH434]

/-- The literal source chain acts on arbitrary final register tests.
It retains original row masks and re-averages representatives each visit. -/
def sourceOriginalRootFunctionalChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (terminal : Output → List (Option ℕ) → ℂ) :
    (remaining start : ℕ) → Output → List (Option ℕ) → ℂ
  | 0,start => fun Y H =>
      sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N start T Vs V mu H terminal Y
  | n+1,start => fun Y H =>
      sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N start T Vs V mu H
        (fun yg hg => if (∑ g : BG,(yg.2 g).2.card) ≤ T then
          sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k hg
            (fun out ht => if (∑ g : BG,(out.2 g).2.card) ≤ T then
              sourceOriginalRootFunctionalChain434 q rho Vs V mu K zeta theta k N T terminal
                n (start+1) out ht else 0) yg else 0) Y

theorem source_original_root_FUNCTIONAL_NODUP_EXACT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (n start : ℕ) (Y : Output) (H : List (Option ℕ)) :
    sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T
      (fun out H' => if (H'.filterMap id).Nodup then physicalVacuum SP sm BP bm J ell out else 0)
      n start Y H =
    sourceOriginalRootPaddedGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start Y H := by
  induction n generalizing start Y H with
  | zero => rfl
  | succ n ih =>
    simp only [sourceOriginalRootFunctionalChain434,sourceOriginalRootPaddedGEChain434,ih]

/-- Fixed chronological offset, not a path-dependent count of performed
births. Every G has n*T slots and every E has n*(J+ell) slots. -/
def sourceOriginalRootPhaseGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (phi : ℕ → Option ℕ → ℂ) (F : Output → ℂ) :
    (remaining start offset : ℕ) → Output → ℂ
  | 0,start,offset =>
      sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap q rho N start Vs V mu
        (fun x z => sourceOriginalRootListPhase434 phi offset
          (sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z)) F
  | n+1,start,offset =>
      sourceOriginalUnfilteredEvolutionSeenErasedG434 SP sm BP bm (J+ell) cap q rho N start Vs V mu
        (fun x z => sourceOriginalRootListPhase434 phi offset
          (sourceOriginalRootGPad434 SP sm BP bm J ell cap T x z))
        (sourceOriginalUnfilteredEdgeSeenErasedPhase434 SP sm BP bm J ell m cap patterns
          (fun _ _ => True)
          (fun x z => sourceOriginalRootListPhase434 phi (offset+Fintype.card BG*T)
            (sourceOriginalRootEPad434 SP sm BP bm J ell m cap patterns x z))
          q rho Vs V mu K T zeta theta (physicalAlternatingSign start) k
          (sourceOriginalRootPhaseGEChain434 q rho Vs V mu K zeta theta k N T phi F
            n (start+1) (offset+Fintype.card BG*T+Fintype.card BG*(J+ell))))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredRootFunctionalLength -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

theorem source_original_root_PADDED_G_CONGR_LENGTH434
    (q rho : ℝ) (N i T : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (H : List (Option ℕ))
    (F F' : Output → List (Option ℕ) → ℂ)
    (hF : ∀ Y H',H'.length=H.length+Fintype.card BG*T → F Y H'=F' Y H')
    (X : Output) :
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H F X =
    sourceOriginalRootPaddedG434 SP sm BP bm J ell cap q rho N i T Vs V mu H F' X := by
  unfold sourceOriginalRootPaddedG434
  apply congrArg (fun f : State → ℂ => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext x
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  rw [hF _ _ (by simp only [List.length_append,source_original_root_G_PAD_LENGTH434])]

theorem source_original_root_PADDED_E_CONGR_LENGTH434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (H : List (Option ℕ))
    (F F' : Output → List (Option ℕ) → ℂ)
    (hF : ∀ Y H',H'.length=H.length+Fintype.card BG*(J+ell) → F Y H'=F' Y H')
    (X : Output) :
    sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta o k H F X =
    sourceOriginalRootPaddedE434 SP sm BP bm J ell m cap patterns q rho Vs V mu K
      zeta theta o k H F' X := by
  unfold sourceOriginalRootPaddedE434
  apply congrArg (fun f : State → ℂ => fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu f X)
  funext x
  apply Finset.sum_congr rfl
  intro z hz
  rw [hF _ _ (by simp only [List.length_append,source_original_root_E_PAD_LENGTH434])]

/-- Final-register replacement only at the fixed potential length.
This includes the terminal G batch, even though its performed births vanish. -/
theorem source_original_root_FUNCTIONAL_CONGR_LENGTH434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (n start : ℕ) (F F' : Output → List (Option ℕ) → ℂ)
    (Y : Output) (H : List (Option ℕ))
    (hF : ∀ Y' H',H'.length=H.length+(n+1)*(Fintype.card BG*T)+n*(Fintype.card BG*(J+ell)) →
      F Y' H'=F' Y' H') :
    sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T F n start Y H =
    sourceOriginalRootFunctionalChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T F' n start Y H := by
  induction n generalizing start Y H with
  | zero =>
    apply source_original_root_PADDED_G_CONGR_LENGTH434 SP sm BP bm J ell cap
      q rho N start T Vs V mu H F F'
    intro Y' H' hh
    exact hF Y' H' (by simpa using hh)
  | succ n ih =>
    simp only [sourceOriginalRootFunctionalChain434]
    apply source_original_root_PADDED_G_CONGR_LENGTH434 SP sm BP bm J ell cap
      q rho N start T Vs V mu H
    intro yg hg hhg
    by_cases hold : (∑ g : BG,(yg.2 g).2.card)≤T
    · rw [if_pos hold,if_pos hold]
      apply source_original_root_PADDED_E_CONGR_LENGTH434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
        zeta theta (physicalAlternatingSign start) k hg
      intro out ht hht
      by_cases hold' : (∑ g : BG,(out.2 g).2.card)≤T
      · rw [if_pos hold',if_pos hold']
        apply ih
        intro Y' H' hh
        apply hF
        rw [hht,hhg] at hh
        simp only [Nat.add_mul,Nat.one_mul] at *
        omega
      · rw [if_neg hold',if_neg hold']
    · rw [if_neg hold,if_neg hold]
end Green64Analytic.CorrelationSquare

end

end

