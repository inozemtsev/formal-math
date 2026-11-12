module

public import Green64.Library.Weights.ActualFrameFilteredLiteral
public import Green64.Library.Correlation.Part048
public import Green64.Library.Weights.Part027
public import Green64.Library.Weights.Part028
public import Green64.Library.Correlation.Part047
public import Green64.Library.Analysis.Estimates.Part013
public import Green64.Library.Correlation.Part029
public import Green64.Library.Correlation.Part030
public import Green64.Library.Correlation.Part044
public import Green64.Library.Correlation.Part043

@[expose] public section

/-!
# Correlation / Part049

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualFrameProjectedDirtyBridge -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Projected genuine DIRTY frame operator, retaining ORIGINAL weighted
Fock orbit average rather than evaluating one arbitrary representative. -/
def sourceOriginalActualFrameProjectedDirty434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (H : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) : ℂ :=
  let PF := fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ H)
    (Classical.propDecidable _) (F out st) 0
  if (∑ g : BG,(y.2 g).2.card) ≤ H then
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
      (fun x => sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x seen PF) y else 0

/-- The local marked DIRTY operator is the exact weighted Fock average
of the physical dirty E-frame row on the ORIGINAL reachable sector.
No independent-frame count, cancellation hypothesis or orbit shortcut. -/
theorem source_original_ACTUAL_MARKED_projected_DIRTY_frame_average434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (H : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    sourceOriginalMemoryMarkedProjectedDirty434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k H F y seen =
    sourceOriginalActualFrameProjectedDirty434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k H F y seen := by
  classical
  unfold sourceOriginalMemoryMarkedProjectedDirty434 sourceOriginalActualFrameProjectedDirty434
  dsimp only
  by_cases hp : (∑ g : BG,(y.2 g).2.card) ≤ H
  · simp only [if_pos hp]
    unfold fullPhysicalOrbitAverage
    apply congrArg (fun v : ℂ => v / (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ))
    apply Finset.sum_congr rfl
    intro x hx
    have hxreach : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
        (physicalFockProjection SP sm BP bm (J+ell) cap x) seen := by
      rw [(Finset.mem_filter.mp hx).2]
      exact hy
    apply congrArg (fun v : ℂ => (fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x : ℂ)*v)
    let PF : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
      fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ H)
        (Classical.propDecidable _) (F out st) 0
    change physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x seen PF -
      sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V mu K zeta theta o k x seen PF =
      sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x seen PF
    rw [source_original_SOURCE_MARKED_E_frame_row434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen hxreach PF]
    rw [source_original_SOURCE_MARKED_CLEAN_frame_row434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen hxreach PF]
    rw [source_original_FRAME_E_clean_dirty_split434]
    ring
  · simp only [if_neg hp]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualCleanOrbitReindex -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)


/-- E OLD-permutation reindexing changes only the injection's OLD
indices, not whether source branches promote or store particles. -/
theorem source_original_SOURCE_CLEAN_reindex434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (e : (g : BG) → Equiv.Perm (Fin (x.2 g).2.1.val))
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns
      (sourceOriginalFullEReindexState434 SP sm BP bm (J+ell) cap x e)
      (sourceOriginalFullEChoiceReindex434 SP sm BP bm cap J ell m patterns x e z) ↔
    sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns x z := by
  rfl

/-- Original literal CLEAN witness sum is invariant under arbitrary
OLD Fock-coordinate permutations, not merely the unfiltered E row. -/
theorem source_original_SOURCE_MARKED_CLEAN_E_reindex434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (e : (g : BG) → Equiv.Perm (Fin (x.2 g).2.1.val))
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k
      (sourceOriginalFullEReindexState434 SP sm BP bm (J+ell) cap x e) seen F =
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k x seen F := by
  classical
  unfold sourceOriginalMemoryMarkedFilteredE434
  symm
  apply Fintype.sum_equiv (sourceOriginalFullEChoiceReindex434
    SP sm BP bm cap J ell m patterns x e)
  intro z
  rw [source_original_SOURCE_E_reindex_legal434,
    source_original_SOURCE_E_reindex_coefficient434,
    source_original_SOURCE_E_reindex_output434]
  simp only [orientedEFreshBatchEligible,source_original_SOURCE_E_reindex_births434]
  rw [source_original_SOURCE_CLEAN_reindex434]
  rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualCleanOrbitRepresentative -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)


theorem source_original_SOURCE_MARKED_CLEAN_E_orbit_invariant434
    (x y : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hxy : physicalFockProjection SP sm BP bm (J+ell) cap x =
      physicalFockProjection SP sm BP bm (J+ell) cap y)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap y) seen)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k y seen F =
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k x seen F := by
  obtain ⟨e,rfl⟩ := source_original_REACHABLE_orbit_reindex434
    SP sm BP bm (J+ell) cap x y seen hxy hy
  exact source_original_SOURCE_MARKED_CLEAN_E_reindex434
    SP sm BP bm J ell m cap patterns x e q rho Vs V mu K zeta theta o k seen F

/-- The original full physical Fock orbit average of CLEAN equals its
source OLD representative; the orbit mass is paid once, with no
flat-counting replacement or abstract conditional expectation premise. -/
theorem source_original_SOURCE_MARKED_CLEAN_E_orbit_representative434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V mu K zeta theta o k st seen F)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) =
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k x seen F := by
  let out := physicalFockProjection SP sm BP bm (J+ell) cap x
  have hpos : (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu out : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (physicalOrbitMass_pos SP sm BP bm (J+ell) cap
      Vs mu hVs hmu out (Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩)))
  have hc (y : FullPhysicalState SP sm BP bm (J+ell) cap)
      (hy : physicalFockProjection SP sm BP bm (J+ell) cap y=out) :
      sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V mu K zeta theta o k y seen F =
      sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V mu K zeta theta o k x seen F := by
    exact (source_original_SOURCE_MARKED_CLEAN_E_orbit_invariant434
      SP sm BP bm J ell m cap patterns y x seen hy hx
      q rho Vs V mu K zeta theta o k F).symm
  unfold fullPhysicalOrbitAverage
  change (∑ y ∈ (Finset.univ : Finset (FullPhysicalState SP sm BP bm (J+ell) cap))
      with physicalFockProjection SP sm BP bm (J+ell) cap y=out,
      (fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
        sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
          (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
          q rho Vs V mu K zeta theta o k y seen F) /
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu out : ℂ) = _
  have hn :
      (∑ y ∈ (Finset.univ : Finset (FullPhysicalState SP sm BP bm (J+ell) cap))
        with physicalFockProjection SP sm BP bm (J+ell) cap y=out,
        (fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
          sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
            (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
            q rho Vs V mu K zeta theta o k y seen F) =
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu out : ℂ) *
        sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
          (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
          q rho Vs V mu K zeta theta o k x seen F := by
    unfold physicalOrbitMass
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hc y (Finset.mem_filter.mp hy).2]
  rw [hn]
  exact mul_div_cancel_left₀ _ hpos
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualCleanCanonicalProjected -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)


/-- Literal frame CLEAN row with both total-OLD endpoint gates is
the Fock-averaged physical P CLEAN P on the actual reachable sector.
This is an operator identity; no local L2 or transference premise. -/
theorem source_original_ACTUAL_CLEAN_frame_projected_exact434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    (if (∑ g : BG,(y.2 g).2.card) ≤ T then
      sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y) seen
        (fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ T)
          (Classical.propDecidable _) (F out st) 0)
    else 0) =
    sourceOriginalMemoryMarkedProjectedE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k T F y seen := by
  classical
  let x := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y
  have hp : physicalFockProjection SP sm BP bm (J+ell) cap x = y :=
    source_original_REACHABLE_canonical_projection434
      SP sm BP bm (J+ell) cap hcap y seen hy
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen := by
    simpa only [hp] using hy
  let PF : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ T)
      (Classical.propDecidable _) (F out st) 0
  have hLiteral := source_original_SOURCE_MARKED_CLEAN_frame_row434
    SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta o k x seen hx PF
  have hOrbit := source_original_SOURCE_MARKED_CLEAN_E_orbit_representative434
    SP sm BP bm J ell m cap patterns x seen hx
    q rho Vs V mu hVs hmu K zeta theta o k PF
  rw [hp] at hOrbit
  unfold sourceOriginalMemoryMarkedProjectedE434
  by_cases ht : (∑ g : BG,(y.2 g).2.card) ≤ T
  · simp only [if_pos ht]
    exact (hOrbit.trans hLiteral).symm
  · simp only [if_neg ht]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFrameThetaModes -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "Frame" => SourceOriginalSourceEFrame434 SP sm BP J ell m patterns

/-- Frequency of an ACTUALLY admissible original physical source E
frame. Inadmissible frames have zero weight and arbitrary frequency 0. -/
def sourceOriginalActualFrameThetaFreq434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (seen : Finset ℕ) (o k : ℤ) (r : Frame) : ℕ :=
  if h : ∃ f : SourceOriginalSourceEFrameInjections434
      SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434
        SP sm BP bm J ell m cap patterns x seen o k r f then
    let z := sourceOriginalSourceEFrameLift434
      SP sm BP bm J ell m cap patterns x r (Classical.choose h)
    sourceOrientedPhysicalD SP sm BP bm J ell m cap
      (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1
  else 0

/-- Exact complex theta=0 amplitude for this SAME physical frame.
The joint RAW/comparison K, full numerical seen, two endpoint
permutations and the actual future F remain unchanged. -/
def sourceOriginalActualFrameThetaWeight434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (r : Frame) : ℂ :=
  if h : ∃ f : SourceOriginalSourceEFrameInjections434
      SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434
        SP sm BP bm J ell m cap patterns x seen o k r f then
    let z := sourceOriginalSourceEFrameLift434
      SP sm BP bm J ell m cap patterns x r (Classical.choose h)
    if keep x z then
      sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs Vb mu K zeta 0 o k x z *
        F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
          (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset)
    else 0
  else 0

/-- The ACTUAL marked/source signed E-frame is a finite Fourier
sum in theta, with authentic source D frequency and complex weights.
This does not claim that distinct chronological visits are orthogonal. -/
theorem source_original_ACTUAL_frame_E_theta_atoms434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm
      J ell m cap patterns keep q rho Vs Vb mu K zeta theta o k x seen F =
    ∑ r : Frame,
      sourceOriginalActualFrameThetaWeight434 SP sm BP bm J ell m cap patterns
        keep q rho Vs Vb mu K zeta o k x seen F r *
      originalReturnPhase theta o k
        (sourceOriginalActualFrameThetaFreq434
          SP sm BP bm J ell m cap patterns x seen o k r) := by
  classical
  unfold sourceOriginalSourceEFrameFilteredRow434
  apply Finset.sum_congr rfl
  intro r hr
  unfold sourceOriginalActualFrameThetaWeight434
    sourceOriginalActualFrameThetaFreq434
  by_cases h : ∃ f : SourceOriginalSourceEFrameInjections434
      SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434
        SP sm BP bm J ell m cap patterns x seen o k r f
  · simp only [dif_pos h]
    let z := sourceOriginalSourceEFrameLift434
      SP sm BP bm J ell m cap patterns x r (Classical.choose h)
    change (if keep x z then _ else 0) =
      (if keep x z then _ else 0) * _
    by_cases hc : keep x z
    · simp only [if_pos hc]
      rw [source_oriented_PHYSICAL_coefficient_theta_dephase434]
      ring
    · simp only [if_neg hc, zero_mul]
  · simp only [dif_neg h, zero_mul]

/-- Exact regrouping of any finite source return phases by their
physical divisor frequencies. No bound or loss of off-diagonal terms. -/
theorem source_original_finite_return_phase_group_by_D434
    {I : Type} [DecidableEq I] (s : Finset I)
    (freq : I → ℕ) (w : I → ℂ)
    (theta : ℝ) (o k : ℤ) :
    (∑ r ∈ s, w r * originalReturnPhase theta o k (freq r)) =
    ∑ d ∈ s.image freq,
      (∑ r ∈ s.filter (fun r => freq r = d), w r) *
        originalReturnPhase theta o k d := by
  calc
    _ = ∑ d ∈ s.image freq,
          ∑ r ∈ s.filter (fun r => freq r = d),
            w r * originalReturnPhase theta o k (freq r) := by
          exact (Finset.sum_fiberwise_of_maps_to
            (s := s) (t := s.image freq) (g := freq)
            (fun r hr => Finset.mem_image_of_mem freq hr)
            (fun r => w r * originalReturnPhase theta o k (freq r))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      rw [(Finset.mem_filter.mp hr).2]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFrameThetaDMode -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "Frame" => SourceOriginalSourceEFrame434 SP sm BP J ell m patterns

/-- The true finite source E divisor-frequency support for a given
state and chronological seen; no fake prime interval or history reset. -/
def sourceOriginalActualFrameThetaSupport434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (seen : Finset ℕ) (o k : ℤ) : Finset ℕ :=
  (Finset.univ : Finset Frame).image
    (sourceOriginalActualFrameThetaFreq434
      SP sm BP bm J ell m cap patterns x seen o k)

/-- Exact signed sum of admissible physical E source frame amplitudes
with a common divisor D. Distinct frames with the same D interfere
INSIDE one mode; they must not be squared separately. -/
def sourceOriginalActualFrameThetaDMode434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (D : ℕ) : ℂ :=
  ∑ r ∈ (Finset.univ : Finset Frame).filter
    (fun r => sourceOriginalActualFrameThetaFreq434
      SP sm BP bm J ell m cap patterns x seen o k r = D),
      sourceOriginalActualFrameThetaWeight434 SP sm BP bm J ell m cap patterns
        keep q rho Vs Vb mu K zeta o k x seen F r

/-- Full ORIGINAL physical source E row grouped by TRUE numeric D;
theta is the only variable in the displayed Fourier phases. The
complete same-frequency signed amplitudes remain coherent. -/
theorem source_original_ACTUAL_frame_E_theta_D_modes434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm
      J ell m cap patterns keep q rho Vs Vb mu K zeta theta o k x seen F =
    ∑ D ∈ sourceOriginalActualFrameThetaSupport434
        SP sm BP bm J ell m cap patterns x seen o k,
      sourceOriginalActualFrameThetaDMode434 SP sm BP bm J ell m cap patterns
        keep q rho Vs Vb mu K zeta o k x seen F D *
      originalReturnPhase theta o k D := by
  rw [source_original_ACTUAL_frame_E_theta_atoms434]
  simpa only [sourceOriginalActualFrameThetaSupport434,
    sourceOriginalActualFrameThetaDMode434] using
    (source_original_finite_return_phase_group_by_D434
      (s := (Finset.univ : Finset Frame))
      (sourceOriginalActualFrameThetaFreq434
        SP sm BP bm J ell m cap patterns x seen o k)
      (sourceOriginalActualFrameThetaWeight434 SP sm BP bm J ell m cap patterns
        keep q rho Vs Vb mu K zeta o k x seen F)
      theta o k)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFullSmallJointHistoryDIRTY -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The actual S+Ts prime carrier provides the required physical nonzero
moduli directly; no fresh source assumption is imposed. -/
instance source_original_actual_SMALL_nonzero434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (data : SourceComparisonData434 ι β cfg x L Y Hp) :
    ∀ g : Option ι, ∀ p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g},
      NeZero p.val :=
  fun g p => ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩

/-- Literal JOINT-HISTORY DIRTY L2 estimate on the FULL S+Ts SMALL
carrier, obtained by authentic reindexing and quantified over arbitrary Fock×seen tests. The original
S set and its V_s are physical factors: no prime is erased.
The auxiliary original S field becomes empty ONLY in the source-data
interface used to invoke the established Ts physical estimate. -/
theorem eventually_source_original_ACTUAL_FULL_SMALL_JOINT_DIRTY_L2_saving434
    (cfg : SourceComparisonFixed434) (ell Jmin Cq Cxi : ℕ) (hell : 1 ≤ ell)
    (Ck q rho c0 B : ℝ) (hq : 0<q) (hq1 : q<1)
    (hr : 0< rho) (hr1 : rho<1) (hc0 : 0<c0) :
    let cfgP := sourceOriginalPromotedSmallFixed434 cfg
    let Ccol := sourceOriginalMemoryEColumnLoss434 cfgP ell Cq Cxi q rho
    let Bcolumn := 2*(B+1)+Ccol
    let K := sourceOriginalMemoryBigRowBase434 rho cfgP.vmin 2 (ell+cfg.tmax)
    let J := sourceOriginalMemoryRareSlotChoice434 (max Jmin cfg.tmax) c0 cfgP.C0 K
      (Bcolumn+sourceOriginalMemoryERowLoss434 cfgP ell Cq Cxi q)
    max Jmin cfg.tmax ≤ J ∧
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J) (cap : G → ℕ)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hSmallGroupsLower : c0*Real.log L ≤ (Fintype.card ι:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (Q : ℕ) (xi : ℝ) (hxi : 0<xi) (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (hA hB : SourceOriginalProbePattern434 G m → ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0<hB nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (F : FullPhysicalOutput
        (fun g => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let En := sourceOriginalMemoryMarkedEnergy434
      (fun g => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      J ell cap (sourceOriginalActualSmallMass434 data) data.Vbig mu
    En (sourceOriginalMemoryMarkedProjectedDirty434
      (fun g => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}) (fun _ p => p.val)
      (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
      J ell m cap (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
      q rho (sourceOriginalActualSmallMass434 data) data.Vbig mu
      (memoryOrientationK (fun g => {p : ℕ // p ∈ data.Tb g}) J ell m
        (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
        (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
          J ell m hmJ Q hA hB xi) o) zeta theta o k (Nat.ceil (L^2)) F) ≤
    L^(-(2*B))*En F 
 := by
  dsimp only
  let cfgP := sourceOriginalPromotedSmallFixed434 cfg
  have hLocal := source_original_memory_PHYSICAL_SOURCE_ORIENTED_MARKED_DIRTY_JOINT_L2_log_saving434
    cfgP ell Jmin Cq Cxi hell Ck q rho c0 B hq hq1 hr hr1 hc0
  refine ⟨hLocal.1,?_⟩
  filter_upwards [hLocal.2,eventually_ge_atTop (Real.exp 1)] with L hL hLarge
  intro ι G instI instDI instG instDG x Y Hp data sep instS instB
    m hm hmJ cap hSmallUpper hBigLower hHarmonic hSmallGroupsLower
    blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB
    zeta theta o k ho hk0 hk F
  have hlog : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hLarge
    simpa using hh
  let dataP := sourceOriginalPromotedSmallData434 data hlog
  have sepP : SourceOriginalSource03GroupSeparation434 dataP :=
    source_original_promoted_small_sep434 data hlog sep
  letI (g : Option ι) (p : {p : ℕ // p ∈ dataP.Ts g}) : NeZero p.val :=
    ⟨(dataP.hTsPrime g p.val p.property).ne_zero⟩
  letI (g : G) (p : {p : ℕ // p ∈ dataP.Tb g}) : NeZero p.val :=
    ⟨(dataP.hTbPrime g p.val p.property).ne_zero⟩
  have hUpper (g : Option ι) (p : ℕ) (hp : p ∈ dataP.Ts g) :
      (p:ℝ) ≤ Real.exp (L^cfgP.bexp) := by
    cases g with
    | none => exact (data.hSmall p hp).2
    | some i => exact hSmallUpper i p hp
  have hLower : c0*Real.log L ≤ (Fintype.card (Option ι):ℝ) := by
    rw [Fintype.card_option]
    push_cast
    nlinarith only [hSmallGroupsLower]
  exact hL x Y Hp dataP sepP m hm hmJ cap hUpper hBigLower hHarmonic hLower
    blockA blockB hBlocks Q xi hxi hQ hXi hA hB hhA hhB zeta theta o k ho hk0 hk
    F
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualProjectedCleanTelescoping -/

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

/-- The original frame G/E chain with both OLD projectors and literal
CLEAN selection at every E. This is the genuine original E-frame carrier. -/
def sourceOriginalOLDProjectedCleanFrameGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu y seen F
  | n+1,start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen (fun yg sg =>
          if (∑ g : BG,(yg.2 g).2.card) ≤ T then
            sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu
              (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
              zeta theta (physicalAlternatingSign start) k
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
              (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then
                sourceOriginalOLDProjectedCleanFrameGEChain434 q rho Vs V mu K zeta theta k N T
                  n (start+1) F out st else 0)
          else 0)

/-- A telescoping recursion with one DIRTY E insertion. It retains the
whole OLD-projector/mask history before insertion and the genuine
projected full continuation after insertion; no history-count payment. -/
def sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,_,_ => fun _ _ => 0
  | n+1,start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen (fun yg sg =>
          if (∑ g : BG,(yg.2 g).2.card) ≤ T then
            sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu
              (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
              zeta theta (physicalAlternatingSign start) k
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
              (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then
                sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
                  q rho Vs V mu K zeta theta k N T n (start+1) F out st else 0) +
            sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu
              (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
              zeta theta (physicalAlternatingSign start) k
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
              (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then
                sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434 q rho Vs V mu K zeta theta k
                  N T n (start+1) F out st else 0)
          else 0)

/-- Exact first-DIRTY telescoping in the source's full projected E-chain.
The insertion carries the original G, E, K, seen history and both P masks. -/
theorem source_original_MEMORY_PEP_PCLEAN_frame_telescoping434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F y seen -
    sourceOriginalOLDProjectedCleanFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F y seen =
    sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      simp only [sourceOriginalOLDProjectedFrameGEChain434,
        sourceOriginalOLDProjectedCleanFrameGEChain434,
        sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434,sub_self]
  | succ n ih =>
      dsimp only [sourceOriginalOLDProjectedFrameGEChain434,
        sourceOriginalOLDProjectedCleanFrameGEChain434,
        sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434]
      rw [←source_original_OLD_G_sub434]
      congr 1
      funext yg sg
      by_cases hy : (∑ g : BG,(yg.2 g).2.card) ≤ T
      · simp only [if_pos hy]
        let x := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg
        let KE := memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start)
        let PFull := fun (out : FullPhysicalOutput SP sm BP bm (J+ell)) (st : Finset ℕ) =>
          if (∑ g : BG,(out.2 g).2.card) ≤ T then
            sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu K zeta theta k N T n (start+1) F out st else 0
        let PClean := fun (out : FullPhysicalOutput SP sm BP bm (J+ell)) (st : Finset ℕ) =>
          if (∑ g : BG,(out.2 g).2.card) ≤ T then
            sourceOriginalOLDProjectedCleanFrameGEChain434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu K zeta theta k N T n (start+1) F out st else 0
        let PDiff := fun (out : FullPhysicalOutput SP sm BP bm (J+ell)) (st : Finset ℕ) =>
          if (∑ g : BG,(out.2 g).2.card) ≤ T then
            sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu K zeta theta k N T n (start+1) F out st else 0
        have hPoint : (fun out st => PFull out st-PClean out st)=PDiff := by
          funext out st
          by_cases ht : (∑ g : BG,(out.2 g).2.card) ≤ T
          · simp only [PFull,PClean,PDiff,if_pos ht]
            exact ih (start+1) out st
          · simp only [PFull,PClean,PDiff,if_neg ht,sub_self]
        have hSplit := source_original_FRAME_E_clean_dirty_split434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k x sg PFull
        have hClean :
            sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k x sg PFull -
            sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k x sg PClean =
            sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k x sg PDiff := by
          unfold sourceOriginalSourceEFrameCleanRow434
          rw [←source_original_FRAME_FILTERED_E_sub434]
          rw [hPoint]
        change sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k x sg PFull -
          sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k x sg PClean =
          sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k x sg PFull +
          sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k x sg PDiff
        rw [hSplit]
        calc
          _ = sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
                q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k x sg PFull +
              (sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
                q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k x sg PFull -
               sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
                q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k x sg PClean) := by ring
          _ = _ := by rw [hClean]
      · simp only [if_neg hy,sub_self]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualProjectedCleanRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 16000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

def sourceOriginalOLDProjectedFrameMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T N 0
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)


def sourceOriginalOLDProjectedCleanMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalOLDProjectedCleanFrameGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T N 0
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)


def sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T N 0
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)


/-- The authentic PEP root is exactly the frame-root PEP expression on
the source's reachable numerical inventory; no abstract operator is
substituted for its physical Fock/orbit kernel. -/
theorem source_original_MEMORY_OLD_projected_root_frame_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    sourceOriginalOLDProjectedFrameMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T := by
  unfold sourceOriginalOLDProjectedMemoryRoot434 sourceOriginalOLDProjectedFrameMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : physicalVacuum SP sm BP bm J ell y=0
  · simp only [hv,star_zero,mul_zero,zero_mul]
  · by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
    · simp only [if_pos hn]
      rw [source_original_MEMORY_OLD_projected_frame_exact434
        SP sm BP bm J ell m cap patterns hi hcap q rho Vs V _ hVs hmu K zeta theta
        k (2*R) T _ (2*R) 0 y _
        (source_original_MEMORY_initial_reachable434 SP sm BP bm J ell y hv hn)]
    · simp only [if_neg hn]

/-- Exact original projected-root discrepancy as an uncompressed sum of
one true CLEAN-vs-DIRTY E insertion across all chronological visits.
All Fock weights, physical baseline, both vacuum endpoints and birth
Nodup gate are still literal. No L2 or correlation saving is assumed. -/
theorem source_original_MEMORY_PEP_PCLEAN_root_telescoping434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T -
    sourceOriginalOLDProjectedCleanMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T := by
  rw [source_original_MEMORY_OLD_projected_root_frame_exact434
    SP sm BP bm J ell m cap patterns hd.big_injective hd.cap_saturated
    q rho Vs V K zeta theta k R T hd.Vsmall_pos
    (source_original_SOURCE_tilt_positive434 BP bm q hd.q_pos.le (2*R) V
      hd.Vbig_pos hd.big_above_visits)]
  unfold sourceOriginalOLDProjectedFrameMemoryRoot434
    sourceOriginalOLDProjectedCleanMemoryRoot434
    sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434
  dsimp only
  rw [←mul_sub,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
  · simp only [if_pos hn]
    rw [←mul_sub,source_original_MEMORY_PEP_PCLEAN_frame_telescoping434]
  · simp only [if_neg hn,mul_zero,sub_self]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualProjectedFrameLiteral -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)


/-- At a reachable source output, original literal P E P agrees with
the original oriented frame E applied at the canonical Fock state.
No CLEAN or positive analytic replacement is used. -/
theorem source_original_ACTUAL_FRAME_E_projected_exact434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    (if (∑ g : BG,(y.2 g).2.card) ≤ T then
      sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y) seen
        (fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ T)
          (Classical.propDecidable _) (F out st) 0)
    else 0) =
    sourceOriginalMemoryMarkedProjectedE434 SP sm BP bm J ell m cap patterns
      (fun _ _ => True) q rho Vs V mu K zeta theta o k T F y seen := by
  classical
  let x := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y
  have hp : physicalFockProjection SP sm BP bm (J+ell) cap x = y :=
    source_original_REACHABLE_canonical_projection434
      SP sm BP bm (J+ell) cap hcap y seen hy
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen := by
    simpa only [hp] using hy
  let PF : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ T)
      (Classical.propDecidable _) (F out st) 0
  have hFrame := source_original_SOURCE_MARKED_E_frame_row434
    SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta o k x seen hx PF
  have hOrbit := source_original_SOURCE_SYMMETRIC_E_canonical434
    SP sm BP bm cap J ell m patterns hcap y seen hy
    q rho Vs V mu hVs hmu K zeta theta o k PF
  rw [source_original_ACTUAL_PEP_projected_true434]
  by_cases ht : (∑ g : BG,(y.2 g).2.card) ≤ T
  · simp only [if_pos ht]
    exact (hOrbit.trans hFrame).symm
  · simp only [if_neg ht]

/-- TRUE projected DIRTY is exactly the frame E-CLEAN difference with
the very same P masks, real seen/primes and original coefficients.
No arbitrary positive bound is substituted. -/
theorem source_original_ACTUAL_FRAME_DIRTY_projected_exact434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    (if (∑ g : BG,(y.2 g).2.card) ≤ T then
      sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y) seen
        (fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ T)
          (Classical.propDecidable _) (F out st) 0)
    else 0) =
    sourceOriginalMemoryMarkedProjectedDirty434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k T F y seen := by
  classical
  let x := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y
  let PF : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ T)
      (Classical.propDecidable _) (F out st) 0
  have hSplit := source_original_FRAME_E_clean_dirty_split434
    SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta o k x seen PF
  have hFull := source_original_ACTUAL_FRAME_E_projected_exact434
    SP sm BP bm J ell m cap patterns hcap q rho Vs V mu hVs hmu
    K zeta theta o k T F y seen hy
  have hClean := source_original_ACTUAL_CLEAN_frame_projected_exact434
    SP sm BP bm J ell m cap patterns hcap q rho Vs V mu hVs hmu
    K zeta theta o k T F y seen hy
  have hDirty := source_original_ACTUAL_projected_TRUE_minus_CLEAN434
    SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta o k T F y seen
  rw [←hDirty,←hFull,←hClean]
  by_cases ht : (∑ g : BG,(y.2 g).2.card) ≤ T
  · simp only [if_pos ht]
    rw [hSplit]
    ring
  · simp only [if_neg ht,sub_self]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualProjectedReachable -/

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


/-- Every selected original CLEAN/DIRTY E branch propagates the actual
reachable numerical inventory. The keep predicate cannot introduce an
unreachable target. -/
theorem source_original_ACTUAL_FILTERED_E_reachable_congr434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (F A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (hFA : ∀ out st,sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) out st →
      F out st = A out st) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen F =
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen A := by
  classical
  unfold sourceOriginalMemoryMarkedFilteredE434
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hl : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z
  · by_cases hk : keep x z
    · by_cases he : orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z
      · simp only [hl,hk,he,true_and,and_true,ite_true]
        rw [hFA _ _ (source_original_SOURCE_ORIENTED_E_reachable434
          SP sm BP bm cap J ell m patterns x seen o k z hx hl he)]
      · simp only [hl,hk,he,and_false,ite_false]
    · simp [hl,hk]
  · simp only [hl,false_and,ite_false]

theorem source_original_ACTUAL_PROJECTED_FILTERED_E_reachable_congr434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (T : ℕ)
    (F A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (hFA : ∀ out st,sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) out st →
      F out st = A out st) :
    sourceOriginalMemoryMarkedProjectedE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k T F y seen =
    sourceOriginalMemoryMarkedProjectedE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k T A y seen := by
  classical
  unfold sourceOriginalMemoryMarkedProjectedE434
  by_cases ht : (∑ g : BG,(y.2 g).2.card) ≤ T
  · simp only [if_pos ht]
    apply source_original_ORBIT_reachable_congr434
      SP sm BP bm (J+ell) cap Vs mu _ _ y seen hy
    intro x hx
    apply source_original_ACTUAL_FILTERED_E_reachable_congr434
      SP sm BP bm J ell m cap patterns keep q rho Vs V mu K
      zeta theta o k x seen hx
    intro out st hr
    by_cases hcut : (∑ g : BG,(out.2 g).2.card) ≤ T
    · simp only [if_pos hcut]
      exact hFA out st hr
    · simp only [if_neg hcut]
  · simp only [if_neg ht]

theorem source_original_ACTUAL_PROJECTED_DIRTY_reachable_congr434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ) (T : ℕ)
    (F A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (hFA : ∀ out st,sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) out st →
      F out st = A out st) :
    sourceOriginalMemoryMarkedProjectedDirty434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k T F y seen =
    sourceOriginalMemoryMarkedProjectedDirty434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k T A y seen := by
  rw [←source_original_ACTUAL_projected_TRUE_minus_CLEAN434
    SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta o k T F y seen,
    ←source_original_ACTUAL_projected_TRUE_minus_CLEAN434
    SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta o k T A y seen]
  congr 1
  · exact source_original_ACTUAL_PROJECTED_FILTERED_E_reachable_congr434
      SP sm BP bm J ell m cap patterns (fun _ _ => True)
      q rho Vs V mu K zeta theta o k T F A y seen hy hFA
  · exact source_original_ACTUAL_PROJECTED_FILTERED_E_reachable_congr434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k T F A y seen hy hFA
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualProjectedDirtyPhysicalChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)


/-- The actual chronological first-DIRTY insertion chain written in
terms of the literal projected marked P(E-CLEAN)P and PCLEANP operators.
Full PEP continuation is the already-certified original frame chain.
The first insertion may occur at any visit; no history is counted twice. -/
def sourceOriginalOLDProjectedDirtyPhysicalInsertionGEChain434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ) :
    (remaining start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
  | 0,_,_ => fun _ _ => 0
  | n+1,start,F => fun y seen =>
      sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N start V mu
        y seen (fun yg sg =>
          sourceOriginalMemoryMarkedProjectedDirty434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k T
            (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu K zeta theta k N T n (start+1) F) yg sg +
          sourceOriginalMemoryMarkedProjectedE434 SP sm BP bm J ell m cap patterns
            (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
            q rho Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k T
            (sourceOriginalOLDProjectedDirtyPhysicalInsertionGEChain434
              q rho Vs V mu K zeta theta k N T n (start+1) F) yg sg)

/-- Exact frame-to-physical conversion of EVERY DIRTY insertion into
the authentic projected L2 operator, with reachable numerical history,
all original G/E signs and full endpoint continuation preserved.
No energetic or asymptotic saving premise is used. -/
theorem source_original_ACTUAL_DIRTY_insertion_physical_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F y seen =
    sourceOriginalOLDProjectedDirtyPhysicalInsertionGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F y seen := by
  induction n generalizing start y seen with
  | zero => rfl
  | succ n ih =>
      dsimp only [sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434,
        sourceOriginalOLDProjectedDirtyPhysicalInsertionGEChain434]
      apply source_original_G_unseen_reachable_congr434
        SP sm BP bm J ell cap hi hcap
        q rho N start Vs V mu hVs hmu y seen hy
      intro yg sg hg
      let KE := memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start)
      let FullNext := sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n (start+1) F
      let FrameNext := sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
        SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta k N T n (start+1) F
      let PhysicalNext := sourceOriginalOLDProjectedDirtyPhysicalInsertionGEChain434
        SP sm BP bm J ell m cap patterns q rho Vs V mu K zeta theta k N T n (start+1) F
      have hd := source_original_ACTUAL_FRAME_DIRTY_projected_exact434
        SP sm BP bm J ell m cap patterns hcap q rho Vs V mu hVs hmu KE
        zeta theta (physicalAlternatingSign start) k T FullNext yg sg hg
      have hc := source_original_ACTUAL_CLEAN_frame_projected_exact434
        SP sm BP bm J ell m cap patterns hcap q rho Vs V mu hVs hmu KE
        zeta theta (physicalAlternatingSign start) k T FrameNext yg sg hg
      have hr := source_original_ACTUAL_PROJECTED_FILTERED_E_reachable_congr434
        SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k T
        FrameNext PhysicalNext yg sg hg
        (fun out st hOut => ih (start+1) out st hOut)
      have hFullMask :
          (fun (out : FullPhysicalOutput SP sm BP bm (J+ell)) st =>
            if (∑ g : BG,(out.2 g).2.card) ≤ T then FullNext out st else 0) =
          (fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ T)
            (Classical.propDecidable _) (FullNext out st) 0) := by
        funext out st
        by_cases ht : (∑ g : BG,(out.2 g).2.card) ≤ T
        · simp only [if_pos ht]
        · simp only [if_neg ht]
      have hFrameMask :
          (fun (out : FullPhysicalOutput SP sm BP bm (J+ell)) st =>
            if (∑ g : BG,(out.2 g).2.card) ≤ T then FrameNext out st else 0) =
          (fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ T)
            (Classical.propDecidable _) (FrameNext out st) 0) := by
        funext out st
        by_cases ht : (∑ g : BG,(out.2 g).2.card) ≤ T
        · simp only [if_pos ht]
        · simp only [if_neg ht]
      rw [←hFullMask] at hd
      rw [←hFrameMask] at hc
      by_cases ht : (∑ g : BG,(yg.2 g).2.card) ≤ T
      · simp only [if_pos ht] at hd hc ⊢
        exact (congrArg₂ (·+·) hd (hc.trans hr))
      · simp only [if_neg ht] at hd hc ⊢
        have hZero := (congrArg₂ (·+·) hd (hc.trans hr))
        simpa only [zero_add] using hZero
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalDirtyRoot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

def sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        sourceOriginalOLDProjectedDirtyPhysicalInsertionGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T N 0
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)



/-- Exact full source PEP-PCLEANP discrepancy as the chronological
insertion of the genuine local physical marked P(E-CLEAN)P residual.
The signed original terminal observable, source baseline, Fock orbit
mass and both vacuum boundaries are unmodified. This is an IDENTITY,
not yet the global L2 saving for its insertion sum. -/
theorem source_original_MEMORY_PEP_PCLEAN_physical_DIRTY_root434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hd : MemorySourceDomain SP sm BP bm cap q rho Vs V k R) :
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T -
    sourceOriginalOLDProjectedCleanMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T := by
  rw [source_original_MEMORY_PEP_PCLEAN_root_telescoping434
    SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T hd]
  unfold sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434
    sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : physicalVacuum SP sm BP bm J ell y=0
  · simp only [hv,star_zero,mul_zero,zero_mul]
  · by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
    · simp only [if_pos hn]
      rw [source_original_ACTUAL_DIRTY_insertion_physical_exact434
        SP sm BP bm J ell m cap patterns hd.big_injective hd.cap_saturated
        q rho Vs V (physicalSourceMuTilde BP bm q (2*R) V) hd.Vsmall_pos
        (source_original_SOURCE_tilt_positive434 BP bm q hd.q_pos.le (2*R) V
          hd.Vbig_pos hd.big_above_visits)
        K zeta theta k (2*R) T
        (fun out _ => physicalVacuum SP sm BP bm J ell out)
        (2*R) 0 y _
        (source_original_MEMORY_initial_reachable434 SP sm BP bm J ell y hv hn)]
    · simp only [if_neg hn]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalHistorySup -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 14000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The actual numerical-history carrier is never empty because it
contains the empty history, including for empty BIG prime families. -/
theorem source_original_ACTUAL_history_pool_nonempty434 :
    (sourceOriginalMemoryBirthPool434 BP bm).powerset.Nonempty := by
  refine ⟨∅,?_⟩
  exact Finset.mem_powerset.mpr (Finset.empty_subset _)

/-- The exact maximum over the REAL chronological birth-history
carrier, not a sum of the number of histories. No hypothesized envelope. -/
def sourceOriginalActualHistorySupNorm434
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (Y : FullPhysicalOutput SP sm BP bm (J+ell)) : ℝ :=
  ((sourceOriginalMemoryBirthPool434 BP bm).powerset).sup'
    (source_original_ACTUAL_history_pool_nonempty434 BP bm)
    (fun seen => ‖F Y seen‖)

theorem source_original_ACTUAL_history_sup_nonneg434
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (Y : FullPhysicalOutput SP sm BP bm (J+ell)) :
    0 ≤ sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F Y := by
  unfold sourceOriginalActualHistorySupNorm434
  exact (norm_nonneg (F Y ∅)).trans
    (Finset.le_sup' (fun seen => ‖F Y seen‖)
      (Finset.mem_powerset.mpr (Finset.empty_subset _)))

theorem source_original_ACTUAL_history_sup_dominates434
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (Y : FullPhysicalOutput SP sm BP bm (J+ell))
    (seen : Finset ℕ)
    (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    ‖F Y seen‖ ≤ sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F Y := by
  unfold sourceOriginalActualHistorySupNorm434
  exact Finset.le_sup' (fun seen => ‖F Y seen‖) hseen

/-- The maximum is the LEAST real bound for all genuine histories.
This exact equivalence prevents hiding a factor |History| in its cost. -/
theorem source_original_ACTUAL_history_sup_le_iff434
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (Y : FullPhysicalOutput SP sm BP bm (J+ell)) (B : ℝ) :
    sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F Y ≤ B ↔
    ∀ seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset, ‖F Y seen‖ ≤ B := by
  constructor
  · intro h seen hs
    exact (source_original_ACTUAL_history_sup_dominates434 SP sm BP bm J ell F Y seen hs).trans h
  · intro h
    unfold sourceOriginalActualHistorySupNorm434
    apply Finset.sup'_le
    intro seen hs
    exact h seen hs

/-- A real-valued complex test whose NORM is precisely the maximum
physical history norm. It incurs NO history-cardinality factor. -/
def sourceOriginalActualHistoryComplexEnvelope434
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (Y : FullPhysicalOutput SP sm BP bm (J+ell)) : ℂ :=
  ((sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F Y):ℂ)

theorem source_original_ACTUAL_history_complex_envelope_norm434
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (Y : FullPhysicalOutput SP sm BP bm (J+ell)) :
    ‖sourceOriginalActualHistoryComplexEnvelope434 SP sm BP bm J ell F Y‖ =
      sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F Y := by
  unfold sourceOriginalActualHistoryComplexEnvelope434
  rw [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (source_original_ACTUAL_history_sup_nonneg434 SP sm BP bm J ell F Y)]

/-- An actual full-chain continuation automatically meets the
history-UNIFORM target-envelope condition required by projected DIRTY. -/
theorem source_original_ACTUAL_history_complex_envelope_dominates434
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (Y : FullPhysicalOutput SP sm BP bm (J+ell))
    (seen : Finset ℕ)
    (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    ‖F Y seen‖ ≤
      ‖sourceOriginalActualHistoryComplexEnvelope434 SP sm BP bm J ell F Y‖ := by
  rw [source_original_ACTUAL_history_complex_envelope_norm434]
  exact source_original_ACTUAL_history_sup_dominates434 SP sm BP bm J ell F Y seen hseen
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualRhoOneBigRow -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)

/-- The actual fixed-store/fixed-promotion row at rho=1.
All target integrations and legal OLD injections are retained. The
explicit OLD cost is polynomial of degree d, not free rho damping. -/
theorem source_original_ACTUAL_BIG_rho_one_retrieval434
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V R : ℝ)
    (hV : 0 < V) (hR : 1 ≤ R) (hMass : ∑ p : P,mu p ≤ R)
    (x : BigState modulus M B) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (S A : Finset (Fin M)) (hA : A ⊆ orientedUnshared M shared)
    (d : ℕ) (hd : (orientedUnshared M shared).card ≤ d) :
    (∑ f : ↥A ↪ Fin x.2.1.val,∑ t : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step (S,⟨A,f⟩)
      then ‖orientedBigBranchCoefficient modulus M B mu V 1 x t shared
        sigma tau step (S,⟨A,f⟩)‖ else 0) ≤
      (max 1 (x.2.1.val:ℝ))^d * ((max 1 V⁻¹)^d*R^d) := by
  classical
  have ha : A.card ≤ d := (Finset.card_le_card hA).trans hd
  have hv : (V^A.card)⁻¹ ≤ (max 1 V⁻¹)^d := by
    rw [← inv_pow]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr hV.le) (le_max_right _ _) _).trans
      (pow_right_mono₀ (le_max_left _ _) ha)
  have hcard : Fintype.card (↥A ↪ Fin x.2.1.val) ≤ x.2.1.val^A.card := by
    calc
      _ ≤ Fintype.card (↥A → Fin x.2.1.val) :=
        Fintype.card_le_of_injective (fun f => f.toFun) (by
          intro f g h
          exact Function.Embedding.ext (fun a => congrFun h a))
      _ = _ := by simp
  have hc : (Fintype.card (↥A ↪ Fin x.2.1.val):ℝ) ≤ (max 1 (x.2.1.val:ℝ))^d := by
    calc
      _ ≤ (x.2.1.val:ℝ)^A.card := by exact_mod_cast hcard
      _ ≤ (max 1 (x.2.1.val:ℝ))^A.card :=
        pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
      _ ≤ _ := pow_right_mono₀ (le_max_left _ _) ha
  let C := (max 1 V⁻¹)^d*R^d
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
      (pow_nonneg (le_trans zero_le_one hR) _)
  have he (f : ↥A ↪ Fin x.2.1.val) :
      (∑ t : Fin M → P,
        if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step (S,⟨A,f⟩)
        then ‖orientedBigBranchCoefficient modulus M B mu V 1 x t shared
          sigma tau step (S,⟨A,f⟩)‖ else 0) ≤ C := by
    have hh := source_original_memory_BIG_fixed_choice_target_cap434 modulus M B mu
      hmu V 1 R hV (by norm_num) hR hMass x shared sigma tau D step (S,⟨A,f⟩) hA d hd
    simp only [one_pow,one_div] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hv
      (pow_nonneg (le_trans zero_le_one hR) _))
  calc
    _ ≤ ∑ f : ↥A ↪ Fin x.2.1.val,C := Finset.sum_le_sum (fun f _ => he f)
    _ = (Fintype.card (↥A ↪ Fin x.2.1.val):ℝ)*C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hC

/-- The complete literal absolute BIG row, including all targets, stores,
promotion subsets and ordered OLD injections. The explicit bound pays the OLD length; it is independent
of the active slot count, residue step and cutoff. -/
theorem source_original_ACTUAL_BIG_rho_one_row434
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V R : ℝ)
    (hV : 0<V)
    (hR : 1 ≤ R) (hMass : ∑ p : P,mu p ≤ R)
    (x : BigState modulus M B) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (d : ℕ) (hd : (orientedUnshared M shared).card ≤ d) :
    (∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c
      then ‖orientedBigBranchCoefficient modulus M B mu V 1 x t shared
        sigma tau step c‖ else 0) ≤
      (4:ℝ)^d * ((max 1 (x.2.1.val:ℝ))^d *
        ((max 1 V⁻¹)^d*R^d)) := by
  classical
  let U := orientedUnshared M shared
  let row := fun S A : Finset (Fin M) =>
    ∑ f : ↥A ↪ Fin x.2.1.val,∑ t : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step (S,⟨A,f⟩)
      then ‖orientedBigBranchCoefficient modulus M B mu V 1 x t shared
        sigma tau step (S,⟨A,f⟩)‖ else 0
  let C := (max 1 (x.2.1.val:ℝ))^d * ((max 1 V⁻¹)^d*R^d)
  have hC : 0 ≤ C := by
    have hmem : 0 ≤ (max 1 (x.2.1.val:ℝ))^d :=
      pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
    exact mul_nonneg hmem (mul_nonneg
      (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
      (pow_nonneg (le_trans zero_le_one hR) _))
  have hrow (S A : Finset (Fin M)) (hA : A ⊆ U) : row S A ≤ C :=
    source_original_ACTUAL_BIG_rho_one_retrieval434 modulus M B mu hmu
      V R hV hR hMass x shared sigma tau D step S A hA d hd
  have hzero (S A : Finset (Fin M)) (hbad : ¬ S ⊆ U ∨ ¬ A ⊆ U) :
      row S A=0 := by
    apply Finset.sum_eq_zero
    intro f hf
    apply Finset.sum_eq_zero
    intro t ht
    apply if_neg
    intro hlegal
    rcases hbad with hS | hA
    · exact hS hlegal.stores_unshared
    · exact hA hlegal.promotes_unshared
  have hdecomp :
      (∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,
        if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c
        then ‖orientedBigBranchCoefficient modulus M B mu V 1 x t shared
          sigma tau step c‖ else 0) =
      ∑ S : Finset (Fin M),∑ A : Finset (Fin M),row S A := by
    simp only [BigEdgeChoice,Fintype.sum_prod_type,Fintype.sum_sigma,row]
  rw [hdecomp]
  calc
    _ = ∑ S ∈ U.powerset,∑ A : Finset (Fin M),row S A := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S hS hnot
      apply Finset.sum_eq_zero
      intro A hA
      exact hzero S A (Or.inl (by simpa only [Finset.mem_powerset] using hnot))
    _ = ∑ S ∈ U.powerset,∑ A ∈ U.powerset,row S A := by
      apply Finset.sum_congr rfl
      intro S hS
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro A hA hnot
      exact hzero S A (Or.inr (by simpa only [Finset.mem_powerset] using hnot))
    _ ≤ ∑ S ∈ U.powerset,∑ A ∈ U.powerset,C := by
      apply Finset.sum_le_sum
      intro S hS
      exact Finset.sum_le_sum (fun A hA => hrow S A (Finset.mem_powerset.mp hA))
    _ = (4:ℝ)^U.card*C := by
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_powerset,
        Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)=2*2 by norm_num,mul_pow]
      ring
    _ ≤ (4:ℝ)^d*C :=
      mul_le_mul_of_nonneg_right (pow_right_mono₀ (by norm_num) hd) hC
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualRhoOneBigFrame -/

section

open scoped BigOperators Classical
noncomputable section
open Filter
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
variable (M : ℕ) (cap : G → ℕ) (x : BigGroupState BP modulus M cap)

/-- Tensor the complete actual BIG rows, preserving each ordered target
and memory choice. No count of active/shared slots is paid. -/
theorem source_original_ACTUAL_BIG_rho_one_frame434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (V : G → ℝ) (R : ℝ) (hV : ∀ g,0<V g)
    (hR : 1 ≤ R)
    (hMass : ∀ g,(∑ p : BP g,mu g p) ≤ R)
    (shared : G → Finset (Fin M)) (sigma tau : BigGroupPerm (BG:=G) M)
    (D : ℕ) (step : ℤ) (d : ℕ)
    (hd : ∀ g,(orientedUnshared M (shared g)).card ≤ d) :
    (∑ b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x,
      if sourceOriginalMemoryBigFrameLegal434 BP modulus M cap x shared sigma tau D step b
      then sourceOriginalMemoryBigFrameNorm434 BP modulus M cap x mu V 1
        shared sigma tau step b else 0) ≤
      ∏ g : G,(4:ℝ)^d*((max 1 ((x g).2.1.val:ℝ))^d*((max 1 (V g)⁻¹)^d*R^d)) := by
  classical
  let w := fun (g : G) (z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) (x g)) =>
    if OrientedBigEdgeLegal (modulus g) M (cap g) (x g) z.1
      (shared g) (sigma g) (tau g) D step z.2 then
      ‖orientedBigBranchCoefficient (modulus g) M (cap g) (mu g) (V g) 1
        (x g) z.1 (shared g) (sigma g) (tau g) step z.2‖ else 0
  have hprod (b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x) :
      (∏ g : G,w g (b g)) =
      if sourceOriginalMemoryBigFrameLegal434 BP modulus M cap x shared sigma tau D step b
      then sourceOriginalMemoryBigFrameNorm434 BP modulus M cap x mu V 1
        shared sigma tau step b else 0 := by
    simp only [w,Finset.prod_ite_zero,Finset.mem_univ,forall_const,
      sourceOriginalMemoryBigFrameLegal434,sourceOriginalMemoryBigFrameNorm434]
    congr <;> exact Subsingleton.elim _ _
  have he :
      (∑ b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x,
        ∏ g : G,w g (b g)) =
      ∏ g : G,∑ z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) (x g),w g z := by
    convert (Fintype.prod_sum w).symm using 1 <;> congr <;> exact Subsingleton.elim _ _
  simp_rw [← hprod]
  rw [he]
  apply Finset.prod_le_prod₀
  · intro g hg
    apply Finset.sum_nonneg
    intro z hz
    dsimp only [w]
    split_ifs <;> positivity
  · intro g hg
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    exact source_original_ACTUAL_BIG_rho_one_row434 (modulus g) M (cap g)
      (mu g) (hmu g) (V g) R (hV g) hR (hMass g)
      (x g) (shared g) (sigma g) (tau g) D step d (hd g)


/-- The numerical prime box controls alphabet size uniformly. Only
injectivity and positive integral labels are used. -/
theorem source_original_ACTUAL_numeric_alphabet_box434
    {P : Type} [Fintype P] (b : P → ℕ) [∀ p,NeZero (b p)]
    (hi : Function.Injective b) (X : ℝ) (hX : 1 ≤ X)
    (hmax : ∀ p,(b p:ℝ) ≤ X) :
    (Fintype.card P:ℝ) ≤ 2*X := by
  let f : P → Fin (Nat.ceil X) := fun p =>
    ⟨b p-1,by
      have hp := NeZero.pos (b p)
      have hb : b p ≤ Nat.ceil X := by
        exact_mod_cast (hmax p).trans (Nat.le_ceil X)
      omega⟩
  have hf : Function.Injective f := by
    intro p r h
    apply hi
    have hh := congrArg Fin.val h
    change b p-1=b r-1 at hh
    have hp := NeZero.pos (b p)
    have hr := NeZero.pos (b r)
    omega
  have hc : Fintype.card P ≤ Nat.ceil X := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hcR : (Fintype.card P:ℝ) ≤ (Nat.ceil X:ℝ) := by exact_mod_cast hc
  have hCeil := Nat.ceil_lt_add_one (zero_le_one.trans hX)
  linarith

/-- A concrete source-box estimate for the full BIG E frame at rho=1
with source-saturated caps card(BP g). The threshold precedes all moving
groups, alphabets, slots, patterns, physical states and signed steps.
No OLD-smallness, row-norm or cancellation premise occurs. -/
theorem eventually_source_original_ACTUAL_BIG_rho_one_source_box434
    (c vmin : ℝ) (hc : 0 < c) (hv : 0 < vmin) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (hi : ∀ g,Function.Injective (bm g))
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
      (V : G → ℝ) (hV : ∀ g,vmin ≤ V g)
      (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
      (hmin : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (hmax : ∀ g p,(bm g p:ℝ) ≤ Real.exp (Real.sqrt L))
      (J ell m : ℕ) (pat : SourcePattern G J m)
      (x : BigGroupState BP bm (J+ell) (fun g => Fintype.card (BP g)))
      (sigma tau : BigGroupPerm (BG:=G) (J+ell)) (D : ℕ) (step : ℤ),
      (∑ b : sourceOriginalMemoryBigFrameChoice434 BP bm (J+ell)
          (fun g => Fintype.card (BP g)) x,
        if sourceOriginalMemoryBigFrameLegal434 BP bm (J+ell)
          (fun g => Fintype.card (BP g)) x (sourceBigShared J ell m pat)
          sigma tau D step b
        then sourceOriginalMemoryBigFrameNorm434 BP bm (J+ell)
          (fun g => Fintype.card (BP g)) x
          (physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V)
          V 1 (sourceBigShared J ell m pat) sigma tau step b else 0) ≤
      (16*max 1 vmin⁻¹*Real.exp (Real.sqrt L))^((ell+m)*Fintype.card G) := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc] with L hL
  intro G _ _ BP _ _ bm _ hi q hq hq1 V hV hHarmonic hmin hmax J ell m pat x
    sigma tau D step
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP bm q N V
  have hVp (g : G) : 0 < V g := hv.trans_le (hV g)
  have hb (g : G) (p : BP g) : (1:ℝ)/2 ≤ physicalSourceBaseline BP bm q N g p :=
    (source_original_B26_physical_baseline_half434 BP bm q hq hq1 N g p
      (hL (bm g p) (hmin g p))).1
  have hmuMass (g : G) := source_original_memory_physical_tilt_mass_two434
    BP bm q N V g (hVp g) (hHarmonic g) (hb g)
  let E := Real.exp (Real.sqrt L)
  let A := max 1 vmin⁻¹
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (Real.sqrt_nonneg L)
  have hA : 1 ≤ A := le_max_left _ _
  have hn (g : G) : max 1 ((x g).2.1.val:ℝ) ≤ 2*E := by
    have hh := source_original_ACTUAL_numeric_alphabet_box434 (bm g) (hi g) E hE (hmax g)
    have hn : (x g).2.1.val ≤ Fintype.card (BP g) := Nat.le_of_lt_succ (x g).2.1.isLt
    have hnR : ((x g).2.1.val:ℝ) ≤ (Fintype.card (BP g):ℝ) := by exact_mod_cast hn
    exact max_le (by linarith) (hnR.trans hh)
  have hInv (g : G) : max 1 (V g)⁻¹ ≤ A := by
    exact max_le_max le_rfl (by
      simpa only [one_div] using one_div_le_one_div_of_le hv (hV g))
  have hf := source_original_ACTUAL_BIG_rho_one_frame434 BP bm (J+ell)
    (fun g => Fintype.card (BP g)) x mu (fun g => (hmuMass g).1)
    V 2 hVp (by norm_num) (fun g => (hmuMass g).2)
    (sourceBigShared J ell m pat) sigma tau D step (ell+m)
    (memory_source_unshared_count J ell m pat)
  apply hf.trans
  calc
    _ ≤ ∏ _g : G,(16*A*E)^(ell+m) := by
      apply Finset.prod_le_prod₀
      · intro g hg
        positivity
      · intro g hg
        have hb : 8*max 1 ((x g).2.1.val:ℝ)*max 1 (V g)⁻¹ ≤ 16*A*E := by
          have hh := mul_le_mul (hn g) (hInv g)
            (le_trans zero_le_one (le_max_left _ _)) (by positivity)
          nlinarith only [hh]
        calc
          _ = (8*max 1 ((x g).2.1.val:ℝ)*max 1 (V g)⁻¹)^(ell+m) := by
            rw [show (8:ℝ)=4*2 by norm_num]
            simp only [mul_pow]
            ring
          _ ≤ _ := pow_le_pow_left₀ (by positivity) hb _
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,←pow_mul];rfl
end Green64Analytic.CorrelationSquare

end

end

