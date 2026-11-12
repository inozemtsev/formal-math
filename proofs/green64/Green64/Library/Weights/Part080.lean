module

public import Green64.Library.Weights.Part078
public import Green64.Library.Weights.Part003
public import Green64.Library.Correlation.Part049
public import Green64.Library.Correlation.Part028
public import Green64.Library.Weights.Part054
public import Green64.Library.Correlation.Part048

@[expose] public section

/-!
# Weights / Part080

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMarkedCleanLiteralRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 900000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap sizes : BG → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

local notation "Small" => GroupState SP sm (J+ell)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bm sizes prime
local notation "Frame" => SourceOriginalB26FrozenFrame434 BP J ell m patterns
local notation "SPerm" => GroupPermFamily (G := SG) (J+ell)
local notation "Out" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- One exhaustive literal CLEAN term, retaining the actual birth LIST,
the original joint K, phase, OLD translation, and original target test. -/
def sourceOriginalMarkedCleanIndexedTerm434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (xs ys : Small) (a b : A) (t : Old) (S : Finset ℕ)
    (h : Frame) (ss tt : SPerm) : ℂ :=
  let births := sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m
    (patterns h.1) (fun g i => b g (h.2.2.2 g i))
  let dsmall := sourceOriginalB26SmallSourceD434 SP sm J ell xs ss
  let D := sourceOriginalB26FrozenD434 BP bm J ell m dsmall
    (patterns h.1) h.2.1 a h.2.2.1
  let step := o*k*(D:ℤ)
  if births.Nodup ∧ Disjoint S births.toFinset then
    (sourceOriginalB26FrozenPhysicalWeight434 SP sm BP bm J ell m
      cap sizes hsizes prime patterns mu Vb K dsmall zeta theta o k a (0,t) h b *
      (groupPermutationPairMass (G := SG) (J+ell):ℂ) *
      groupPermutedKernel SP sm (J+ell) q Vs (sourceSmallShared J ell)
        step (fun _ _ => 1) ss tt xs ys) *
    sourceOriginalB26TargetPullback434 SP sm BP bm J ell cap sizes hsizes prime
      (fun Y => F Y (S ∪ births.toFinset)) ys b
      (fun g i => t g i+(step : ZMod (bm g (prime g i))))
  else 0

/-- Exact ORIGINAL marked CLEAN row, for the entire actual pattern family.
This is the original source witness sum, not an independently resampled
kernel. It has no boundedness assumption on its arbitrary complex future. -/
theorem source_original_MARKED_CLEAN_full_literal_row434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (xs : Small) (a : A) (t : Old) (S : Finset ℕ) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q 1 Vs Vb mu K zeta theta o k
      (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap sizes hsizes prime a t) S F =
    ∑ h : Frame,∑ b : A,∑ ys : Small,∑ ss : SPerm,∑ tt : SPerm,
      sourceOriginalMarkedCleanIndexedTerm434 SP sm BP bm J ell m cap sizes hsizes prime
        patterns mu Vb K q Vs zeta theta o k F xs ys a b t S h ss tt := by
  let x := (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap sizes hsizes prime a t)
  let H := fun z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x =>
    if orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns S z then
      (if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z
       then sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
         q 1 Vs Vb mu K zeta theta o k x z else 0) *
      F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
        (S ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset)
    else 0
  have he := source_original_B26_CLEAN_CHOICES_EXHAUSTIVE434 SP sm BP bm
    J ell m cap sizes hsizes prime patterns xs a t H
  calc
    _ = ∑ z,if memorySourceCleanChoice SP sm BP bm J ell m cap patterns x z then H z else 0 := by
      unfold sourceOriginalMemoryMarkedFilteredE434
      apply Finset.sum_congr rfl
      intro z hz
      rw [source_original_MARKED_CLEAN_predicate434]
      by_cases hl : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z
      <;> by_cases hc : memorySourceCleanChoice SP sm BP bm J ell m cap patterns x z
      <;> by_cases hb : orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns S z
      <;> dsimp only [x] at hl hc
      <;> simp only [H,x,hl,hc,hb,and_true,and_false,true_and,false_and,
        ite_true,ite_false,zero_mul]
    _ = _ := by
      rw [he]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro ys hys
      apply Finset.sum_congr rfl
      intro ss hss
      apply Finset.sum_congr rfl
      intro tt htt
      dsimp only [H]
      unfold orientedEFreshBatchEligible
      rw [source_original_MARKED_CLEAN_births_literal434 SP sm BP bm
        J ell m cap sizes hsizes prime patterns xs ys a b t h ss tt]
      unfold sourceOriginalMarkedCleanIndexedTerm434
      dsimp only
      by_cases hf :
          (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m (patterns h.1)
            (fun g i => b g (h.2.2.2 g i))).Nodup ∧
          Disjoint S (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m (patterns h.1)
            (fun g i => b g (h.2.2.2 g i))).toFinset
      · simp only [if_pos hf]
        rw [source_original_B26_FROZEN_ORIGINAL_CLEAN_SUMMAND434 SP sm BP bm
          J ell m cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
          xs ys a (0,t) h b ss tt]
        rw [source_original_B26_CLEAN_LITERAL_OUTPUT434 SP sm BP bm
          J ell m cap sizes hsizes prime patterns
          (fun Y => F Y (S ∪ (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m
            (patterns h.1) (fun g i => b g (h.2.2.2 g i))).toFinset))
          xs ys a b t h ss tt o k]
        have hd := source_original_B26_FROZEN_D_from_original434 SP sm BP bm
          J ell m cap sizes hsizes prime xs a (0,t) (patterns h.1) h.2.1 h.2.2.1 ss
        dsimp only [sourceOrientedStep]
        rw [hd]
        rfl
      · simp only [if_neg hf]

end Green64Analytic.CorrelationSquare

end

end

/-! ## MarkedCleanChronologicalTarget -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare

open Green64FullPhysicalE Green64SmallHaar

set_option autoImplicit false
set_option maxHeartbeats 900000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap sizes : BG → ℕ) (hsizes : ∀ g, sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

local notation "Small" => GroupState SP sm (J + ell)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bm sizes prime
local notation "Frame" => SourceOriginalB26FrozenFrame434 BP J ell m patterns
local notation "SPerm" => GroupPermFamily (G := SG) (J + ell)
local notation "Out" => FullPhysicalOutput SP sm BP bm (J + ell)

/-- The literal marked CLEAN term indexed at its target chronological state.
Every physical factor is copied verbatim from
`sourceOriginalMarkedCleanIndexedTerm434`.  The only change is that the future
reads the updated seen set through the exact list-retaining B369 equivalence. -/
def sourceOriginalMarkedCleanIndexedTargetTerm434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (xs ys : Small) (a b : A) (t : Old) (S : Finset ℕ)
    (h : Frame) (ss tt : SPerm) : ℂ :=
  let births := sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m
    (patterns h.1) (fun g i => b g (h.2.2.2 g i))
  let dsmall := sourceOriginalB26SmallSourceD434 SP sm J ell xs ss
  let D := sourceOriginalB26FrozenD434 BP bm J ell m dsmall
    (patterns h.1) h.2.1 a h.2.2.1
  let step := o * k * (D : ℤ)
  if hlegal : births.Nodup ∧ Disjoint S births.toFinset then
    let chronological : SourceChronologicalSeenBirthList434 ℕ :=
      ⟨(S, births), hlegal⟩
    (sourceOriginalB26FrozenPhysicalWeight434 SP sm BP bm J ell m
      cap sizes hsizes prime patterns mu Vb K dsmall zeta theta o k a (0, t) h b *
      (groupPermutationPairMass (G := SG) (J + ell) : ℂ) *
      groupPermutedKernel SP sm (J + ell) q Vs (sourceSmallShared J ell)
        step (fun _ _ => 1) ss tt xs ys) *
    sourceOriginalB26TargetPullback434 SP sm BP bm J ell cap sizes hsizes prime
      (fun Y => F Y
        (sourceChronologicalSeenBirthListEquiv434 ℕ chronological).1.1)
      ys b (fun g i => t g i + (step : ZMod (bm g (prime g i))))
  else 0

/-- Exact source-consumer binding: the original marked term and the target
chronological reindexing are definitionally the same complex coefficient.
In particular K, source-dependent D, both endpoint permutation families,
SMALL Haar, OLD translation and target pullback stay inside the term before
any absolute value or square. -/
theorem source_original_MARKED_CLEAN_indexed_chronological_target434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (xs ys : Small) (a b : A) (t : Old) (S : Finset ℕ)
    (h : Frame) (ss tt : SPerm) :
    sourceOriginalMarkedCleanIndexedTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
        F xs ys a b t S h ss tt =
      sourceOriginalMarkedCleanIndexedTargetTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
        F xs ys a b t S h ss tt := by
  unfold sourceOriginalMarkedCleanIndexedTerm434
  unfold sourceOriginalMarkedCleanIndexedTargetTerm434
  dsimp only
  by_cases hlegal :
      (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m
        (patterns h.1) (fun g i => b g (h.2.2.2 g i))).Nodup ∧
      Disjoint S
        (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m
          (patterns h.1) (fun g i => b g (h.2.2.2 g i))).toFinset
  · rw [if_pos hlegal, dif_pos hlegal]
    rfl
  · rw [if_neg hlegal, dif_neg hlegal]

end Green64Analytic.CorrelationSquare

end

end

/-! ## MarkedCleanFullChronologicalTarget -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare

open Green64FullPhysicalE Green64SmallHaar

set_option autoImplicit false
set_option maxHeartbeats 900000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap sizes : BG → ℕ) (hsizes : ∀ g, sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

local notation "Small" => GroupState SP sm (J + ell)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bm sizes prime
local notation "Frame" => SourceOriginalB26FrozenFrame434 BP J ell m patterns
local notation "SPerm" => GroupPermFamily (G := SG) (J + ell)
local notation "Out" => FullPhysicalOutput SP sm BP bm (J + ell)

/-- Full literal original marked CLEAN row, now indexed by the exact target
chronological carrier of B369.  This is an equality for the complete pattern,
target, SMALL and two-permutation sums, not a per-term conditional interface. -/
theorem source_original_MARKED_CLEAN_full_chronological_target434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (xs : Small) (a : A) (t : Old) (S : Finset ℕ) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q 1 Vs Vb mu K zeta theta o k
      (xs, sourceOriginalB26FrozenBigState434 BP bm J ell cap sizes hsizes prime a t)
      S F =
    ∑ h : Frame, ∑ b : A, ∑ ys : Small, ∑ ss : SPerm, ∑ tt : SPerm,
      sourceOriginalMarkedCleanIndexedTargetTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
        F xs ys a b t S h ss tt := by
  rw [source_original_MARKED_CLEAN_full_literal_row434 SP sm BP bm
    J ell m cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
    F xs a t S]
  simp_rw [source_original_MARKED_CLEAN_indexed_chronological_target434]

end Green64Analytic.CorrelationSquare

end

end

/-! ## MarkedCleanOrbitChronological -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare

open Green64FullPhysicalE Green64SmallHaar

set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap sizes : BG → ℕ) (hsizes : ∀ g, sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

local notation "Small" => GroupState SP sm (J + ell)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bm sizes prime
local notation "Frame" => SourceOriginalB26FrozenFrame434 BP J ell m patterns
local notation "SPerm" => GroupPermFamily (G := SG) (J + ell)
local notation "Out" => FullPhysicalOutput SP sm BP bm (J + ell)

/-- The genuine weighted physical Fock orbit of the literal marked CLEAN row
is exactly the complete chronological target sum at any reachable frozen OLD
representative.  The orbit theorem pays physical orbit mass once; B371 then
exposes all frames and targets without a representative-count factor. -/
theorem source_original_MARKED_CLEAN_orbit_chronological_target434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (hVs : ∀ g, 0 < Vs g)
    (hmu : ∀ g p, 0 < mu g p)
    (F : Out → Finset ℕ → ℂ)
    (xs : Small) (a : A) (t : Old) (S : Finset ℕ)
    (hr : sourceOriginalPhysicalReachable434 SP sm BP bm (J + ell)
      (physicalFockProjection SP sm BP bm (J + ell) cap
        (xs, sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t)) S) :
    fullPhysicalOrbitAverage SP sm BP bm (J + ell) cap Vs mu
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
        J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q 1 Vs Vb mu K zeta theta o k st S F)
      (physicalFockProjection SP sm BP bm (J + ell) cap
        (xs, sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t)) =
    ∑ h : Frame, ∑ b : A, ∑ ys : Small, ∑ ss : SPerm, ∑ tt : SPerm,
      sourceOriginalMarkedCleanIndexedTargetTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
        F xs ys a b t S h ss tt := by
  let x : FullPhysicalState SP sm BP bm (J + ell) cap :=
    (xs, sourceOriginalB26FrozenBigState434 BP bm J ell cap
      sizes hsizes prime a t)
  calc
    _ = sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q 1 Vs Vb mu K zeta theta o k x S F :=
      source_original_SOURCE_MARKED_CLEAN_E_orbit_representative434
        SP sm BP bm J ell m cap patterns x S hr q 1 Vs Vb mu hVs hmu
        K zeta theta o k F
    _ = _ := source_original_MARKED_CLEAN_full_chronological_target434
      SP sm BP bm J ell m cap sizes hsizes prime patterns
      mu Vb K q Vs zeta theta o k F xs a t S

/-- Exact squared-norm consumer form of the preceding identity.  This is not
an application of Cauchy--Schwarz: the complete signed physical orbit row is
first identified with the chronological target sum, and only then is the
common complex value squared. -/
theorem source_original_MARKED_CLEAN_orbit_chronological_norm_sq434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (hVs : ∀ g, 0 < Vs g)
    (hmu : ∀ g p, 0 < mu g p)
    (F : Out → Finset ℕ → ℂ)
    (xs : Small) (a : A) (t : Old) (S : Finset ℕ)
    (hr : sourceOriginalPhysicalReachable434 SP sm BP bm (J + ell)
      (physicalFockProjection SP sm BP bm (J + ell) cap
        (xs, sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t)) S) :
    ‖fullPhysicalOrbitAverage SP sm BP bm (J + ell) cap Vs mu
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
        J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q 1 Vs Vb mu K zeta theta o k st S F)
      (physicalFockProjection SP sm BP bm (J + ell) cap
        (xs, sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t))‖ ^ 2 =
    ‖∑ h : Frame, ∑ b : A, ∑ ys : Small, ∑ ss : SPerm, ∑ tt : SPerm,
      sourceOriginalMarkedCleanIndexedTargetTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
        F xs ys a b t S h ss tt‖ ^ 2 := by
  rw [source_original_MARKED_CLEAN_orbit_chronological_target434
    SP sm BP bm J ell m cap sizes hsizes prime patterns
    mu Vb K q Vs zeta theta o k hVs hmu F xs a t S hr]

end Green64Analytic.CorrelationSquare

end

end

/-! ## MarkedCleanCollisionRow -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap sizes : BG → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

local notation "Small" => GroupState SP sm (J+ell)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bm sizes prime
local notation "Frame" => SourceOriginalB26FrozenFrame434 BP J ell m patterns
local notation "SPerm" => GroupPermFamily (G := SG) (J+ell)
local notation "Out" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- The literal marked chronological term with only the B26
auxiliary/active ban removed.  The global birth-list and seen gates remain
outside exactly as in the source term. -/
def sourceOriginalMarkedUnbannedCleanIndexedTerm434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (xs ys : Small) (a b : A) (t : Old) (S : Finset ℕ)
    (h : Frame) (ss tt : SPerm) : ℂ :=
  let births := sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m
    (patterns h.1) (fun g i => b g (h.2.2.2 g i))
  let dsmall := sourceOriginalB26SmallSourceD434 SP sm J ell xs ss
  let D := sourceOriginalB26FrozenD434 BP bm J ell m dsmall
    (patterns h.1) h.2.1 a h.2.2.1
  let step := o*k*(D:ℤ)
  if births.Nodup ∧ Disjoint S births.toFinset then
    (sourceOriginalB26FrozenUnbannedPhysicalWeight434 BP bm J ell m patterns SP sm cap sizes hsizes prime mu Vb K dsmall zeta theta o k a (0,t) h b *
      (groupPermutationPairMass (G := SG) (J+ell):ℂ) *
      groupPermutedKernel SP sm (J+ell) q Vs (sourceSmallShared J ell)
        step (fun _ _ => 1) ss tt xs ys) *
    sourceOriginalB26TargetPullback434 SP sm BP bm J ell cap sizes hsizes prime
      (fun Y => F Y (S ∪ births.toFinset)) ys b
      (fun g i => t g i+(step : ZMod (bm g (prime g i))))
  else 0

/-- The same literal marked term restricted to the genuine auxiliary/active
collision event. -/
def sourceOriginalMarkedAuxCollisionIndexedTerm434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (xs ys : Small) (a b : A) (t : Old) (S : Finset ℕ)
    (h : Frame) (ss tt : SPerm) : ℂ :=
  let births := sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m
    (patterns h.1) (fun g i => b g (h.2.2.2 g i))
  let dsmall := sourceOriginalB26SmallSourceD434 SP sm J ell xs ss
  let D := sourceOriginalB26FrozenD434 BP bm J ell m dsmall
    (patterns h.1) h.2.1 a h.2.2.1
  let step := o*k*(D:ℤ)
  if births.Nodup ∧ Disjoint S births.toFinset then
    (sourceOriginalB26FrozenAuxCollisionPhysicalWeight434 BP bm J ell m patterns SP sm cap sizes hsizes prime mu Vb K dsmall zeta theta o k a (0,t) h b *
      (groupPermutationPairMass (G := SG) (J+ell):ℂ) *
      groupPermutedKernel SP sm (J+ell) q Vs (sourceSmallShared J ell)
        step (fun _ _ => 1) ss tt xs ys) *
    sourceOriginalB26TargetPullback434 SP sm BP bm J ell cap sizes hsizes prime
      (fun Y => F Y (S ∪ births.toFinset)) ys b
      (fun g i => t g i+(step : ZMod (bm g (prime g i))))
  else 0

/-- Exact marked-term correction.  The four chronological gates (birth
Nodup, seen disjointness, source legality and target pullback) are not
relaxed. -/
theorem source_original_MARKED_CLEAN_indexed_eq_unbanned_MINUS_collision434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (xs ys : Small) (a b : A) (t : Old) (S : Finset ℕ)
    (h : Frame) (ss tt : SPerm) :
    sourceOriginalMarkedCleanIndexedTerm434 SP sm BP bm J ell m
      cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
      F xs ys a b t S h ss tt =
    sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
      cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
      F xs ys a b t S h ss tt -
    sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
      cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
      F xs ys a b t S h ss tt := by
  unfold sourceOriginalMarkedCleanIndexedTerm434
    sourceOriginalMarkedUnbannedCleanIndexedTerm434
    sourceOriginalMarkedAuxCollisionIndexedTerm434
  dsimp only
  by_cases hf :
      (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m (patterns h.1)
        (fun g i => b g (h.2.2.2 g i))).Nodup ∧
      Disjoint S (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m
        (patterns h.1) (fun g i => b g (h.2.2.2 g i))).toFinset
  · simp only [if_pos hf]
    rw [source_original_B26_FROZEN_physical_clean_eq_unbanned_MINUS_collision434]
    ring
  · simp [hf]

/-- Full chronological marked CLEAN row after the exact collision split.
The coherent sums over pattern, auxiliary tuple, both BIG endpoint
permutations, target active state, SMALL target and both SMALL permutations
all remain in their literal source order. -/
theorem source_original_MARKED_CLEAN_full_row_eq_unbanned_MINUS_collision434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (xs : Small) (a : A) (t : Old) (S : Finset ℕ) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q 1 Vs Vb mu K zeta theta o k
      (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap sizes hsizes prime a t) S F =
    (∑ h : Frame,∑ b : A,∑ ys : Small,∑ ss : SPerm,∑ tt : SPerm,
      sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
        F xs ys a b t S h ss tt) -
    (∑ h : Frame,∑ b : A,∑ ys : Small,∑ ss : SPerm,∑ tt : SPerm,
      sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
        F xs ys a b t S h ss tt) := by
  rw [source_original_MARKED_CLEAN_full_literal_row434 SP sm BP bm
    J ell m cap sizes hsizes prime patterns mu Vb K q Vs zeta theta o k
    F xs a t S]
  simp_rw [source_original_MARKED_CLEAN_indexed_eq_unbanned_MINUS_collision434]
  simp only [Finset.sum_sub_distrib]

end Green64Analytic.CorrelationSquare

end

end

/-! ## FrozenPhysicalAuxTestCollision -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- B384's true canonical joint Knu AUX-dependent collision is literally the
B381 source FROZEN physical collision, including the original Fock/OLD torus,
its actual dependent D and physical target law. The test remains inside the AUX
sum. The fixed source Fock/OLD torus is not counted or discarded. -/
theorem source_original_B385_frozen_physical_collision_aux_test_exact434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (dsmall : ℕ)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g, sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (a b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k ≠ 0)
    (test : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) → ℂ) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t =>
        sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
          Q hA hB xi aux s t
    (∑ aux : SourceBigAux BP J m pat,
      sourceOriginalB26FrozenAuxCollisionPhysicalWeight434 BP bm
        J ell m patterns SP sm cap sizes hsizes prime mu V K dsmall
        zeta theta o k a r
        (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434 BP J ell m patterns)
        b * test aux) =
    (bigEndpointPairMass (BG := G) (J+ell) : ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau *
      sourceOriginalB26CanonicalAuxTestError434 P V J ell m hmJ ν
        Q hA hB xi dsmall a b sigma tau zeta theta o k test := by
  dsimp only
  unfold sourceOriginalB26FrozenAuxCollisionPhysicalWeight434
    sourceOriginalB26CanonicalAuxTestError434
  dsimp only
  simp only [ho, hk, true_and, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro aux haux
  by_cases hb :
      sourceOriginalB26FrozenAuxBan434 (fun g => {p : ℕ // p ∈ P g})
        J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux a b
  · simp [hb]
  · rw [source_original_B26_FROZEN_PHYSICAL_coefficient434]
    simp [hb, hk] <;> ring

/-- Norm of the ACTUAL frozen physical B26 collision, even with a complex
Fock/OLD/source test that varies by AUX. The original residue torus, real
endpoint mass, target fresh law, moving D and physical orientation remain. -/
theorem source_original_B385_frozen_physical_collision_aux_test_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hB xi : ℝ) (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (Pmin vmin : ℝ) (hP : 0 < Pmin) (hv : 0 < vmin)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVmin : ∀ g, vmin ≤ V g)
    (hPmin : ∀ g p, p ∈ P g → Pmin ≤ (p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (dsmall : ℕ)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g, sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (a b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (r : memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k ≠ 0)
    (test : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hTest : ∀ aux, ‖test aux‖ ≤ M) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t =>
        sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
          Q hA hB xi aux s t
    ‖(∑ aux : SourceBigAux BP J m pat,
      sourceOriginalB26FrozenAuxCollisionPhysicalWeight434 BP bm
        J ell m patterns SP sm cap sizes hsizes prime mu V K dsmall
        zeta theta o k a r
        (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434 BP J ell m patterns)
        b * test aux)‖ ≤
    bigEndpointPairMass (BG := G) (J+ell) *
      ‖sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau‖ *
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2) * M) := by
  dsimp only
  rw [source_original_B385_frozen_physical_collision_aux_test_exact434
    P V J ell m hmJ ν Q hA hB xi mu dsmall SP sm
    cap sizes hsizes prime a b r sigma tau zeta theta o k ho hk test]
  have hmass : 0 ≤ bigEndpointPairMass (BG := G) (J+ell) := by
    unfold bigEndpointPairMass
    exact Finset.prod_nonneg (fun _ _ =>
      (Green64SmallHaar.permutationPairMass_positive (J+ell)).le)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmass]
  exact mul_le_mul_of_nonneg_left
    (source_original_B26_canonical_aux_dependent_test_bound434
      P V J ell m hmJ ν hDisj Q hA hB xi hhA hhB hxi
      Pmin vmin hP hv hV hVmin hPmin dsmall a b sigma tau
      zeta theta o k ho test M hM hTest)
    (mul_nonneg hmass (norm_nonneg _))

end Green64Analytic.CorrelationSquare

end

end

/-! ## MarkedChronologicalAuxCollisionExact -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The literal marked CLEAN collision's AUX-dependent test: numerical birth
LIST Nodup, historical seen exclusion, source SMALL permutations and kernel,
OLD translated residue, Fock pullback, and full future F are all retained.
The source D depends on the actual AUX tuple and both physical orientations. -/
def sourceOriginalB26MarkedChronologicalAuxTest434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g, sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (xs ys : GroupState SP sm (J+ell))
    (a b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ss tt : GroupPermFamily (G := SG) (J+ell))
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν)) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ P g}
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
  let births := sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m
    pat (fun g i => b g (tau g i))
  let dsmall := sourceOriginalB26SmallSourceD434 SP sm J ell xs ss
  let D := sourceOriginalB26FrozenD434 BP bm J ell m dsmall pat aux a sigma
  let step := o*k*(D:ℤ)
  if births.Nodup ∧ Disjoint S births.toFinset then
    (groupPermutationPairMass (G := SG) (J+ell) : ℂ) *
      groupPermutedKernel SP sm (J+ell) q Vs (sourceSmallShared J ell)
        step (fun _ _ => 1) ss tt xs ys *
      sourceOriginalB26TargetPullback434 SP sm BP bm J ell cap sizes
        hsizes prime (fun Y => F Y (S ∪ births.toFinset)) ys b
        (fun g i => t g i + (step : ZMod (bm g (prime g i))))
  else 0

/-- The exact original marked chronological collision row at fixed source and
physical target/permutation coordinates is canonical B26 aux collision tested
against the LITERAL dependent small/OLD/Fock/seen future. No history, OLD,
Fourier, or character counting measure has been substituted or bounded. -/
theorem source_original_B386_marked_chronological_aux_collision_exact434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g, sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (ho : o = 1 ∨ o = -1) (hk : k ≠ 0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (xs ys : GroupState SP sm (J+ell))
    (a b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ss tt : GroupPermFamily (G := SG) (J+ell)) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t =>
        sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν Q hA hB xi aux s t
    (∑ aux : SourceBigAux BP J m pat,
      sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
        F xs ys a b t S
        (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434 BP J ell m patterns)
        ss tt) =
    (bigEndpointPairMass (BG := G) (J+ell) : ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau *
      sourceOriginalB26CanonicalAuxTestError434 P V J ell m hmJ ν
        Q hA hB xi (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss)
        a b sigma tau zeta theta o k
        (sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
          SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S
          sigma tau ss tt) := by
  dsimp only
  calc
    (∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
      sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) J ell m cap sizes hsizes prime (fun _ =>
          sourceOriginalProbeMemoryPattern434 J m hmJ ν) mu V
        (fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
          Q hA hB xi aux s t) q Vs zeta theta o k F xs ys a b t S
        (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434
          (fun g => {p : ℕ // p ∈ P g}) J ell m
          (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν)) ss tt) =
    (∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
      sourceOriginalB26FrozenAuxCollisionPhysicalWeight434 (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) J ell m
        (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν)
        SP sm cap sizes hsizes prime mu V
        (fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
          Q hA hB xi aux s t)
        (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss) zeta theta o k
        a (0,t) (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434
          (fun g => {p : ℕ // p ∈ P g}) J ell m
          (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν)) b *
      sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
        SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S sigma tau ss tt aux) := by
        apply Finset.sum_congr rfl
        intro aux haux
        unfold sourceOriginalMarkedAuxCollisionIndexedTerm434
          sourceOriginalB26MarkedChronologicalAuxTest434
        dsimp only
        by_cases hg :
          (sourceOriginalMarkedCleanBirthNumbers434 (fun g => {p : ℕ // p ∈ P g})
            (fun _ p => p.val) J ell m
            (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
            (fun g i => b g (tau g i))).Nodup ∧
          Disjoint S (sourceOriginalMarkedCleanBirthNumbers434
            (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) J ell m
            (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
            (fun g i => b g (tau g i))).toFinset
        · simp [hg] <;> ring
        · simp [hg]
    _ = _ := source_original_B385_frozen_physical_collision_aux_test_exact434
      P V J ell m hmJ ν Q hA hB xi mu
      (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss)
      SP sm cap sizes hsizes prime a b (0,t) sigma tau
      zeta theta o k ho hk
      (sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
        SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S sigma tau ss tt)

end Green64Analytic.CorrelationSquare

end

end

/-! ## MarkedAuxTestUniformFutureBound -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- A genuinely physical SMALL kernel's norm is bounded by the SAME original
SMALL edge scalar, uniformly in the moving integer shift. No parity symmetry,
positivity of a complex Fourier coefficient, or auxiliary counting is used:
the only shift dependence is an honest zero-or-one legality gate. -/
theorem source_original_B387_SMALL_kernel_uniform_shift_bound434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
    (M : ℕ) (q : ℝ) (Vs : SG → ℝ)
    (shared : (g : SG) → Finset (Fin M))
    (step : ℤ) (ss tt : GroupPermFamily (G := SG) M)
    (xs ys : GroupState SP sm M) :
    ‖groupPermutedKernel SP sm M q Vs shared step (fun _ _ => 1)
      ss tt xs ys‖ ≤
    ‖(groupEdgeScalar SP sm M q Vs shared xs ys : ℂ)‖ := by
  unfold groupPermutedKernel
  by_cases hg : groupEdgeAllowedPerm SP sm M shared step ss tt xs ys
  · simp [hg]
  · simp [hg]

/-- Actual Fock/OLD, birth-list and historical seen test bounded pointwise
uniformly over AUX by the original SMALL edge coefficient and a bound on the
literal marked target observable. Crucially the SMALL scalar is independent
of the AUX-dependent physical shift even though its legality is not. -/
theorem source_original_B387_marked_chronological_aux_test_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g, sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ Y seen, ‖F Y seen‖ ≤ B)
    (xs ys : GroupState SP sm (J+ell))
    (a b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ss tt : GroupPermFamily (G := SG) (J+ell))
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν)) :
    ‖sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
      SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S
      sigma tau ss tt aux‖ ≤
    groupPermutationPairMass (G := SG) (J+ell) *
      ‖(groupEdgeScalar SP sm (J+ell) q Vs (sourceSmallShared J ell)
         xs ys : ℂ)‖ * B := by
  have hmass : 0 ≤ groupPermutationPairMass (G := SG) (J+ell) :=
    (groupPermutationPairMass_positive (G := SG) (J+ell)).le
  have hkernel := source_original_B387_SMALL_kernel_uniform_shift_bound434
    SP sm (J+ell) q Vs (sourceSmallShared J ell)
    (o*k*(sourceOriginalB26FrozenD434
      (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
      J ell m (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss)
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux a sigma : ℤ))
    ss tt xs ys
  unfold sourceOriginalB26MarkedChronologicalAuxTest434
  dsimp only
  by_cases hb :
    (sourceOriginalMarkedCleanBirthNumbers434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
      (fun g i => b g (tau g i))).Nodup ∧
    Disjoint S (sourceOriginalMarkedCleanBirthNumbers434
      (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
      (fun g i => b g (tau g i))).toFinset
  · rw [if_pos hb, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hmass]
    have htarget :
      ‖sourceOriginalB26TargetPullback434 SP sm (fun g => {p : ℕ // p ∈ P g})
          (fun _ p => p.val) J ell cap sizes hsizes prime
          (fun Y => F Y (S ∪
            (sourceOriginalMarkedCleanBirthNumbers434 (fun g => {p : ℕ // p ∈ P g})
              (fun _ p => p.val) J ell m
              (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
              (fun g i => b g (tau g i))).toFinset)) ys b
          (fun g i => t g i +
            (o*k*(sourceOriginalB26FrozenD434 (fun g => {p : ℕ // p ∈ P g})
              (fun _ p => p.val) J ell m
              (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss)
              (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux a sigma : ℤ) :
              ZMod ((fun _ p => p.val) g (prime g i))))‖ ≤ B := by
      unfold sourceOriginalB26TargetPullback434
      exact hF _ _
    simp only [Int.cast_mul] at htarget ⊢
    calc
      _ ≤ (groupPermutationPairMass (G := SG) (J+ell)) *
          ‖(groupEdgeScalar SP sm (J+ell) q Vs (sourceSmallShared J ell)
            xs ys : ℂ)‖ *
          ‖sourceOriginalB26TargetPullback434 SP sm (fun g => {p : ℕ // p ∈ P g})
            (fun _ p => p.val) J ell cap sizes hsizes prime
            (fun Y => F Y (S ∪
              (sourceOriginalMarkedCleanBirthNumbers434 (fun g => {p : ℕ // p ∈ P g})
                (fun _ p => p.val) J ell m
                (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
                (fun g i => b g (tau g i))).toFinset)) ys b
            (fun g i => t g i +
              (o*k*(sourceOriginalB26FrozenD434 (fun g => {p : ℕ // p ∈ P g})
                (fun _ p => p.val) J ell m
                (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss)
                (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux a sigma : ℤ) :
                ZMod ((fun _ p => p.val) g (prime g i))))‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hkernel hmass) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left htarget
        (mul_nonneg hmass (norm_nonneg _))
  · simp only [if_neg hb, norm_zero]
    exact mul_nonneg (mul_nonneg hmass (norm_nonneg _)) hB

end Green64Analytic.CorrelationSquare

end

end

/-! ## MarkedPhysicalCollisionBound -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The literal chronological marked B26 collision is quantitatively bounded
even when its SMALL/OLD/Fock/seen future depends on the auxiliary tuple
through the moving source divisor D.  The B26 collision is paid exactly once;
both endpoint permutations and either physical orientation remain explicit. -/
theorem source_original_B388_marked_chronological_collision_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0 < hA) (hhC : 0 < hC) (hxi : 0 < xi)
    (Pmin vmin : ℝ) (hP : 0 < Pmin) (hv : 0 < vmin)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVmin : ∀ g, vmin ≤ V g)
    (hPmin : ∀ g p, p ∈ P g → Pmin ≤ (p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g, sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (ho : o = 1 ∨ o = -1) (hk : k ≠ 0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ Y seen, ‖F Y seen‖ ≤ B)
    (xs ys : GroupState SP sm (J+ell))
    (a b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ss tt : GroupPermFamily (G := SG) (J+ell)) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t =>
        sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
          Q hA hC xi aux s t
    ‖(∑ aux : SourceBigAux BP J m pat,
      sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
        F xs ys a b t S
        (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434 BP J ell m patterns)
        ss tt)‖ ≤
    bigEndpointPairMass (BG := G) (J+ell) *
      ‖sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau‖ *
      (((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
          (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
        (groupPermutationPairMass (G := SG) (J+ell) *
          ‖(groupEdgeScalar SP sm (J+ell) q Vs (sourceSmallShared J ell)
            xs ys : ℂ)‖ * B)) := by
  dsimp only
  rw [source_original_B386_marked_chronological_aux_collision_exact434
    P V J ell m hmJ ν Q hA hC xi mu SP sm cap sizes hsizes prime
    q Vs zeta theta o k ho hk F xs ys a b t S sigma tau ss tt]
  have hmass : 0 ≤ bigEndpointPairMass (BG := G) (J+ell) := by
    unfold bigEndpointPairMass
    exact Finset.prod_nonneg (fun _ _ =>
      (Green64SmallHaar.permutationPairMass_positive (J+ell)).le)
  have hsmass : 0 ≤ groupPermutationPairMass (G := SG) (J+ell) :=
    (groupPermutationPairMass_positive (G := SG) (J+ell)).le
  have hM : 0 ≤ groupPermutationPairMass (G := SG) (J+ell) *
      ‖(groupEdgeScalar SP sm (J+ell) q Vs (sourceSmallShared J ell)
          xs ys : ℂ)‖ * B :=
    mul_nonneg (mul_nonneg hsmass (norm_nonneg _)) hB
  have htest := fun aux =>
    source_original_B387_marked_chronological_aux_test_bound434
      P J ell m hmJ ν SP sm cap sizes hsizes prime q Vs o k
      F B hB hF xs ys a b t S sigma tau ss tt aux
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmass]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hmass (norm_nonneg _))
  convert source_original_B26_canonical_aux_dependent_test_bound434
    P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
    Pmin vmin hP hv hV hVmin hPmin
    (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss)
    a b sigma tau zeta theta o k ho
    (sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
      SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S sigma tau ss tt)
    (groupPermutationPairMass (G := SG) (J+ell) *
      ‖(groupEdgeScalar SP sm (J+ell) q Vs (sourceSmallShared J ell)
        xs ys : ℂ)‖ * B) hM htest using 1

end Green64Analytic.CorrelationSquare

end

end

/-! ## OrbitFullMarkedCollisionExact -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap sizes : BG → ℕ)
  (hsizes : ∀ g,sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

local notation "Small" => GroupState SP sm (J+ell)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bm sizes prime
local notation "Frame" => SourceOriginalB26FrozenFrame434 BP J ell m patterns
local notation "SPerm" => GroupPermFamily (G := SG) (J+ell)
local notation "Out" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- The original physical Fock-orbit consumer, not merely the frozen
representative, is literally chronological unbanned CLEAN minus the genuine
B26 collision before any norm, character projection or Fourier integral.
The B374 orbit average keeps its original mass exactly once; both OLD and
seen remain in the Fock representative and chronological target pullback. -/
theorem source_original_B389_orbit_MARKED_CLEAN_eq_unbanned_MINUS_collision434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (hVs : ∀ g, 0 < Vs g) (hmu : ∀ g p, 0 < mu g p)
    (F : Out → Finset ℕ → ℂ)
    (xs : Small) (a : A) (t : Old) (S : Finset ℕ)
    (hr : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t)) S) :
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
        J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q 1 Vs Vb mu K zeta theta o k st S F)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t)) =
    (∑ h : Frame,∑ b : A,∑ ys : Small,∑ ss : SPerm,∑ tt : SPerm,
      sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm
        J ell m cap sizes hsizes prime patterns
        mu Vb K q Vs zeta theta o k F xs ys a b t S h ss tt) -
    (∑ h : Frame,∑ b : A,∑ ys : Small,∑ ss : SPerm,∑ tt : SPerm,
      sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm
        J ell m cap sizes hsizes prime patterns
        mu Vb K q Vs zeta theta o k F xs ys a b t S h ss tt) := by
  calc
    _ = sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m
          cap patterns
          (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
          q 1 Vs Vb mu K zeta theta o k
          (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
            sizes hsizes prime a t) S F :=
      source_original_SOURCE_MARKED_CLEAN_E_orbit_representative434
        SP sm BP bm J ell m cap patterns
        (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t) S hr q 1 Vs Vb mu hVs hmu
        K zeta theta o k F
    _ = _ := source_original_MARKED_CLEAN_full_row_eq_unbanned_MINUS_collision434
      SP sm BP bm J ell m cap sizes hsizes prime patterns
      mu Vb K q Vs zeta theta o k F xs a t S

end Green64Analytic.CorrelationSquare

end

end

/-! ## B26TargetFreshMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (J ell m : ℕ)

/-- Real presentation of the original frozen BIG fresh law. This keeps
the genuine source endpoint, its two permutations and shared copy gates. -/
def source_original_B390_fresh_law_real434
    (mu : (g : G) → BP g → ℝ) (pat : SourcePattern G J m)
    (a b : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) : ℝ :=
  ∏ g,∏ i : Fin (J+ell),if i ∈ sourceBigShared J ell m pat g then
    (if b g (tau g i)=a g (sigma g i) then 1 else 0) else
      mu g (b g (tau g i))

theorem source_original_B390_fresh_law_real_cast434
    (mu : (g : G) → BP g → ℝ) (pat : SourcePattern G J m)
    (a b : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    (source_original_B390_fresh_law_real434 BP J ell m mu pat a b sigma tau : ℂ) =
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau := by
  rw [source_original_B26_fresh_law_permuted434]
  unfold source_original_B390_fresh_law_real434 sourceOriginalB26FrozenFreshLaw434
  push_cast
  simp only [Equiv.refl_symm,Equiv.refl_apply]
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp_all

theorem source_original_B390_fresh_law_real_nonneg434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (pat : SourcePattern G J m)
    (a b : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    0 ≤ source_original_B390_fresh_law_real434 BP J ell m mu pat a b sigma tau := by
  apply Finset.prod_nonneg
  intro g _
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> first | positivity | exact hmu _ _

/-- Exact sum over all target BIG active arrays: one, rather than their
cardinality. No iid law is substituted: shared positions are copied and
all original target and source permutations are kept. -/
theorem source_original_B390_fresh_law_real_row_mass434
    (mu : (g : G) → BP g → ℝ) (hmass : ∀ g,∑ p : BP g,mu g p=1)
    (pat : SourcePattern G J m) (a : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    (∑ b,source_original_B390_fresh_law_real434 BP J ell m mu pat a b sigma tau)=1 := by
  let e := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau
  have hr : (∑ b,source_original_B390_fresh_law_real434 BP J ell m mu pat a b sigma tau) =
      ∑ b : SourceOriginalB26Active434 BP J ell,∏ g,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then
          (if b g i=a g (sigma g i) then 1 else 0) else mu g (b g i) := by
    apply Fintype.sum_equiv e
    intro b
    rfl
  rw [hr,← Fintype.prod_sum (fun (g : G) (b : Fin (J+ell) → BP g) =>
    ∏ i : Fin (J+ell),if i ∈ sourceBigShared J ell m pat g then
      (if b i=a g (sigma g i) then (1:ℝ) else 0) else mu g (b i))]
  have hg (g : G) :
      (∑ b : Fin (J+ell) → BP g,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then
          (if b i=a g (sigma g i) then (1:ℝ) else 0) else mu g (b i))=1 := by
    rw [← Fintype.prod_sum (fun (i : Fin (J+ell)) (p : BP g) =>
      if i ∈ sourceBigShared J ell m pat g then
        (if p=a g (sigma g i) then (1:ℝ) else 0) else mu g p)]
    apply Finset.prod_eq_one
    intro i _
    by_cases hi : i ∈ sourceBigShared J ell m pat g
    · simp [hi]
    · simpa only [if_neg hi] using hmass g
  simp only [hg,Finset.prod_const_one]

/-- The B388 target mass is a normalized positive measure, with no
extra factor for repeated source or target prime marks. This is directly
the original complex B26 law, not a comparison replacement. -/
theorem source_original_B390_original_fresh_law_norm_row_mass434
    (mu : (g : G) → BP g → ℝ)
    (hmu : ∀ g p,0 ≤ mu g p)
    (hmass : ∀ g,∑ p : BP g,mu g p=1)
    (pat : SourcePattern G J m) (a : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    (∑ b : SourceOriginalB26Active434 BP J ell,
      ‖sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau‖) = 1 := by
  have hnorm (b : SourceOriginalB26Active434 BP J ell) :
      ‖sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau‖ =
        source_original_B390_fresh_law_real434 BP J ell m mu pat a b sigma tau := by
    rw [← source_original_B390_fresh_law_real_cast434]
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (source_original_B390_fresh_law_real_nonneg434
        BP J ell m mu hmu pat a b sigma tau)]
  simp only [hnorm]
  exact source_original_B390_fresh_law_real_row_mass434
    BP J ell m mu hmass pat a sigma tau

end Green64Analytic.CorrelationSquare

end

end

/-! ## MarkedCollisionTargetSum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The entire target BIG active-state sum of the genuine marked B26
collision is bounded without its cardinality: the original fresh law
has normalized mass one even with repetitions and shared copy gates.
The AUX-dependent shift is not pulled out, and both BIG and SMALL endpoint
permutations and OLD/seen data are retained pointwise. -/
theorem source_original_B391_marked_collision_target_sum_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0 < hA) (hhC : 0 < hC) (hxi : 0 < xi)
    (Pmin vmin : ℝ) (hP : 0 < Pmin) (hv : 0 < vmin)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVmin : ∀ g, vmin ≤ V g)
    (hPmin : ∀ g p, p ∈ P g → Pmin ≤ (p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (hmass : ∀ g, ∑ p : {p : ℕ // p ∈ P g}, mu g p = 1)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g, sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (ho : o = 1 ∨ o = -1) (hk : k ≠ 0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ Y seen, ‖F Y seen‖ ≤ B)
    (xs ys : GroupState SP sm (J+ell))
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ss tt : GroupPermFamily (G := SG) (J+ell)) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    ‖∑ b : SourceOriginalB26Active434 BP J ell,
      ∑ aux : SourceBigAux BP J m pat,
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
          cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
          F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434 BP J ell m patterns)
          ss tt‖ ≤
    bigEndpointPairMass (BG := G) (J+ell) *
      (((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
        (groupPermutationPairMass (G := SG) (J+ell) *
          ‖(groupEdgeScalar SP sm (J+ell) q Vs (sourceSmallShared J ell)
            xs ys : ℂ)‖ * B)) := by
  dsimp only
  let fac : ℝ :=
    bigEndpointPairMass (BG := G) (J+ell) *
      (((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
        (groupPermutationPairMass (G := SG) (J+ell) *
          ‖(groupEdgeScalar SP sm (J+ell) q Vs (sourceSmallShared J ell)
            xs ys : ℂ)‖ * B))
  have hbound (b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell) :
      ‖∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
            (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm
          (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
          J ell m cap sizes hsizes prime
          (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν)
          mu V
          (fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V
            J ell m hmJ ν Q hA hC xi aux s t)
          q Vs zeta theta o k F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434
            (fun g => {p : ℕ // p ∈ P g}) J ell m
            (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν))
          ss tt‖ ≤
        ‖sourceOriginalB26FrozenFreshLaw434 (fun g => {p : ℕ // p ∈ P g})
          J ell m mu (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
          a b sigma tau‖ * fac := by
    convert source_original_B388_marked_chronological_collision_bound434
      P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
      Pmin vmin hP hv hV hVmin hPmin mu SP sm
      cap sizes hsizes prime q Vs zeta theta o k ho hk
      F B hB hF xs ys a b t S sigma tau ss tt using 1 <;> dsimp [fac] <;> ring
  calc
    _ ≤ ∑ b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell,
          ‖∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
              (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
            sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm
              (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) J ell m
              cap sizes hsizes prime
              (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν) mu V
              (fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
                Q hA hC xi aux s t) q Vs zeta theta o k
              F xs ys a b t S
              (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434
                (fun g => {p : ℕ // p ∈ P g}) J ell m
                (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν)) ss tt‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell,
          ‖sourceOriginalB26FrozenFreshLaw434 (fun g => {p : ℕ // p ∈ P g})
            J ell m mu (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
            a b sigma tau‖ * fac := by
      apply Finset.sum_le_sum
      intro b hb
      exact hbound b
    _ = (∑ b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell,
          ‖sourceOriginalB26FrozenFreshLaw434 (fun g => {p : ℕ // p ∈ P g})
            J ell m mu (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
            a b sigma tau‖) * fac := by rw [Finset.sum_mul]
    _ = fac := by
      rw [source_original_B390_original_fresh_law_norm_row_mass434
        (fun g => {p : ℕ // p ∈ P g}) J ell m mu hmu hmass
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) a sigma tau, one_mul]
    _ = _ := rfl

end Green64Analytic.CorrelationSquare

end

end

/-! ## FourHaarNoCardinalityLoss -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Both of the actual original source/target permutation measures, BIG and
SMALL, have exactly unit total mass. The full pair normalization is in real
arithmetic, which is what quantitative norm inequalities need. -/
theorem source_original_B392_four_Haar_real_normalized434
    {G SG : Type} [Fintype G] [DecidableEq G]
    [Fintype SG] [DecidableEq SG] (M : ℕ) :
    bigEndpointPairMass (BG := G) M *
      groupPermutationPairMass (G := SG) M *
      ((Fintype.card (BigGroupPerm (BG := G) M) : ℝ)^2 *
       (Fintype.card (GroupPermFamily (G := SG) M) : ℝ)^2) = 1 := by
  have hbig : bigEndpointPairMass (BG := G) M *
      (Fintype.card (BigGroupPerm (BG := G) M) : ℝ)^2 = 1 := by
    have hc : (bigEndpointPairMass (BG := G) M : ℂ) *
        ((Fintype.card (BigGroupPerm (BG := G) M) : ℂ)^2) = 1 := by
      simpa [bigEndpointPairMass, groupPermutationPairMass,
        BigGroupPerm, GroupPermFamily] using
          (groupPermutationPairMass_normalized (G := G) M)
    exact_mod_cast hc
  have hsmall : groupPermutationPairMass (G := SG) M *
      (Fintype.card (GroupPermFamily (G := SG) M) : ℝ)^2 = 1 := by
    exact_mod_cast (groupPermutationPairMass_normalized (G := SG) M)
  calc
    _ = (bigEndpointPairMass (BG := G) M *
          (Fintype.card (BigGroupPerm (BG := G) M) : ℝ)^2) *
        (groupPermutationPairMass (G := SG) M *
          (Fintype.card (GroupPermFamily (G := SG) M) : ℝ)^2) := by ring
    _ = 1 := by rw [hbig, hsmall]; ring

/-- Four original permutation sums, with their *actual* physical BIG and
SMALL pair densities, are a normalized average, not four raw cardinality
losses. This handles a completely arbitrary dependent complex integrand,
so later AUX/OLD/seen/Fock/character tests remain inside the sum. -/
theorem source_original_B392_four_Haar_uniform_bound434
    {G SG : Type} [Fintype G] [DecidableEq G]
    [Fintype SG] [DecidableEq SG] (M : ℕ)
    (f : BigGroupPerm (BG := G) M → BigGroupPerm (BG := G) M →
      GroupPermFamily (G := SG) M → GroupPermFamily (G := SG) M → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ sigma tau ss tt, ‖f sigma tau ss tt‖ ≤
      bigEndpointPairMass (BG := G) M *
        groupPermutationPairMass (G := SG) M * B) :
    ‖∑ sigma, ∑ tau, ∑ ss, ∑ tt, f sigma tau ss tt‖ ≤ B := by
  let D : ℝ := bigEndpointPairMass (BG := G) M *
    groupPermutationPairMass (G := SG) M * B
  have hD : 0 ≤ D := by
    dsimp [D]
    apply mul_nonneg
    · apply mul_nonneg
      · unfold bigEndpointPairMass
        exact Finset.prod_nonneg (fun _ _ =>
          (permutationPairMass_positive M).le)
      · exact (groupPermutationPairMass_positive (G := SG) M).le
    · exact hB
  calc
    ‖∑ sigma, ∑ tau, ∑ ss, ∑ tt, f sigma tau ss tt‖ ≤
      ∑ sigma, ‖∑ tau, ∑ ss, ∑ tt, f sigma tau ss tt‖ := norm_sum_le _ _
    _ ≤ ∑ sigma, ∑ tau, ‖∑ ss, ∑ tt, f sigma tau ss tt‖ := by
      apply Finset.sum_le_sum; intro sigma hsigma; exact norm_sum_le _ _
    _ ≤ ∑ sigma, ∑ tau, ∑ ss, ‖∑ tt, f sigma tau ss tt‖ := by
      apply Finset.sum_le_sum; intro sigma hsigma
      apply Finset.sum_le_sum; intro tau htau
      exact norm_sum_le _ _
    _ ≤ ∑ sigma, ∑ tau, ∑ ss, ∑ tt, ‖f sigma tau ss tt‖ := by
      apply Finset.sum_le_sum; intro sigma hsigma
      apply Finset.sum_le_sum; intro tau htau
      apply Finset.sum_le_sum; intro ss hss
      exact norm_sum_le _ _
    _ ≤ ∑ sigma : BigGroupPerm (BG := G) M,
          ∑ tau : BigGroupPerm (BG := G) M,
          ∑ ss : GroupPermFamily (G := SG) M,
          ∑ tt : GroupPermFamily (G := SG) M, D := by
      apply Finset.sum_le_sum; intro sigma hsigma
      apply Finset.sum_le_sum; intro tau htau
      apply Finset.sum_le_sum; intro ss hss
      apply Finset.sum_le_sum; intro tt htt
      exact hf sigma tau ss tt
    _ = B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [D]
      have hnorm := source_original_B392_four_Haar_real_normalized434 (G := G) (SG := SG) M
      push_cast
      nlinarith [hnorm]
end Green64Analytic.CorrelationSquare

end

end

/-! ## FullPermutationMarkedCollisionBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Full source/target BIG and SMALL permutation averages of the literal
chronological B26 collision, after its genuine BIG target-state sum.
The original auxiliary-dependent D, OLD/Fock and numerical seen/birth gates
are preserved; no factor counting permutations or target BIG arrays remains. -/
theorem source_original_B393_full_Haar_marked_collision_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0 < hA) (hhC : 0 < hC) (hxi : 0 < xi)
    (Pmin vmin : ℝ) (hP : 0 < Pmin) (hv : 0 < vmin)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVmin : ∀ g, vmin ≤ V g)
    (hPmin : ∀ g p, p ∈ P g → Pmin ≤ (p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (hmass : ∀ g, ∑ p : {p : ℕ // p ∈ P g}, mu g p = 1)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g, sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (ho : o = 1 ∨ o = -1) (hk : k ≠ 0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ Y seen, ‖F Y seen‖ ≤ B)
    (xs ys : GroupState SP sm (J+ell))
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    ‖∑ sigma : BigGroupPerm (BG := G) (J+ell),
      ∑ tau : BigGroupPerm (BG := G) (J+ell),
      ∑ ss : GroupPermFamily (G := SG) (J+ell),
      ∑ tt : GroupPermFamily (G := SG) (J+ell),
      ∑ b : SourceOriginalB26Active434 BP J ell,
      ∑ aux : SourceBigAux BP J m pat,
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
          cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
          F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434 BP J ell m patterns)
          ss tt‖ ≤
    ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
      (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      ‖(groupEdgeScalar SP sm (J+ell) q Vs (sourceSmallShared J ell)
        xs ys : ℂ)‖ * B := by
  dsimp only
  let delta : ℝ :=
    (((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
      (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)
  let edge : ℝ := ‖(groupEdgeScalar SP sm (J+ell) q Vs
      (sourceSmallShared J ell) xs ys : ℂ)‖
  have hd : 0 ≤ delta := by
    dsimp [delta]
    have hpv : 0 ≤ Pmin*vmin := le_of_lt (mul_pos hP hv)
    positivity
  have he : 0 ≤ edge := norm_nonneg _
  have hM : 0 ≤ delta*edge*B := mul_nonneg (mul_nonneg hd he) hB
  have h := source_original_B392_four_Haar_uniform_bound434
    (G := G) (SG := SG) (J+ell)
    (fun sigma tau ss tt =>
      ∑ b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell,
      ∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm
          (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
          J ell m cap sizes hsizes prime
          (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν) mu V
          (fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
            Q hA hC xi aux s t)
          q Vs zeta theta o k F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434
            (fun g => {p : ℕ // p ∈ P g}) J ell m
            (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν)) ss tt)
    (delta*edge*B) hM (by
      intro sigma tau ss tt
      convert source_original_B391_marked_collision_target_sum_bound434
        P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
        Pmin vmin hP hv hV hVmin hPmin mu hmu hmass
        SP sm cap sizes hsizes prime q Vs zeta theta o k ho hk
        F B hB hF xs ys a t S sigma tau ss tt using 1 <;>
        dsimp [delta,edge] <;> ring)
  simpa only [delta,edge] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## AuxDependentSmallTargetRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Do not bound the SMALL legality gate by one before summing SMALL target
states: doing so destroys the available row estimate. For every actual
AUX-dependent frozen D and target Fock/OLD/seen test, the *gated* original
SMALL row has the ell-only physical mass, independent of the source shift.
This is the input needed to pay B26 collision after, not before, the y-sum. -/
theorem source_original_B394_aux_dependent_SMALL_target_row434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hVs : ∀ g, 0 < Vs g) (o k : ℤ)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ Y seen, ‖F Y seen‖ ≤ B)
    (xs : GroupState SP sm (J+ell))
    (a b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ss tt : GroupPermFamily (G := SG) (J+ell))
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν)) :
    ‖∑ ys : GroupState SP sm (J+ell),
      sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
        SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S
        sigma tau ss tt aux‖ ≤
    groupPermutationPairMass (G := SG) (J+ell) *
      (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B := by
  let M := J+ell
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
  let births := sourceOriginalMarkedCleanBirthNumbers434 (fun g => {p : ℕ // p ∈ P g})
    (fun _ p => p.val) J ell m pat (fun g i => b g (tau g i))
  let dsmall := sourceOriginalB26SmallSourceD434 SP sm J ell xs ss
  let D := sourceOriginalB26FrozenD434 (fun g => {p : ℕ // p ∈ P g})
    (fun _ p => p.val) J ell m dsmall pat aux a sigma
  let step : ℤ := o*k*(D:ℤ)
  let mass := groupPermutationPairMass (G := SG) M
  let ker := fun ys : GroupState SP sm M =>
    groupPermutedKernel SP sm M q Vs (sourceSmallShared J ell) step
      (fun _ _ => (1:ℂ)) ss tt xs ys
  have hmass : 0 ≤ mass := (groupPermutationPairMass_positive (G := SG) M).le
  have hrow : (∑ ys : GroupState SP sm M, ‖ker ys‖) ≤
      ∏ g : SG, memorySmallRowConstant q (Vs g) ell := by
    simpa only [ker,M,norm_one,one_mul] using
      (source_original_memory_SOURCE_SMALL_group_kernel_row434
        SP sm J ell q Vs hq hq1 hVs step (fun _ _ => (1:ℂ)) ss tt xs)
  have htest (ys : GroupState SP sm M) :
      ‖sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
        SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S
        sigma tau ss tt aux‖ ≤ mass*‖ker ys‖*B := by
    have htarget :
        ‖sourceOriginalB26TargetPullback434 SP sm
          (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
          J ell cap sizes hsizes prime
          (fun Y => F Y (S ∪ births.toFinset)) ys b
          (fun g i => t g i + (step : ZMod ((fun _ p => p.val) g (prime g i))))‖ ≤ B := by
      unfold sourceOriginalB26TargetPullback434
      exact hF _ _
    change ‖if births.Nodup ∧ Disjoint S births.toFinset then
        (mass:ℂ) * ker ys *
          sourceOriginalB26TargetPullback434 SP sm
            (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
            J ell cap sizes hsizes prime
            (fun Y => F Y (S ∪ births.toFinset)) ys b
            (fun g i => t g i +
              (step : ZMod ((fun _ p => p.val) g (prime g i))))
        else 0‖ ≤ mass*‖ker ys‖*B
    by_cases hb : births.Nodup ∧ Disjoint S births.toFinset
    · rw [if_pos hb, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hmass]
      exact mul_le_mul_of_nonneg_left htarget
        (mul_nonneg hmass (norm_nonneg _))
    · rw [if_neg hb, norm_zero]
      exact mul_nonneg (mul_nonneg hmass (norm_nonneg _)) hB
  calc
    ‖∑ ys : GroupState SP sm M,
      sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
        SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S
        sigma tau ss tt aux‖ ≤
      ∑ ys : GroupState SP sm M,
        ‖sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
          SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S
          sigma tau ss tt aux‖ := norm_sum_le _ _
    _ ≤ ∑ ys : GroupState SP sm M, mass * ‖ker ys‖ * B := by
      apply Finset.sum_le_sum
      intro ys hys
      exact htest ys
    _ = mass * (∑ ys : GroupState SP sm M, ‖ker ys‖) * B := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ mass * (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrow hmass) hB
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## CollisionAfterSmallTargetRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Apply the source B26 collision to the genuine shift-aware SMALL target row. -/
theorem source_original_B395_B26_aux_collision_after_SMALL_target434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
    (Pmin vmin : ℝ) (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPmin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
    (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖ ≤ B)
    (xs : GroupState SP sm (J+ell))
    (a b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ss tt : GroupPermFamily (G := SG) (J+ell)) :
    ‖sourceOriginalB26CanonicalAuxTestError434 P V J ell m hmJ ν
      Q hA hC xi (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss)
      a b sigma tau zeta theta o k
      (fun aux => ∑ ys : GroupState SP sm (J+ell),
        sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
          SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S
          sigma tau ss tt aux)‖ ≤
    ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
      (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (groupPermutationPairMass (G := SG) (J+ell) *
        (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B) := by
  let C : ℝ := groupPermutationPairMass (G := SG) (J+ell) *
    (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    have hp : 0 ≤ groupPermutationPairMass (G := SG) (J+ell) :=
      (groupPermutationPairMass_positive (G := SG) (J+ell)).le
    have hsqrt : Real.sqrt q < 1 := by
      have hsq := Real.sq_sqrt (le_of_lt hq)
      have hn := Real.sqrt_nonneg q
      nlinarith only [hsq, hn, hq1]
    have hden : 0 < 1 - Real.sqrt q := sub_pos.mpr hsqrt
    have hc : ∀ g : SG, 0 ≤ memorySmallRowConstant q (Vs g) ell := by
      intro g
      unfold memorySmallRowConstant
      have hv := hVs g
      positivity
    exact mul_nonneg (mul_nonneg hp (Finset.prod_nonneg (fun g hg => hc g))) hB
  have htest : ∀ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
      ‖∑ ys : GroupState SP sm (J+ell),
        sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
          SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S
          sigma tau ss tt aux‖ ≤ C := by
    intro aux
    simpa only [C] using
      (source_original_B394_aux_dependent_SMALL_target_row434
        P J ell m hmJ ν SP sm cap sizes hsizes prime q Vs hq hq1 hVs
        o k F B hB hF xs a b t S sigma tau ss tt aux)
  convert (source_original_B26_canonical_aux_dependent_test_bound434
      P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
      Pmin vmin hP hv hV hVmin hPmin
      (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss)
      a b sigma tau zeta theta o k ho
      (fun aux => ∑ ys : GroupState SP sm (J+ell),
        sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
          SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S
          sigma tau ss tt aux) C hCnonneg htest) using 1 <;> dsimp [C]
end Green64Analytic.CorrelationSquare

end

end

/-! ## CanonicalCollisionFubini -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exact finite Fubini for a collision/test kernel. No positivity or
independence assumption is made: the coefficient and the forbidden event
may depend arbitrarily on the full AUX coordinate. -/
theorem source_original_B396_finite_bad_aux_test_sum_comm434
    {A Y : Type} [Fintype A] [Fintype Y]
    (w c : A → ℂ) (ban : A → Prop) [DecidablePred ban]
    (test : A → Y → ℂ) :
    (∑ a : A, w a * (if ban a then 0 else c a *
       (∑ y : Y, test a y))) =
    ∑ y : Y, ∑ a : A, w a *
      (if ban a then 0 else c a * test a y) := by
  classical
  calc
    _ = ∑ a : A, ∑ y : Y, w a *
          (if ban a then 0 else c a * test a y) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hb : ban a
      · simp [hb]
      · simp only [if_neg hb, Finset.mul_sum]
    _ = _ := Finset.sum_comm
end Green64Analytic.CorrelationSquare

end

end

/-! ## CanonicalSourceCollisionFubini -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The genuine B26 canonical AUX collision commutes with any finite target
sum before norm and before the four-sign projector. The source mass, moving
D, joint canonical K, and auxiliary/active ban remain untouched. -/
theorem source_original_B397_canonical_aux_error_finite_fubini434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hC xi : ℝ) (dsmall : ℕ)
    (s t : ∀ g, Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ)
    {Y : Type} [Fintype Y]
    (test : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) → Y → ℂ) :
    sourceOriginalB26CanonicalAuxTestError434 P V J ell m hmJ ν
      Q hA hC xi dsmall s t sigma tau zeta theta o k
      (fun aux => ∑ y : Y, test aux y) =
    ∑ y : Y, sourceOriginalB26CanonicalAuxTestError434 P V J ell m hmJ ν
      Q hA hC xi dsmall s t sigma tau zeta theta o k
      (fun aux => test aux y) := by
  classical
  let BP := fun g => {p : ℕ // p ∈ P g}
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
  let Aux := SourceBigAux BP J m pat
  let w : Aux → ℂ := fun aux =>
    (sourceAuxMass BP (fun _ p => p.val) J m V pat aux : ℂ)
  let ban : Aux → Prop := fun aux =>
    sourceOriginalB26FrozenAuxBan434 BP J ell m pat aux s t
  let c : Aux → ℂ := fun aux =>
    originalEdgeScalar
      (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux
        (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
      zeta theta
      (sourceOriginalB26FrozenD434 BP (fun _ p => p.val) J ell m
        dsmall pat aux s sigma) o k
  change (∑ aux : Aux, w aux * (if ban aux then 0 else
      c aux * (∑ y : Y, test aux y))) =
    ∑ y : Y, ∑ aux : Aux, w aux *
      (if ban aux then 0 else c aux * test aux y)
  exact source_original_B396_finite_bad_aux_test_sum_comm434 w c ban test
end Green64Analytic.CorrelationSquare

end

end

/-! ## MarkedPhysicalAuxSmallFubini -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The *literal* B386 physical chronological B26 collision, now including
all SMALL target states, equals canonical bad-AUX collision with that target
sum INSIDE the AUX-dependent test. Original moving source D, physical SMALL
legality, numerical seen/birth Nodup, OLD/Fock and both orientations remain. -/
theorem source_original_B398_physical_marked_collision_all_SMALL_exact434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hC xi : ℝ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (xs : GroupState SP sm (J+ell))
    (a b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ss tt : GroupPermFamily (G := SG) (J+ell)) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    (∑ ys : GroupState SP sm (J+ell),
      ∑ aux : SourceBigAux BP J m pat,
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
          cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
          F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434 BP J ell m patterns)
          ss tt) =
    (bigEndpointPairMass (BG := G) (J+ell):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau *
      sourceOriginalB26CanonicalAuxTestError434 P V J ell m hmJ ν
        Q hA hC xi (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss)
        a b sigma tau zeta theta o k
        (fun aux => ∑ ys : GroupState SP sm (J+ell),
          sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
            SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S
            sigma tau ss tt aux) := by
  dsimp only
  let Y := GroupState SP sm (J+ell)
  let Aux := SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
    (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
  let test : Aux → Y → ℂ := fun aux ys =>
    sourceOriginalB26MarkedChronologicalAuxTest434 P J ell m hmJ ν
      SP sm cap sizes hsizes prime q Vs o k F xs ys a b t S
      sigma tau ss tt aux
  let term : Y → Aux → ℂ := fun ys aux =>
    sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm
      (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
      J ell m cap sizes hsizes prime
      (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν) mu V
      (fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t) q Vs zeta theta o k F xs ys a b t S
      (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434
        (fun g => {p : ℕ // p ∈ P g}) J ell m
        (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν)) ss tt
  let canon : (Aux → ℂ) → ℂ := fun f =>
    sourceOriginalB26CanonicalAuxTestError434 P V J ell m hmJ ν
      Q hA hC xi (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss)
      a b sigma tau zeta theta o k f
  let mass : ℂ := (bigEndpointPairMass (BG := G) (J+ell):ℂ) *
    sourceOriginalB26FrozenFreshLaw434 (fun g => {p : ℕ // p ∈ P g})
      J ell m mu (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
      a b sigma tau
  have hfixed (ys : Y) :
      (∑ aux : Aux, term ys aux) =
        mass * canon (fun aux => test aux ys) := by
    exact source_original_B386_marked_chronological_aux_collision_exact434
      P V J ell m hmJ ν Q hA hC xi mu SP sm cap sizes hsizes prime
      q Vs zeta theta o k ho hk F xs ys a b t S sigma tau ss tt
  have hfubini :
      canon (fun aux => ∑ ys : Y, test aux ys) =
        ∑ ys : Y, canon (fun aux => test aux ys) := by
    exact source_original_B397_canonical_aux_error_finite_fubini434
      P V J ell m hmJ ν Q hA hC xi
      (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss)
      a b sigma tau zeta theta o k test
  change (∑ ys : Y, ∑ aux : Aux, term ys aux) =
    mass * canon (fun aux => ∑ ys : Y, test aux ys)
  calc
    _ = ∑ ys : Y, mass * canon (fun aux => test aux ys) := by
      apply Finset.sum_congr rfl
      intro ys hys
      exact hfixed ys
    _ = mass * (∑ ys : Y, canon (fun aux => test aux ys)) := by
      rw [Finset.mul_sum]
    _ = _ := by rw [hfubini]
end Green64Analytic.CorrelationSquare

end

end

/-! ## MarkedPhysicalSmallSumCollisionBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Actual marked chronological B26 collision summed over physical SMALL
states, with the B26 cost once and no SMALL state cardinality. Unlike B388,
we use the ORIGINAL gated SMALL row BEFORE removing the bad AUX tuples. -/
theorem source_original_B399_marked_collision_all_SMALL_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
    (Pmin vmin : ℝ) (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPmin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
    (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖ ≤ B)
    (xs : GroupState SP sm (J+ell))
    (a b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ss tt : GroupPermFamily (G := SG) (J+ell)) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    ‖∑ ys : GroupState SP sm (J+ell),
      ∑ aux : SourceBigAux BP J m pat,
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
          cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
          F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434 BP J ell m patterns)
          ss tt‖ ≤
    bigEndpointPairMass (BG := G) (J+ell) *
      ‖sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau‖ *
      (((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (groupPermutationPairMass (G := SG) (J+ell) *
        (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B)) := by
  dsimp only
  rw [source_original_B398_physical_marked_collision_all_SMALL_exact434
    P V J ell m hmJ ν Q hA hC xi mu SP sm cap sizes hsizes prime
    q Vs zeta theta o k ho hk F xs a b t S sigma tau ss tt]
  have hmass : 0 ≤ bigEndpointPairMass (BG := G) (J+ell) := by
    unfold bigEndpointPairMass
    exact Finset.prod_nonneg (fun _ _ =>
      (permutationPairMass_positive (J+ell)).le)
  rw [norm_mul,norm_mul, Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hmass]
  exact mul_le_mul_of_nonneg_left
    (source_original_B395_B26_aux_collision_after_SMALL_target434
      P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
      Pmin vmin hP hv hV hVmin hPmin SP sm cap sizes hsizes prime
      q Vs hq hq1 hVs zeta theta o k ho
      F B hB hF xs a b t S sigma tau ss tt)
    (mul_nonneg hmass (norm_nonneg _))
end Green64Analytic.CorrelationSquare

end

end

/-! ## FullTargetBigSmallCollisionBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Literal original marked B26 collision after summing both target BIG
active arrays and target SMALL physical states, with no state-cardinality
factor. This uses B399's shift-aware gated SMALL row before collision and
B390's exact original normalized fresh BIG target law. -/
theorem source_original_B400_marked_collision_ALL_target_BIG_SMALL_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
    (Pmin vmin : ℝ) (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPmin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (hmass : ∀ g,∑ p : {p : ℕ // p ∈ P g},mu g p=1)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
    (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
    (xs : GroupState SP sm (J+ell))
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ss tt : GroupPermFamily (G := SG) (J+ell)) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    ‖∑ b : SourceOriginalB26Active434 BP J ell,
      ∑ ys : GroupState SP sm (J+ell),
      ∑ aux : SourceBigAux BP J m pat,
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
          cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
          F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434 BP J ell m patterns)
          ss tt‖ ≤
    bigEndpointPairMass (BG := G) (J+ell) *
      (((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (groupPermutationPairMass (G := SG) (J+ell) *
        (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B)) := by
  dsimp only
  let fac : ℝ := bigEndpointPairMass (BG := G) (J+ell) *
    (((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
       (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (groupPermutationPairMass (G := SG) (J+ell) *
        (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B))
  let T : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell → ℂ :=
    fun b => ∑ ys : GroupState SP sm (J+ell),
      ∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm
          (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
          J ell m cap sizes hsizes prime
          (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν) mu V
          (fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
            Q hA hC xi aux s t) q Vs zeta theta o k F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434
            (fun g => {p : ℕ // p ∈ P g}) J ell m
            (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν)) ss tt
  let law : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell → ℂ :=
    fun b => sourceOriginalB26FrozenFreshLaw434
      (fun g => {p : ℕ // p ∈ P g}) J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) a b sigma tau
  have hbound (b : SourceOriginalB26Active434
      (fun g => {p : ℕ // p ∈ P g}) J ell) :
      ‖T b‖ ≤ ‖law b‖ * fac := by
    convert (source_original_B399_marked_collision_all_SMALL_bound434
      P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
      Pmin vmin hP hv hV hVmin hPmin mu SP sm cap sizes hsizes prime
      q Vs hq hq1 hVs zeta theta o k ho hk
      F B hB hF xs a b t S sigma tau ss tt) using 1 <;>
      dsimp [T,law,fac] <;> ring
  have hlaw : (∑ b : SourceOriginalB26Active434
      (fun g => {p : ℕ // p ∈ P g}) J ell, ‖law b‖) = 1 := by
    exact source_original_B390_original_fresh_law_norm_row_mass434
      (fun g => {p : ℕ // p ∈ P g}) J ell m mu hmu hmass
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) a sigma tau
  change ‖∑ b : SourceOriginalB26Active434
      (fun g => {p : ℕ // p ∈ P g}) J ell, T b‖ ≤ fac
  calc
    _ ≤ ∑ b : SourceOriginalB26Active434
        (fun g => {p : ℕ // p ∈ P g}) J ell, ‖T b‖ := norm_sum_le _ _
    _ ≤ ∑ b : SourceOriginalB26Active434
        (fun g => {p : ℕ // p ∈ P g}) J ell, ‖law b‖ * fac := by
      apply Finset.sum_le_sum
      intro b hb
      exact hbound b
    _ = (∑ b : SourceOriginalB26Active434
          (fun g => {p : ℕ // p ∈ P g}) J ell, ‖law b‖) * fac := by
      rw [Finset.sum_mul]
    _ = fac := by rw [hlaw,one_mul]
end Green64Analytic.CorrelationSquare

end

end

/-! ## FullHaarAllTargetCollisionBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The literal marked collision summed over all BIG/SMALL targets and all
four ORIGINAL source/target BIG/SMALL permutation families; exact normalized
Haar measure removes every permutation/target count, while the shift-aware
SMALL row from B400 is still used. -/
theorem source_original_B401_full_Haar_all_target_collision_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
    (Pmin vmin : ℝ) (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPmin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (hmass : ∀ g,∑ p : {p : ℕ // p ∈ P g},mu g p=1)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
    (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
    (xs : GroupState SP sm (J+ell))
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    ‖∑ sigma : BigGroupPerm (BG := G) (J+ell),
      ∑ tau : BigGroupPerm (BG := G) (J+ell),
      ∑ ss : GroupPermFamily (G := SG) (J+ell),
      ∑ tt : GroupPermFamily (G := SG) (J+ell),
      ∑ b : SourceOriginalB26Active434 BP J ell,
      ∑ ys : GroupState SP sm (J+ell),
      ∑ aux : SourceBigAux BP J m pat,
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
          cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
          F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434 BP J ell m patterns)
          ss tt‖ ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B := by
  dsimp only
  let delta : ℝ :=
    (((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
      (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)
  let row : ℝ := ∏ g : SG, memorySmallRowConstant q (Vs g) ell
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    have hpv : 0 ≤ Pmin*vmin := le_of_lt (mul_pos hP hv)
    positivity
  have hsqrt : Real.sqrt q < 1 := by
    have hsq := Real.sq_sqrt (le_of_lt hq)
    have hn := Real.sqrt_nonneg q
    nlinarith only [hsq,hn,hq1]
  have hden : 0 < 1 - Real.sqrt q := sub_pos.mpr hsqrt
  have hrow : 0 ≤ row := by
    dsimp [row]
    apply Finset.prod_nonneg
    intro g hg
    unfold memorySmallRowConstant
    have hvg := hVs g
    positivity
  have hM : 0 ≤ delta * row * B :=
    mul_nonneg (mul_nonneg hdelta hrow) hB
  have h := source_original_B392_four_Haar_uniform_bound434
    (G := G) (SG := SG) (J+ell)
    (fun sigma tau ss tt =>
      ∑ b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell,
      ∑ ys : GroupState SP sm (J+ell),
      ∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm
          (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
          J ell m cap sizes hsizes prime
          (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν) mu V
          (fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
            Q hA hC xi aux s t)
          q Vs zeta theta o k F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434
            (fun g => {p : ℕ // p ∈ P g}) J ell m
            (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν)) ss tt)
    (delta*row*B) hM (by
      intro sigma tau ss tt
      convert (source_original_B400_marked_collision_ALL_target_BIG_SMALL_bound434
        P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
        Pmin vmin hP hv hV hVmin hPmin mu hmu hmass
        SP sm cap sizes hsizes prime q Vs hq hq1 hVs
        zeta theta o k ho hk F B hB hF xs a t S sigma tau ss tt) using 1 <;>
        dsimp [delta,row] <;> ring)
  simpa only [delta,row] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## CanonicalFrameReindex -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Literal B26 frozen Frame is Unit × AUX × BIG source/target permutations.
Reorder all target BIG, SMALL target and SMALL permutations into the form
consumed by B401. This is an equality of sums, with NO absolute values. -/
theorem source_original_B402_full_frame_to_Haar_reindex434
    {Aux Big Small B Y : Type}
    [Fintype Aux] [Fintype Big] [Fintype Small] [Fintype B] [Fintype Y]
    (f : (Σ _ : Unit, Aux × Big × Big) → B → Y → Small → Small → ℂ) :
    (∑ frame : (Σ _ : Unit, Aux × Big × Big),
      ∑ b : B, ∑ y : Y, ∑ ss : Small, ∑ tt : Small,
        f frame b y ss tt) =
    (∑ sigma : Big, ∑ tau : Big, ∑ ss : Small, ∑ tt : Small,
      ∑ b : B, ∑ y : Y, ∑ aux : Aux,
        f ⟨(), (aux, sigma, tau)⟩ b y ss tt) := by
  classical
  let e : (Aux × Big × Big × B × Y × Small × Small) ≃
      (Big × Big × Small × Small × B × Y × Aux) := {
    toFun := fun ⟨a, sigma, tau, b, y, ss, tt⟩ =>
      ⟨sigma, tau, ss, tt, b, y, a⟩
    invFun := fun ⟨sigma, tau, ss, tt, b, y, a⟩ =>
      ⟨a, sigma, tau, b, y, ss, tt⟩
    left_inv := by
      rintro ⟨a, sigma, tau, b, y, ss, tt⟩
      rfl
    right_inv := by
      rintro ⟨sigma, tau, ss, tt, b, y, a⟩
      rfl
  }
  calc
    _ = ∑ p : Aux × Big × Big × B × Y × Small × Small,
          (fun ⟨a, sigma, tau, b, y, ss, tt⟩ =>
            f ⟨(), (a, sigma, tau)⟩ b y ss tt) p := by
      simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
      simp
    _ = ∑ p : Big × Big × Small × Small × B × Y × Aux,
          (fun ⟨sigma, tau, ss, tt, b, y, a⟩ =>
            f ⟨(), (a, sigma, tau)⟩ b y ss tt) p := by
      apply Fintype.sum_equiv e
      rintro ⟨a, sigma, tau, b, y, ss, tt⟩
      rfl
    _ = _ := by simp only [Fintype.sum_prod_type]
end Green64Analytic.CorrelationSquare

end

end

/-! ## ChronologicalFullCollisionBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Quantitative B26 correction for the ORIGINAL chronological marked full
Frame consumer, not a reindexed replacement. Exact B402 reindex preserves
all AUX, both endpoint permutations, target BIG/SMALL, SMALL Haar and Fock. -/
theorem source_original_B403_chronological_full_frame_collision_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
    (Pmin vmin : ℝ) (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPmin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (hmass : ∀ g,∑ p : {p : ℕ // p ∈ P g},mu g p=1)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
    (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
    (xs : GroupState SP sm (J+ell))
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    ‖∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
      ∑ b : SourceOriginalB26Active434 BP J ell,
      ∑ ys : GroupState SP sm (J+ell),
      ∑ ss : GroupPermFamily (G := SG) (J+ell),
      ∑ tt : GroupPermFamily (G := SG) (J+ell),
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
          cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
          F xs ys a b t S h ss tt‖ ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B := by
  dsimp only
  rw [source_original_B402_full_frame_to_Haar_reindex434]
  exact source_original_B401_full_Haar_all_target_collision_bound434
    P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
    Pmin vmin hP hv hV hVmin hPmin mu hmu hmass
    SP sm cap sizes hsizes prime q Vs hq hq1 hVs
    zeta theta o k ho hk F B hB hF xs a t S
end Green64Analytic.CorrelationSquare

end

end

/-! ## OrbitChronologicalCollisionConsumerBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Quantitative error between the genuine Fock orbit consumer and its
only-auxiliary-ban-removed original chronological comparison, at the same
reachable Fock/OLD/seen representative. No orbit or history count is used. -/
theorem source_original_B404_orbit_marked_CLEAN_vs_unbanned_BOUND434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
    (Pmin vmin : ℝ) (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPmin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (hmu_pos : ∀ g p, 0 < mu g p)
    (hmass : ∀ g,∑ p : {p : ℕ // p ∈ P g},mu g p=1)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
    (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
    (xs : GroupState SP sm (J+ell))
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (hr : sourceOriginalPhysicalReachable434 SP sm
      (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) (J+ell)
      (physicalFockProjection SP sm (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434
          (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
          J ell cap sizes hsizes prime a t)) S) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    ‖fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
        J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q 1 Vs V mu K zeta theta o k st S F)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t)) -
      (∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
        ∑ b : SourceOriginalB26Active434 BP J ell,
        ∑ ys : GroupState SP sm (J+ell),
        ∑ ss : GroupPermFamily (G := SG) (J+ell),
        ∑ tt : GroupPermFamily (G := SG) (J+ell),
          sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
            cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
            F xs ys a b t S h ss tt)‖ ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B := by
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ P g}
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
  let patterns : Unit → SourcePattern G J m := fun _ => pat
  let K : SourcePatternK BP J ell m patterns :=
    fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
      Q hA hC xi aux s t
  let O : ℂ := fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
    (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
      J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q 1 Vs V mu K zeta theta o k st S F)
    (physicalFockProjection SP sm BP bm (J+ell) cap
      (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
        sizes hsizes prime a t))
  let U : ℂ := ∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
    ∑ b : SourceOriginalB26Active434 BP J ell,
    ∑ ys : GroupState SP sm (J+ell),
    ∑ ss : GroupPermFamily (G := SG) (J+ell),
    ∑ tt : GroupPermFamily (G := SG) (J+ell),
      sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
        F xs ys a b t S h ss tt
  let E : ℂ := ∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
    ∑ b : SourceOriginalB26Active434 BP J ell,
    ∑ ys : GroupState SP sm (J+ell),
    ∑ ss : GroupPermFamily (G := SG) (J+ell),
    ∑ tt : GroupPermFamily (G := SG) (J+ell),
      sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
        F xs ys a b t S h ss tt
  have hOrbit : O = U - E := by
    simpa only [O,U,E] using
      (source_original_B389_orbit_MARKED_CLEAN_eq_unbanned_MINUS_collision434
        SP sm BP bm J ell m cap sizes hsizes prime patterns
        mu V K q Vs zeta theta o k hVs hmu_pos F xs a t S hr)
  have hCollision :
      ‖E‖ ≤
        ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
          (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
          (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B := by
    simpa only [E] using
      (source_original_B403_chronological_full_frame_collision_bound434
        P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
        Pmin vmin hP hv hV hVmin hPmin mu hmu hmass
        SP sm cap sizes hsizes prime q Vs hq hq1 hVs
        zeta theta o k ho hk F B hB hF xs a t S)
  have hFinal :
      ‖O - U‖ ≤
        ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
          (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
          (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B := by
    rw [hOrbit, show (U-E)-U = -E by abel, norm_neg]
    exact hCollision
  simpa only [O,U] using hFinal
end Green64Analytic.CorrelationSquare

end

end

