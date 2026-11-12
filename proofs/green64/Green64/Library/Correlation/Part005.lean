module

public import Green64.Library.Weights.Part024
public import Green64.Library.Correlation.Part001
public import Green64.Library.Weights.Part002
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Green64.Library.Analysis.Estimates.Part003
public import Green64.Library.Weights.Part009

@[expose] public section

/-!
# Correlation / Part005

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemoryOriginalCleanDirtySplit -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- No store and no OLD promotion in ANY original big group.
Numerical equality of memory atoms does not affect this predicate. -/
def memorySourceCleanChoice
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x) :
    Prop :=
  ∀ g : BG,
    ((z.2.2.1.bigChoice g).2).1 = ∅ ∧
    ((z.2.2.1.bigChoice g).2).2.1 = ∅
/-- The clean part of the EXACT original oriented E kernel.
The source legality and output-fibre predicates are unchanged. -/
def memoryOriginalCleanEdgeKernel
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℂ :=
  ∑ z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod J ell m
        cap patterns x o k,
    if sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap
          patterns x o k z = y ∧
       memorySourceCleanChoice SP smallMod BP bigMod J ell m cap patterns x z
    then sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m
      cap patterns q rho Vs Vb mu K zeta theta o k x z else 0

/-- Dirty source choices have at least one store or promotion. -/
def memoryOriginalDirtyEdgeKernel
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) : ℂ :=
  ∑ z ∈ sourceOrientedPhysicalChoices SP smallMod BP bigMod J ell m
        cap patterns x o k,
    if sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap
          patterns x o k z = y ∧
       ¬ memorySourceCleanChoice SP smallMod BP bigMod J ell m cap patterns x z
    then sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m
      cap patterns q rho Vs Vb mu K zeta theta o k x z else 0

/-- Exact decomposition of the original kernel, including *all*
zero histories, OLD-index multiplicities, Nu/aux, SMALL/BIG Haar,
and the four independent endpoint permutation sums. -/
theorem memory_original_E_clean_dirty_partition
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    orientedEdgeStateKernel SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k x y =
    memoryOriginalCleanEdgeKernel SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k x y +
    memoryOriginalDirtyEdgeKernel SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k x y := by
  unfold orientedEdgeStateKernel memoryOriginalCleanEdgeKernel
    memoryOriginalDirtyEdgeKernel
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hout : sourceOrientedPhysicalOutput SP smallMod BP bigMod
      J ell m cap patterns x o k z = y
  · by_cases hc :
        memorySourceCleanChoice SP smallMod BP bigMod J ell m cap patterns x z
    · simp [hout, hc]
    · simp [hout, hc]
  · simp [hout]
end Green64FullPhysicalE

end

end

/-! ## PhysicalOrientedSharedCongruence -/

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

/-- Corrected source D ensures every retained BIG shared label
has zero edge displacement in its OWN ZMod(p), even for
arbitrary independent source permutation, orientation and k. -/
theorem oriented_big_shared_displacement_zero
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (sigma : BigGroupPerm (BG := BG) (J + ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J + ell))
    (orientation k : ℤ) (g : BG) (i : Fin (J + ell))
    (hi : i ∈ sourceBigShared J ell m pat g) :
    ((sourceOrientedStep SP smallMod BP bigMod J ell m cap
      pat aux x sigma ss orientation k : ℤ) :
      ZMod (bigMod g ((x.2 g).1 (sigma g i)))) = 0 := by
  have hdvd := oriented_shared_big_prime_dvd_D
    SP smallMod BP bigMod J ell m cap
    pat aux x sigma ss g i hi
  have hzero :
      ((sourceOrientedPhysicalD SP smallMod BP bigMod
        J ell m cap pat aux x sigma ss : ℕ) :
        ZMod (bigMod g ((x.2 g).1 (sigma g i)))) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  unfold sourceOrientedStep
  push_cast
  rw [hzero]
  simp

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedSmallCongruence -/

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

/-- Every SOURCE-ORIENTED SMALL shared mark enters the SAME D as
the BIG shared labels; the whole edge step must vanish modulo
each genuinely shared small prime (not a postulated congruence). -/
theorem oriented_small_shared_displacement_zero
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (sigma : BigGroupPerm (BG := BG) (J + ell))
    (ss : Green64SmallHaar.GroupPermFamily (G := SG) (J + ell))
    (orientation k : ℤ) (g : SG) (i : Fin (J + ell))
    (hi : i ∈ sourceSmallShared J ell g) :
    ((sourceOrientedStep SP smallMod BP bigMod J ell m cap
      pat aux x sigma ss orientation k : ℤ) :
      ZMod (smallMod g
        (Green64SmallHaar.marks (smallMod g) (J + ell)
          (x.1 g) (ss g i)))) = 0 := by
  have hshared :
      smallMod g (Green64SmallHaar.marks (smallMod g)
        (J + ell) (x.1 g) (ss g i)) ∣
      (∏ j ∈ sourceSmallShared J ell g,
        smallMod g (Green64SmallHaar.marks (smallMod g)
          (J + ell) (x.1 g) (ss g j))) :=
    Finset.dvd_prod_of_mem (s := sourceSmallShared J ell g)
      (f := fun j =>
        smallMod g (Green64SmallHaar.marks (smallMod g)
          (J + ell) (x.1 g) (ss g j))) hi
  have hgroups :
      smallMod g (Green64SmallHaar.marks (smallMod g)
        (J + ell) (x.1 g) (ss g i)) ∣
      (∏ gg : SG, ∏ j ∈ sourceSmallShared J ell gg,
        smallMod gg (Green64SmallHaar.marks (smallMod gg)
          (J + ell) (x.1 gg) (ss gg j))) := by
    exact hshared.trans (Finset.dvd_prod_of_mem
      (s := Finset.univ)
      (f := fun gg : SG => ∏ j ∈ sourceSmallShared J ell gg,
        smallMod gg (Green64SmallHaar.marks (smallMod gg)
          (J + ell) (x.1 gg) (ss gg j)))
      (Finset.mem_univ g))
  have hdvd :
      smallMod g (Green64SmallHaar.marks (smallMod g)
        (J + ell) (x.1 g) (ss g i)) ∣
      sourceOrientedPhysicalD SP smallMod BP bigMod
        J ell m cap pat aux x sigma ss := by
    unfold sourceOrientedPhysicalD
    exact dvd_mul_of_dvd_left hgroups _
  have hzero :
      ((sourceOrientedPhysicalD SP smallMod BP bigMod
        J ell m cap pat aux x sigma ss : ℕ) :
        ZMod (smallMod g
          (Green64SmallHaar.marks (smallMod g) (J + ell)
            (x.1 g) (ss g i)))) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  unfold sourceOrientedStep
  push_cast
  rw [hzero]
  simp

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedDivisorReversal -/

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

/-- The original source D is the SAME on reversed oriented
endpoints, provided exactly the physical BIG and SMALL shared-copy
conditions hold. This is the divisor invariance needed for the
literal E adjoint; it is not true if source and target are compared
at unpermuted slots under arbitrary endpoint permutations. -/
theorem source_oriented_D_symmetric_on_shared
    (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (x y : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (sigma tau : BigGroupPerm (BG := BG) (J + ell))
    (ss tt : Green64SmallHaar.GroupPermFamily (G := SG) (J + ell))
    (hbig : ∀ (g : BG) (j : Fin (J + ell)),
      j ∈ sourceBigShared J ell m pat g →
      (x.2 g).1 (sigma g j) = (y.2 g).1 (tau g j))
    (hsmall : ∀ (g : SG) (j : Fin (J + ell)),
      j ∈ sourceSmallShared J ell g →
      Green64SmallHaar.marks (smallMod g) (J + ell)
        (x.1 g) (ss g j) =
      Green64SmallHaar.marks (smallMod g) (J + ell)
        (y.1 g) (tt g j)) :
    sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
      pat aux x sigma ss =
    sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
      pat aux y tau tt := by
  have hS :
      (∏ g : SG, ∏ i ∈ sourceSmallShared J ell g,
        smallMod g (Green64SmallHaar.marks (smallMod g)
          (J + ell) (x.1 g) (ss g i))) =
      (∏ g : SG, ∏ i ∈ sourceSmallShared J ell g,
        smallMod g (Green64SmallHaar.marks (smallMod g)
          (J + ell) (y.1 g) (tt g i))) := by
    apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro i hi
    rw [hsmall g i hi]
  have hB :
      (∏ g : BG,
        (∏ i ∈ sourceBigShared J ell m pat g,
          bigMod g ((x.2 g).1 (sigma g i))) *
        (∏ i : ↥(pat.free g), bigMod g (aux g i))) =
      (∏ g : BG,
        (∏ i ∈ sourceBigShared J ell m pat g,
          bigMod g ((y.2 g).1 (tau g i))) *
        (∏ i : ↥(pat.free g), bigMod g (aux g i))) := by
    apply Finset.prod_congr rfl
    intro g hg
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [hbig g i hi]
  unfold sourceOrientedPhysicalD
  rw [hS, hB]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedLegalDivisorSymmetry -/

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

/-- Actual legal source E witness, without a newly assumed BIG/SMALL
shared-copy hypothesis, has the same FULL source D upon reversal.
The target representative may reorder pending Fock particles. -/
theorem oriented_legal_edge_divisor_reversal
    (x y : FullPhysicalState SP smallMod BP bigMod (J + ell) cap)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (hlegal : sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z)
    (hsmall : y.1 = z.2.2.1.smallTarget)
    (hbig : ∀ g : BG, (y.2 g).1 = (z.2.2.1.bigChoice g).1) :
    sourceOrientedPhysicalD SP smallMod BP bigMod
      J ell m cap (patterns z.1) z.2.1 x
      z.2.2.1.sigmaBig z.2.2.2.1 =
    sourceOrientedPhysicalD SP smallMod BP bigMod
      J ell m cap (patterns z.1) z.2.1 y
      z.2.2.1.tauBig z.2.2.2.2 := by
  apply source_oriented_D_symmetric_on_shared
    SP smallMod BP bigMod J ell m cap
    (patterns z.1) z.2.1 x y z.2.2.1.sigmaBig
    z.2.2.1.tauBig z.2.2.2.1 z.2.2.2.2
  · intro g j hj
    rw [hbig g]
    exact (hlegal.2.2.2.1 g).shared_copy j hj
  · intro g j hj
    rw [hsmall]
    exact (hlegal.2.2.2.2 g).2 j hj

end Green64FullPhysicalE

end

/-! ## PhysicalLiteralPhaseIdentification -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

/-- The corrected finite physical E's actual Kν,D^(iζ) and Fourier
return scalar agrees IDENTICALLY with the published literal row
model. No assumption on the complex K or orientation is added;
both forward and conjugated orientations are covered. -/
theorem oriented_source_K_fourier_eq_literal
    {P G : Type} [Fintype G] {slots : G → ℕ}
    (f : Green64Literal.SourceRow (P := P) G slots) :
    originalEdgeScalar f.kernelK f.zeta f.theta
        f.divisorD f.orientation f.k =
    Green64Literal.orientedKernel f *
      Green64Literal.additivePhase f := by
  unfold originalEdgeScalar originalOrientedKernel originalReturnPhase
    Green64Literal.orientedKernel Green64Literal.additivePhase
  push_cast
  ring

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedSourceCoefficientAudit -/

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

/-- One physical small-Haar endpoint sum with a constant source
complex multiplier factors the multiplier exactly ONCE, with no
extra group factorial. Valid for arbitrary edge congruence tests. -/
theorem small_group_physical_kernel_scalar
    (q : ℝ) (Vsmall : SG → ℝ)
    (shared : (g : SG) → Finset (Fin (J+ell)))
    (step : ℤ) (scalar : ℂ)
    (ss tt : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (source target : Green64SmallHaar.GroupState SP smallMod (J+ell)) :
    Green64SmallHaar.groupPermutedKernel
      SP smallMod (J+ell) q Vsmall shared step
      (fun _ _ => scalar) ss tt source target =
    scalar * Green64SmallHaar.groupPermutedKernel
      SP smallMod (J+ell) q Vsmall shared step
      (fun _ _ => 1) ss tt source target := by
  by_cases h : Green64SmallHaar.groupEdgeAllowedPerm
      SP smallMod (J+ell) shared step ss tt source target
  · simp [Green64SmallHaar.groupPermutedKernel, h]
  · simp [Green64SmallHaar.groupPermutedKernel, h]

/-- Source-exact factorization at ONE actual oriented witness:
original BIG/fock rho, V^-a and fresh mu; small Haar physical scalar;
independent two-sided endpoint symmetrizations; free D mass; ONE
Kν D^(iζ) Fourier phase. The K term cannot be charged twice. -/
theorem physical_source_E_branch_phase_once
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
       J ell m cap patterns x) :
    sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig
      Knu zeta theta orientation k x z =
    let pat := patterns z.1
    let aux := z.2.1
    let b := z.2.2.1
    let ss := z.2.2.2.1
    let tt := z.2.2.2.2
    let D := sourceOrientedPhysicalD SP smallMod BP bigMod
      J ell m cap pat aux x b.sigmaBig ss
    let step := sourceOrientedStep SP smallMod BP bigMod
      J ell m cap pat aux x b.sigmaBig ss orientation k
    (sourceAuxMass BP bigMod J m Vbig pat aux : ℂ) *
      (bigEndpointPairMass (BG := BG) (J+ell) : ℂ) *
      (Green64SmallHaar.groupPermutationPairMass
        (G := SG) (J+ell) : ℂ) *
      (∏ g : BG, orientedBigBranchCoefficient
        (bigMod g) (J+ell) (cap g) (muBig g) (Vbig g) rho
        (x.2 g) (b.bigChoice g).1
        (sourceBigShared J ell m pat g)
        (b.sigmaBig g) (b.tauBig g) step (b.bigChoice g).2) *
      (Green64SmallHaar.groupPermutedKernel
        SP smallMod (J+ell) q Vsmall
        (sourceSmallShared J ell) step
        (fun _ _ => 1) ss tt x.1 b.smallTarget) *
      originalEdgeScalar
        (Knu z.1 aux
          (fun g i => (x.2 g).1 (b.sigmaBig g i))
          (fun g i => (b.bigChoice g).1 (b.tauBig g i)))
        zeta theta D orientation k := by
  classical
  unfold sourceOrientedPhysicalCoefficient
  dsimp only
  rw [small_group_physical_kernel_scalar SP smallMod J ell
    q Vsmall (sourceSmallShared J ell)
    (sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns z.1) z.2.1 x z.2.2.1.sigmaBig z.2.2.2.1
      orientation k)
    (originalEdgeScalar
      (Knu z.1 z.2.1
        (fun g i => (x.2 g).1 (z.2.2.1.sigmaBig g i))
        (fun g i => (z.2.2.1.bigChoice g).1
          (z.2.2.1.tauBig g i)))
      zeta theta
      (sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
        (patterns z.1) z.2.1 x
          z.2.2.1.sigmaBig z.2.2.2.1)
      orientation k)]
  ring

end Green64FullPhysicalE

end

/-! ## PhysicalSourceRealSetTransition -/

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

/-- The complete corrected SOURCE E witness has, in EVERY genuine
big prime group, exact active and Fock pending prime set
conservation with the SAME source pattern, sampled D and delta.
No new model/Markov hypotheses are introduced. -/
theorem full_oriented_source_E_actual_set_conservation
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (orientation k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod
      J ell m cap patterns x)
    (h : sourceOrientedPhysicalLegal SP smallMod BP bigMod
      J ell m cap patterns x orientation k z) (g : BG) :
    let b := z.2.2.1
    let pat := patterns z.1
    let step := sourceOrientedStep SP smallMod BP bigMod
      J ell m cap pat z.2.1 x b.sigmaBig z.2.2.2.1
      orientation k
    ((Finset.univ : Finset (Fin (J+ell))).image
        (b.bigChoice g).1 =
      trueBigSharedValues (bigMod g) (J+ell) (cap g)
        (x.2 g) (sourceBigShared J ell m pat g) (b.sigmaBig g) ∪
      trueBigPromotedValues (bigMod g) (J+ell) (cap g)
        (x.2 g) (b.bigChoice g).2 ∪
      trueBigFreshValues (J+ell) (b.bigChoice g).1
        (sourceBigShared J ell m pat g)
        ((b.bigChoice g).2.2.1) (b.tauBig g)) ∧
    ((((sourceOrientedPhysicalOutput SP smallMod BP bigMod
       J ell m cap patterns x orientation k z).2 g).2).map
       (fun a => a.1)).toFinset =
      trueBigSurvivorValues (bigMod g) (J+ell) (cap g)
        (x.2 g) (b.bigChoice g).2 ∪
      trueBigStoredValues (bigMod g) (J+ell) (cap g)
        (x.2 g) (b.sigmaBig g) (b.bigChoice g).2 := by
  dsimp only
  have hg := h.2.2.2.1 g
  constructor
  · exact real_oriented_E_active_set_conservation
      (bigMod g) (J+ell) (cap g) (x.2 g)
      (z.2.2.1.bigChoice g).1
      (sourceBigShared J ell m (patterns z.1) g)
      (z.2.2.1.sigmaBig g) (z.2.2.1.tauBig g)
      (sourceOrientedPhysicalD SP smallMod BP bigMod
        J ell m cap (patterns z.1) z.2.1 x
        z.2.2.1.sigmaBig z.2.2.2.1)
      (sourceOrientedStep SP smallMod BP bigMod
        J ell m cap (patterns z.1) z.2.1 x
        z.2.2.1.sigmaBig z.2.2.2.1 orientation k)
      (z.2.2.1.bigChoice g).2 hg
  · simpa [sourceOrientedPhysicalOutput, fullPhysicalBranchOutput,
      bigGroupBranchOutput, physicalBranchOutput,
      physicalPendingMultiset, Multiset.map_coe] using
      (real_oriented_E_pending_set_conservation
        (bigMod g) (J+ell) (cap g) (x.2 g)
        (z.2.2.1.sigmaBig g)
        (sourceOrientedStep SP smallMod BP bigMod
          J ell m cap (patterns z.1) z.2.1 x
          z.2.2.1.sigmaBig z.2.2.2.1 orientation k)
        (z.2.2.1.bigChoice g).2)

end Green64FullPhysicalE

end

/-! ## PhysicalSourceSymmetricHilbert -/

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
variable (M : ℕ) (cap : BG → ℕ)

noncomputable instance :
    Fintype (FullPhysicalState SP smallMod BP bigMod M cap) :=
  inferInstance

/-- Actual projection from ordered 1/j! physical Fock representatives
to prime-residue MULTISETS. The small Haar state and every ordered
big active array are unchanged. -/
noncomputable def physicalFockProjection
    (x : FullPhysicalState SP smallMod BP bigMod M cap) :
    FullPhysicalOutput SP smallMod BP bigMod M :=
  (x.1, fun g => ((x.2 g).1,
    Green64Fock.fockMultiset ((x.2 g).2)))
/-- Exactly the finite support of genuine symmetric physical states
at the chosen groupwise Fock cutoffs, retaining equal atoms. -/
noncomputable def physicalFockOrbitSupport :
    Finset (FullPhysicalOutput SP smallMod BP bigMod M) :=
  (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod M cap)).image
    (physicalFockProjection SP smallMod BP bigMod M cap)

/-- The true physical Hilbert mass descended by its ACTUAL fibres,
not an invented uniform kernel or a distinct-prime set measure. -/
noncomputable def physicalOrbitMass
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP smallMod BP bigMod M) : ℝ :=
  ∑ x ∈ (Finset.univ :
      Finset (FullPhysicalState SP smallMod BP bigMod M cap))
      with physicalFockProjection SP smallMod BP bigMod M cap x = y,
    fullPhysicalMass SP smallMod BP bigMod M cap Vsmall muBig x

theorem fullPhysicalMass_pos
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g)
    (hmu : ∀ g p, 0 < muBig g p)
    (x : FullPhysicalState SP smallMod BP bigMod M cap) :
    0 < fullPhysicalMass SP smallMod BP bigMod M cap
      Vsmall muBig x := by
  unfold fullPhysicalMass
  apply mul_pos
  · unfold Green64SmallHaar.groupStateMass
    apply Finset.prod_pos
    intro g hg
    exact Green64SmallHaar.stateMass_positive
      (smallMod g) M (Vsmall g) (hV g)
  · exact bigGroupStateMass_positive BP bigMod M cap muBig hmu x.2
theorem physicalOrbitMass_pos
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g)
    (hmu : ∀ g p, 0 < muBig g p)
    (y : FullPhysicalOutput SP smallMod BP bigMod M)
    (hy : y ∈ physicalFockOrbitSupport SP smallMod BP bigMod M cap) :
    0 < physicalOrbitMass SP smallMod BP bigMod M cap
      Vsmall muBig y := by
  obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hy
  unfold physicalOrbitMass
  apply Finset.sum_pos
  · intro z hz
    exact fullPhysicalMass_pos SP smallMod BP bigMod M cap
      Vsmall muBig hV hmu z
  · exact ⟨x, Finset.mem_filter.mpr ⟨hx,hxy⟩⟩

/-- Genuine finite symmetric physical-Hilbert inner product,
with the source SMALL Haar, BIG active µtilde^M and derived
Fock orbit masses, including every repeated atom multiplicity. -/
noncomputable def physicalSymmetricInner
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (F H : FullPhysicalOutput SP smallMod BP bigMod M → ℂ) : ℂ :=
  ∑ y ∈ physicalFockOrbitSupport SP smallMod BP bigMod M cap,
    (physicalOrbitMass SP smallMod BP bigMod M cap
      Vsmall muBig y : ℂ) * star (F y) * H y

variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)
/-- Orthogonal physical input Fock compression of the SOURCE
all-pattern E row. This retains original coefficients, K, D
sampling, auxiliary ban and ALL OLD injection multiplicities.
It is NOT assumed that the raw E preserves symmetry: that
separate invariance theorem is still required for full identity. -/
noncomputable def physicalSymmetricSourceE
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J + ell))
    (F : FullPhysicalOutput SP smallMod BP bigMod (J + ell) → ℂ) : ℂ :=
  (∑ x ∈ (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod (J + ell) cap))
      with physicalFockProjection SP smallMod BP bigMod
        (J + ell) cap x = y,
    (fullPhysicalMass SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig x : ℂ) *
    fullSourcePhysicalE SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig muBig Knu zeta theta orientation k x F) /
    (physicalOrbitMass SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig y : ℂ)

/-- Exact pairing of the compressed true physical E with an
uncompressed SOURCE branch sum, with ALL input Fock 1/j!
masses and active µtilde^M included exactly once. -/
theorem physicalSymmetricSourceE_pairing
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g)
    (hmu : ∀ g p, 0 < muBig g p)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (orientation k : ℤ)
    (F H : FullPhysicalOutput SP smallMod BP bigMod (J + ell) → ℂ) :
    physicalSymmetricInner SP smallMod BP bigMod (J + ell) cap
      Vsmall muBig F
      (physicalSymmetricSourceE SP smallMod BP bigMod
        cap J ell m patterns q rho Vsmall Vbig muBig
        Knu zeta theta orientation k · H) =
    ∑ x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap,
      (fullPhysicalMass SP smallMod BP bigMod
        (J + ell) cap Vsmall muBig x : ℂ) *
      star (F (physicalFockProjection SP smallMod BP bigMod
        (J + ell) cap x)) *
      fullSourcePhysicalE SP smallMod BP bigMod J ell m cap
        patterns q rho Vsmall Vbig muBig Knu
        zeta theta orientation k x H := by
  classical
  unfold physicalSymmetricInner
  rw [Green64Fock.finite_sum_by_image
    (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod (J + ell) cap))
    (physicalFockProjection SP smallMod BP bigMod (J + ell) cap)
    (fun x => (fullPhysicalMass SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig x : ℂ) *
      star (F (physicalFockProjection SP smallMod BP bigMod
        (J + ell) cap x)) *
      fullSourcePhysicalE SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig muBig Knu
        zeta theta orientation k x H)]
  apply Finset.sum_congr rfl
  intro y hy
  have hpos : (physicalOrbitMass SP smallMod BP bigMod
    (J + ell) cap Vsmall muBig y : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (physicalOrbitMass_pos
      SP smallMod BP bigMod (J + ell) cap
      Vsmall muBig hV hmu y hy))
  change (physicalOrbitMass SP smallMod BP bigMod
      (J + ell) cap Vsmall muBig y : ℂ) * star (F y) *
    ((∑ x ∈ (Finset.univ : Finset
      (FullPhysicalState SP smallMod BP bigMod (J + ell) cap))
      with physicalFockProjection SP smallMod BP bigMod
        (J + ell) cap x = y,
      (fullPhysicalMass SP smallMod BP bigMod
        (J + ell) cap Vsmall muBig x : ℂ) *
      fullSourcePhysicalE SP smallMod BP bigMod J ell m cap
        patterns q rho Vsmall Vbig muBig Knu
        zeta theta orientation k x H) /
      (physicalOrbitMass SP smallMod BP bigMod
        (J + ell) cap Vsmall muBig y : ℂ)) = _
  have hsum :
      (∑ x ∈ (Finset.univ : Finset
        (FullPhysicalState SP smallMod BP bigMod (J + ell) cap))
        with physicalFockProjection SP smallMod BP bigMod
          (J + ell) cap x = y,
        (fullPhysicalMass SP smallMod BP bigMod
          (J + ell) cap Vsmall muBig x : ℂ) *
        star (F (physicalFockProjection SP smallMod BP bigMod
          (J + ell) cap x)) *
        fullSourcePhysicalE SP smallMod BP bigMod J ell m cap
          patterns q rho Vsmall Vbig muBig Knu
          zeta theta orientation k x H) =
      star (F y) *
      (∑ x ∈ (Finset.univ : Finset
        (FullPhysicalState SP smallMod BP bigMod (J + ell) cap))
        with physicalFockProjection SP smallMod BP bigMod
          (J + ell) cap x = y,
        (fullPhysicalMass SP smallMod BP bigMod
          (J + ell) cap Vsmall muBig x : ℂ) *
        fullSourcePhysicalE SP smallMod BP bigMod J ell m cap
          patterns q rho Vsmall Vbig muBig Knu
          zeta theta orientation k x H) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
    ring
  rw [hsum]
  field_simp

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedUniformFockFibres -/

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
variable (M : ℕ) (cap : BG → ℕ)

/-- Genuine source Hilbert masses agree on every physical input
Fock fibre, even with repeated OLD atoms: the full SMALL Haar,
BIG active mu and prime-residue Fock 1/j! weights are retained. -/
theorem physical_full_mass_same_Fock_fibre
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap)
    (hproj : physicalFockProjection SP smallMod BP bigMod M cap x =
      physicalFockProjection SP smallMod BP bigMod M cap y) :
    fullPhysicalMass SP smallMod BP bigMod M cap Vsmall muBig x =
      fullPhysicalMass SP smallMod BP bigMod M cap Vsmall muBig y := by
  have hbig (g : BG) :
      (x.2 g).1 = (y.2 g).1 := by
    exact congrArg (fun o : FullPhysicalOutput SP smallMod BP
      bigMod M => (o.2 g).1) hproj
  have hmem (g : BG) :
      Green64Fock.fockMultiset ((x.2 g).2) =
      Green64Fock.fockMultiset ((y.2 g).2) := by
    exact congrArg (fun o : FullPhysicalOutput SP smallMod BP
      bigMod M => (o.2 g).2) hproj
  have hmass (g : BG) :
      bigStateMass (bigMod g) M (cap g) (muBig g) (x.2 g) =
      bigStateMass (bigMod g) M (cap g) (muBig g) (y.2 g) := by
    unfold bigStateMass
    rw [hbig g]
    exact congrArg (fun r : ℝ => activeMass M (muBig g)
      ((y.2 g).1) * r)
      (Green64Fock.fockMass_multiset_eq
        (Green64Fock.sourceAtomMu (muBig g)) ((x.2 g).2)
        ((y.2 g).2) (hmem g))
  unfold fullPhysicalMass
  unfold bigGroupStateMass
  apply congrArg
  exact Finset.prod_congr rfl (fun g _ => hmass g)

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFibreUniformWeight -/

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
variable (M : ℕ) (cap : BG → ℕ)

/-- Full physical Hilbert input Fock fibre; SMALL Haar and ordered
BIG active slots remain fixed; only OLD Fock order varies. -/
noncomputable def actualPhysicalInputFibre
    (y : FullPhysicalOutput SP smallMod BP bigMod M) :
    Finset (FullPhysicalState SP smallMod BP bigMod M cap) :=
  Finset.univ.filter (fun z =>
    physicalFockProjection SP smallMod BP bigMod M cap z = y)

/-- Every TRUE ordered representative of one symmetric Fock input
fibre has the same Hilbert mass. Its conditional-expectation
coefficient is therefore the reciprocal of the ordered-fibre size. -/
theorem physical_oriented_full_input_fibre_uniform_weight
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g)
    (hmu : ∀ g p, 0 < muBig g p)
    (x : FullPhysicalState SP smallMod BP bigMod M cap) :
    let y := physicalFockProjection SP smallMod BP bigMod M cap x
    let fibre := actualPhysicalInputFibre SP smallMod BP bigMod M cap y
    (fullPhysicalMass SP smallMod BP bigMod M cap Vsmall muBig x : ℂ) /
      (physicalOrbitMass SP smallMod BP bigMod M cap Vsmall muBig y : ℂ) =
      1 / (fibre.card : ℂ) := by
  dsimp only
  let y := physicalFockProjection SP smallMod BP bigMod M cap x
  let S := actualPhysicalInputFibre SP smallMod BP bigMod M cap y
  have hx : x ∈ S := by simp [S, actualPhysicalInputFibre, y]
  have hpos := fullPhysicalMass_pos SP smallMod BP bigMod
    M cap Vsmall muBig hV hmu x
  have hm : (fullPhysicalMass SP smallMod BP bigMod
      M cap Vsmall muBig x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpos)
  have hcp : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hc : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcp)
  have hsum :
      physicalOrbitMass SP smallMod BP bigMod M cap
        Vsmall muBig y =
      S.card * fullPhysicalMass SP smallMod BP bigMod
        M cap Vsmall muBig x := by
    unfold physicalOrbitMass
    change (∑ z ∈ S, fullPhysicalMass SP smallMod BP bigMod
        M cap Vsmall muBig z) = _
    calc
      _ = ∑ z ∈ S, fullPhysicalMass SP smallMod BP bigMod
          M cap Vsmall muBig x := by
        apply Finset.sum_congr rfl
        intro z hz
        exact physical_full_mass_same_Fock_fibre
          SP smallMod BP bigMod M cap Vsmall muBig z x
          (Finset.mem_filter.mp hz).2
      _ = _ := by simp
  change ((fullPhysicalMass SP smallMod BP bigMod M cap
      Vsmall muBig x : ℂ) /
      (physicalOrbitMass SP smallMod BP bigMod M cap
        Vsmall muBig y : ℂ)) = 1 / (S.card : ℂ)
  rw [hsum]
  push_cast
  field_simp [hc, hm]

end Green64FullPhysicalE

end

/-! ## PhysicalOrientedFibreDisintegration -/

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
variable (M : ℕ) (cap : BG → ℕ)

/-- Exact disintegration of an ACTUAL source Hilbert conditional
expectation into inverse images of physically symmetric Fock
states. Each ordered OLD-index representative gets precisely the
inverse cardinality of its genuine weighted Hilbert orbit; no
invented flat probability kernel or premature factorial cancellation. -/
theorem physical_oriented_exact_Fock_fibre_disintegration
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g)
    (hmu : ∀ g p, 0 < muBig g p)
    (y : FullPhysicalOutput SP smallMod BP bigMod M)
    (hy : y ∈ physicalFockOrbitSupport SP smallMod BP bigMod M cap)
    (F : FullPhysicalState SP smallMod BP bigMod M cap → ℂ) :
    let S := actualPhysicalInputFibre SP smallMod BP bigMod M cap y
    (∑ x ∈ S, (fullPhysicalMass SP smallMod BP bigMod M cap
      Vsmall muBig x : ℂ) * F x) /
      (physicalOrbitMass SP smallMod BP bigMod M cap
        Vsmall muBig y : ℂ) =
      (1 / (S.card : ℂ)) * (∑ x ∈ S, F x) := by
  dsimp only
  let S := actualPhysicalInputFibre SP smallMod BP bigMod M cap y
  have hcoeff (x : FullPhysicalState SP smallMod BP bigMod M cap)
      (hx : x ∈ S) :
      (fullPhysicalMass SP smallMod BP bigMod M cap
        Vsmall muBig x : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod M cap
          Vsmall muBig y : ℂ) = 1 / (S.card : ℂ) := by
    have hxy : physicalFockProjection SP smallMod BP bigMod M cap x = y :=
      (Finset.mem_filter.mp hx).2
    have h := physical_oriented_full_input_fibre_uniform_weight
      SP smallMod BP bigMod M cap Vsmall muBig hV hmu x
    dsimp only at h
    simpa only [hxy] using h
  calc
    _ = ∑ x ∈ S,
        ((fullPhysicalMass SP smallMod BP bigMod M cap
          Vsmall muBig x : ℂ) /
          (physicalOrbitMass SP smallMod BP bigMod M cap
            Vsmall muBig y : ℂ)) * F x := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ x ∈ S, (1 / (S.card : ℂ)) * F x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hcoeff x hx]
    _ = (1 / (S.card : ℂ)) * (∑ x ∈ S, F x) := by
      rw [Finset.mul_sum]

end Green64FullPhysicalE

end

/-! ## PhysicalSourceVisitG -/

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
variable (M : ℕ) (cap : BG → ℕ)

/-- Source visit factor: sqrt(q) at BOTH boundary visits 0,N,
and q at all strictly internal visits (including N=0). -/
noncomputable def sourceVisitQ (q : ℝ) (N i : ℕ) : ℝ :=
  if i = 0 ∨ i = N then Real.sqrt q else q

noncomputable def sourceVisitEta (q : ℝ) (N i : ℕ) : ℝ :=
  1 - sourceVisitQ q N i
/-- TRUE source G_(i,g) on finite BIG prime×ZMod(p) Fock memory.
α=-η_i/ρ, χ=q_i/ρ², γ=-η_i V_g/ρ, and NEW births
have λ(p,0)=mu_tilde(p). Every 1/b! is inside fockGhostKernel,
not in this outer all-group tensor and not in the E operator. -/
noncomputable def physicalVisitGKernel
    (q rho : ℝ) (N i : ℕ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap) : ℂ :=
  if x.1 = y.1 ∧ ∀ g : BG, (x.2 g).1 = (y.2 g).1 then
    ∏ g : BG,
      Green64Fock.fockGhostKernel
        (B := cap g)
        (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
        (-((sourceVisitEta q N i : ℝ) : ℂ) / (rho : ℂ))
        (((sourceVisitQ q N i : ℝ) : ℂ) / (rho : ℂ) ^ 2)
        (-((sourceVisitEta q N i : ℝ) : ℂ) *
          (Vbig g : ℂ) / (rho : ℂ))
        (Green64Fock.sourceBirthNu (fun p : BP g => (muBig g p : ℂ)))
        ((x.2 g).2) ((y.2 g).2)
  else 0

/-- The source physical visit row changes ONLY big pending Fock
particles. Small Haar residues/marks and all big active labels
are physically unchanged; independent group ghost operations
have their genuine OLD-zero and fresh-birth enumeration. -/
noncomputable def physicalVisitGRow
    (q rho : ℝ) (N i : ℕ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (F : FullPhysicalState SP smallMod BP bigMod M cap → ℂ)
    (x : FullPhysicalState SP smallMod BP bigMod M cap) : ℂ :=
  ∑ y : FullPhysicalState SP smallMod BP bigMod M cap,
    physicalVisitGKernel SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y * F y
/-- The full ordered source Hilbert pairing. BIG active µtilde^M,
SMALL Haar and each BIG Fock sector λ^j/j! are all included
exactly once, via fullPhysicalMass. -/
noncomputable def physicalOrderedInner
    (Vsmall : SG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (F H : FullPhysicalState SP smallMod BP bigMod M cap → ℂ) : ℂ :=
  ∑ x : FullPhysicalState SP smallMod BP bigMod M cap,
    (fullPhysicalMass SP smallMod BP bigMod M cap
      Vsmall muBig x : ℂ) * star (F x) * H x

noncomputable def physicalVisitGAdjointRow
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (F : FullPhysicalState SP smallMod BP bigMod M cap → ℂ)
    (y : FullPhysicalState SP smallMod BP bigMod M cap) : ℂ :=
  ∑ x : FullPhysicalState SP smallMod BP bigMod M cap,
    ((fullPhysicalMass SP smallMod BP bigMod M cap
        Vsmall muBig x : ℂ) /
      (fullPhysicalMass SP smallMod BP bigMod M cap
        Vsmall muBig y : ℂ)) *
    star (physicalVisitGKernel SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y) * F x

/-- Actual all-group source G_i and G_i* are Hilbert adjoints
on finite physical SMALL Haar × BIG active × 1/j! Fock states.
This instantiates the RAW product ghost kernel, not a generic
postulated stochastic transition operator. -/
theorem physicalVisitG_adjoint
    (q rho : ℝ) (N i : ℕ)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (hV : ∀ g, 0 < Vsmall g)
    (hmu : ∀ g p, 0 < muBig g p)
    (F H : FullPhysicalState SP smallMod BP bigMod M cap → ℂ) :
    physicalOrderedInner SP smallMod BP bigMod M cap
      Vsmall muBig F
      (physicalVisitGRow SP smallMod BP bigMod M cap
        q rho N i Vbig muBig H) =
    physicalOrderedInner SP smallMod BP bigMod M cap
      Vsmall muBig
      (physicalVisitGAdjointRow SP smallMod BP bigMod M cap
        q rho N i Vsmall Vbig muBig F) H := by
  simpa [physicalOrderedInner, physicalVisitGRow,
    physicalVisitGAdjointRow] using
    (Green64Fock.finite_weighted_kernel_adjoint_identity
      (fullPhysicalMass SP smallMod BP bigMod M cap Vsmall muBig)
      (fun s => ne_of_gt (fullPhysicalMass_pos
        SP smallMod BP bigMod M cap Vsmall muBig hV hmu s))
      (physicalVisitGKernel SP smallMod BP bigMod M cap
        q rho N i Vbig muBig) F H)

end Green64FullPhysicalE

end

/-! ## MemoryIndTrueHalfEndpointQ -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- The REAL independent Markov source BIG q-kernel charges
sqrt(q) once at both ends of each step. For N=n+1>0 those
charges are EXACTLY sourceVisitQ at each of its N+1 actual visits:
sqrt(q) at t=0,t=N, q in the interior. There is no lost
terminal half-step or duplicated BIG damping, including zero q. -/
theorem memory_ind_true_half_endpoint_sourceVisitQ
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (e : ℕ → ℕ) :
    (∏ i ∈ Finset.range (n+1),
      (Real.sqrt q)^(e i) * (Real.sqrt q)^(e (i+1))) =
    ∏ t ∈ Finset.range (n+2), (sourceVisitQ q (n+1) t)^(e t) := by
  calc
    _ = ∏ t ∈ Finset.range (n+2),
      if t=0 ∨ t=n+1 then (Real.sqrt q)^(e t)
      else (Real.sqrt q)^(e t) * (Real.sqrt q)^(e t) := by
        exact memory_ind_adjacent_endpoint_product
          (fun t => (Real.sqrt q)^(e t)) n
    _ = _ := by
      apply Finset.prod_congr rfl
      intro t ht
      by_cases hb : t=0 ∨ t=n+1
      · simp only [hb, if_true]
        unfold sourceVisitQ
        simp only [hb, if_true]
      · simp only [hb, if_false]
        unfold sourceVisitQ
        rw [if_neg hb]
        rw [← mul_pow, Real.mul_self_sqrt hq]
end Green64FullPhysicalE

end

end

/-! ## MemoryIndBIGPairSourceQ -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- The COMPLETE ORIGINAL independent BIG physical group endpoint
q-damping across actual successive Markov states (N=n+1>0 rows)
equals the genuine source BIG visit q_t product with two correct
sqrt(q) boundary weights, all interior q weights, and all groups.
Works for any original sequence of valid state carriers, including
inactive primes, without a kernel positivity or Markov independence
assumption. This is a REAL mathematical identity needed to match
the source independent kernel to the frozen prime Haar expansion. -/
theorem memory_ind_BIG_all_pairs_eq_source_visit_q
    (q : ℝ) (hq : 0 ≤ q) (n M : ℕ)
    (S : ℕ → Green64SmallHaar.GroupState BP bigMod M) :
    (∏ i ∈ Finset.range (n+1), ∏ g : BG,
      (Green64SmallHaar.endpointDamping (bigMod g) M q (S i g) *
       Green64SmallHaar.endpointDamping (bigMod g) M q (S (i+1) g) : ℝ)) =
    ∏ t ∈ Finset.range (n+2), ∏ g : BG,
      (sourceVisitQ q (n+1) t) ^
        (Green64SmallHaar.omega (bigMod g)
           (Green64SmallHaar.residues (bigMod g) M (S t g))-M) := by
  classical
  let e (g : BG) (t : ℕ) : ℕ :=
    Green64SmallHaar.omega (bigMod g)
      (Green64SmallHaar.residues (bigMod g) M (S t g))-M
  calc
    _ = (∏ g : BG, ∏ i ∈ Finset.range (n+1),
          (Real.sqrt q) ^ (e g i) * (Real.sqrt q) ^ (e g (i+1))) := by
          rw [Finset.prod_comm]
          apply Finset.prod_congr rfl
          intro g hg
          apply Finset.prod_congr rfl
          intro i hi
          rfl
    _ = (∏ g : BG, ∏ t ∈ Finset.range (n+2),
          (sourceVisitQ q (n+1) t) ^ (e g t)) := by
          apply Finset.prod_congr rfl
          intro g hg
          exact memory_ind_true_half_endpoint_sourceVisitQ q hq n (e g)
    _ = _ := by
          rw [Finset.prod_comm]
end Green64FullPhysicalE

end

end

/-! ## MemoryIndBIGFinitePathSourceQ -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- EXACT Fin-indexed form of the ORIGINAL independent BIG double
endpoint q identity. Given the ACTUAL finite Markov state array at
each visit, product over N=n+1 original oriented transitions of
source+target endpoint damping equals product over all N+1 visits
of the physical sourceVisitQ factors, with correct sqrt(q) on both
endpoints. Original ordered valid zero-mark states untouched. -/
theorem memory_ind_BIG_Fin_path_pairs_to_source_q
    (q : ℝ) (hq : 0 ≤ q) (n M : ℕ)
    (states : Fin (n+2) → Green64SmallHaar.GroupState BP bigMod M) :
    (∏ i : Fin (n+1), ∏ g : BG,
      (Green64SmallHaar.endpointDamping (bigMod g) M q
        (states i.castSucc g) *
       Green64SmallHaar.endpointDamping (bigMod g) M q
        (states i.succ g) : ℝ)) =
    ∏ t : Fin (n+2), ∏ g : BG,
      (sourceVisitQ q (n+1) t.val) ^
        (Green64SmallHaar.omega (bigMod g)
          (Green64SmallHaar.residues (bigMod g) M
            (states t g))-M) := by
  let S (t : ℕ) : Green64SmallHaar.GroupState BP bigMod M :=
    states ⟨t % (n+2), Nat.mod_lt _ (by omega)⟩
  have hs (t : ℕ) (ht : t < n+2) :
      S t = states ⟨t,ht⟩ := by
    simp only [S, Nat.mod_eq_of_lt ht]
  have hleft :
      (∏ i : Fin (n+1), ∏ g : BG,
        (Green64SmallHaar.endpointDamping (bigMod g) M q
          (states i.castSucc g) *
         Green64SmallHaar.endpointDamping (bigMod g) M q
          (states i.succ g) : ℝ)) =
      (∏ i ∈ Finset.range (n+1), ∏ g : BG,
        Green64SmallHaar.endpointDamping (bigMod g) M q (S i g) *
        Green64SmallHaar.endpointDamping (bigMod g) M q
          (S (i+1) g)) := by
    rw [Finset.prod_fin_eq_prod_range]
    apply Finset.prod_congr rfl
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi)]
    have hil : i<n+1 := Finset.mem_range.mp hi
    have hs0 := hs i (by omega)
    have hs1 := hs (i+1) (by omega)
    simp only [hs0, hs1]
    rfl
  have hright :
      (∏ t : Fin (n+2), ∏ g : BG,
        (sourceVisitQ q (n+1) t.val) ^
          (Green64SmallHaar.omega (bigMod g)
            (Green64SmallHaar.residues (bigMod g) M
              (states t g))-M)) =
      (∏ t ∈ Finset.range (n+2), ∏ g : BG,
        (sourceVisitQ q (n+1) t) ^
          (Green64SmallHaar.omega (bigMod g)
            (Green64SmallHaar.residues (bigMod g) M
              (S t g))-M)) := by
    rw [Finset.prod_fin_eq_prod_range]
    apply Finset.prod_congr rfl
    intro t ht
    rw [dif_pos (Finset.mem_range.mp ht)]
    rw [hs t (Finset.mem_range.mp ht)]
  calc
    _ = (∏ i ∈ Finset.range (n+1), ∏ g : BG,
        Green64SmallHaar.endpointDamping (bigMod g) M q (S i g) *
        Green64SmallHaar.endpointDamping (bigMod g) M q
          (S (i+1) g)) := hleft
    _ = (∏ t ∈ Finset.range (n+2), ∏ g : BG,
        (sourceVisitQ q (n+1) t) ^
          (Green64SmallHaar.omega (bigMod g)
            (Green64SmallHaar.residues (bigMod g) M (S t g))-M)) :=
          memory_ind_BIG_all_pairs_eq_source_visit_q BP bigMod q hq n M S
    _ = _ := hright.symm
end Green64FullPhysicalE

end

end

/-! ## MemoryIndBIGFinitePathComplexQ -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- Source BIG physical endpoint q equality in the ORIGINAL complex
Hilbert/Fourier scalar field ℂ. This explicit cast avoids invoking a
huge global norm_cast search inside original dependent Nu/aux path
fibre proofs, while keeping all BIG group Haar factors unchanged. -/
theorem memory_ind_BIG_Fin_pair_sourceQ_complex
    (q : ℝ) (hq : 0 ≤ q) (n M : ℕ)
    (states : Fin (n+2) → Green64SmallHaar.GroupState BP bigMod M) :
    (∏ i : Fin (n+1), ∏ g : BG,
      ((Green64SmallHaar.endpointDamping (bigMod g) M q
        (states i.castSucc g) *
        Green64SmallHaar.endpointDamping (bigMod g) M q
          (states i.succ g) : ℝ) : ℂ)) =
    ∏ t : Fin (n+2), ∏ g : BG,
      (((sourceVisitQ q (n+1) t.val) ^
        (Green64SmallHaar.omega (bigMod g)
          (Green64SmallHaar.residues (bigMod g) M (states t g))-M) : ℝ) : ℂ) := by
  have hr := memory_ind_BIG_Fin_path_pairs_to_source_q
    BP bigMod q hq n M states
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hr
  simpa only [Complex.ofReal_prod] using hc
end Green64FullPhysicalE

end

end

/-! ## PhysicalGhostWitness -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {U : Type} [Fintype U] [DecidableEq U]

/-- A source G witness is an OLD zero-subset, one birth count
0≤b≤B and b independently sampled atoms. This preserves the
complete fresh-atom list BEFORE summing the G kernel. -/
abbrev GhostWitnessChoice (old : List U)
    (atZero : U → Prop) [DecidablePred atZero] (B : ℕ) :=
  Σ A : {A : Finset (Fin old.length) //
      A ∈ (Green64MemoryGhostOp.zeroOld old atZero).powerset},
    Σ b : Fin (B + 1), Fin b.val → U

noncomputable instance (old : List U)
    (atZero : U → Prop) [DecidablePred atZero] (B : ℕ) :
    Fintype (GhostWitnessChoice old atZero B) := inferInstance

/-- One indexed, source-legal G_i witness contributes its true
OLD-zero damping, 1/b! independent births, and exact output list.
Zero weights may occur, but no nonzero history is quotiented away. -/
noncomputable def ghostWitnessTerm
    (old next : List U) (atZero : U → Prop)
    [DecidablePred atZero] (B : ℕ)
    (alpha chi gamma : ℂ) (nu : U → ℂ)
    (c : GhostWitnessChoice old atZero B) : ℂ :=
  if Green64MemoryGhostOp.afterGhost old c.1.1 c.2.2 = next then
    Green64MemoryGhostOp.sourceGhostTerm old atZero
      c.1.1 c.2.2 alpha chi gamma nu
  else 0

noncomputable def ghostWitnessKernel
    (old next : List U) (atZero : U → Prop)
    [DecidablePred atZero] (B : ℕ)
    (alpha chi gamma : ℂ) (nu : U → ℂ) : ℂ :=
  ∑ c : GhostWitnessChoice old atZero B,
    ghostWitnessTerm old next atZero B alpha chi gamma nu c

/-- NONTRIVIAL source G disintegration: the expanded sum over
witnesses carrying their exact fresh lists equals the original
raw finiteGhostKernel, including 1/b!, OLD zero subsets and
all repeated target-atom multiplicities. This is the bridge
required before imposing one GLOBAL path birth indicator. -/
theorem ghostWitnessKernel_eq_raw
    (old next : List U) (atZero : U → Prop)
    [DecidablePred atZero] (B : ℕ)
    (alpha chi gamma : ℂ) (nu : U → ℂ) :
    ghostWitnessKernel old next atZero B alpha chi gamma nu =
    Green64MemoryGhostOp.finiteGhostKernel old next atZero
      B alpha chi gamma nu := by
  let S := (Green64MemoryGhostOp.zeroOld old atZero).powerset
  let w := fun (A : Finset (Fin old.length)) (b : ℕ) =>
      ∑ fresh : Fin b → U,
        if Green64MemoryGhostOp.afterGhost old A fresh = next then
          Green64MemoryGhostOp.sourceGhostTerm old atZero
            A fresh alpha chi gamma nu
        else 0
  have hsigma :
      ghostWitnessKernel old next atZero B alpha chi gamma nu =
      ∑ A : {A : Finset (Fin old.length) // A ∈ S},
        ∑ b : Fin (B+1), w A.1 b.1 := by
    unfold ghostWitnessKernel
    simp only [Fintype.sum_sigma]
    rfl
  rw [hsigma]
  have hA :
      (∑ A : {A : Finset (Fin old.length) // A ∈ S},
        ∑ b : Fin (B+1), w A.1 b.1) =
      ∑ A ∈ S, ∑ b : Fin (B+1), w A b.1 := by
    symm
    exact Finset.sum_subtype S (fun A => Iff.rfl)
      (fun A => ∑ b : Fin (B+1), w A b.1)
  rw [hA]
  have hb (A : Finset (Fin old.length)) :
      (∑ b : Fin (B+1), w A b.1) =
      ∑ b ∈ Finset.range (B+1), w A b :=
    Fin.sum_univ_eq_sum_range (w A) (B+1)
  simp_rw [hb]
  rfl

end Green64FullPhysicalE

end

/-! ## PhysicalGhostGroupWitness -/

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
variable (M : ℕ) (cap : BG → ℕ)

/-- One independently indexed, TRUE source ghost G witness for
every BIG group. No endpoint K/D inputs and no abstract kernel
can choose its OLD zero subset or its fresh atom list. -/
abbrev FullGhostWitness
    (x : FullPhysicalState SP smallMod BP bigMod M cap) :=
  (g : BG) →
    GhostWitnessChoice
      (Green64Fock.fockToList ((x.2 g).2))
      (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
      (cap g)

noncomputable instance
    (x : FullPhysicalState SP smallMod BP bigMod M cap) :
    Fintype (FullGhostWitness SP smallMod BP bigMod M cap x) :=
  inferInstance

/-- The EXACT primitive G_i branch term on the complete physical
SMALL Haar × BIG active × OLD/FRESH group Fock states. The
small/active coordinates are fixed, each group carries one original
source G witness and the coefficients multiply with NO cross-group
extra factorial. -/
noncomputable def physicalGBranchTerm
    (q rho : ℝ) (N i : ℕ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x) : ℂ :=
  if x.1 = y.1 ∧ ∀ g : BG, (x.2 g).1 = (y.2 g).1 then
    ∏ g : BG,
      ghostWitnessTerm
        (Green64Fock.fockToList ((x.2 g).2))
        (Green64Fock.fockToList ((y.2 g).2))
        (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
        (cap g)
        (-((sourceVisitEta q N i : ℝ) : ℂ) / (rho : ℂ))
        (((sourceVisitQ q N i : ℝ) : ℂ) / (rho : ℂ) ^ 2)
        (-((sourceVisitEta q N i : ℝ) : ℂ) *
          (Vbig g : ℂ) / (rho : ℂ))
        (Green64Fock.sourceBirthNu
          (fun p : BP g => (muBig g p : ℂ)))
        (c g)
  else 0

/-- The joint G_i kernel is a sum of ORIGINAL physical ghost
witnesses. Each witness retains the ordered sampled birth list,
so a global path indicator can be inserted without inventing
a Markov transition for the already aggregated output. -/
noncomputable def physicalGWitnessKernel
    (q rho : ℝ) (N i : ℕ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap) : ℂ :=
  ∑ c : FullGhostWitness SP smallMod BP bigMod M cap x,
    physicalGBranchTerm SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y c

/-- Full group-tensor source G_i WITNESS disintegration. This
kernel equality is proved by exact finite dependent product-sum,
not by postulating equality of path laws. Equal fresh targets
can come from different OLD subsets and survive with multiplicity. -/
theorem physicalGWitnessKernel_eq_source
    (q rho : ℝ) (N i : ℕ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap) :
    physicalGWitnessKernel SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y =
    physicalVisitGKernel SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y := by
  classical
  by_cases hf : x.1 = y.1 ∧ ∀ g : BG, (x.2 g).1 = (y.2 g).1
  · unfold physicalGWitnessKernel physicalGBranchTerm physicalVisitGKernel
    simp only [if_pos hf]
    let factor : (g : BG) →
        GhostWitnessChoice
          (Green64Fock.fockToList ((x.2 g).2))
          (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
          (cap g) → ℂ :=
      fun g w =>
        ghostWitnessTerm
          (Green64Fock.fockToList ((x.2 g).2))
          (Green64Fock.fockToList ((y.2 g).2))
          (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
          (cap g)
          (-((sourceVisitEta q N i : ℝ) : ℂ) / (rho : ℂ))
          (((sourceVisitQ q N i : ℝ) : ℂ) / (rho : ℂ) ^ 2)
          (-((sourceVisitEta q N i : ℝ) : ℂ) *
            (Vbig g : ℂ) / (rho : ℂ))
          (Green64Fock.sourceBirthNu
            (fun p : BP g => (muBig g p : ℂ)))
          w
    change (∑ c : FullGhostWitness SP smallMod BP bigMod M cap x,
        ∏ g : BG, factor g (c g)) =
      ∏ g : BG,
        Green64Fock.fockGhostKernel
          (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
          (-((sourceVisitEta q N i : ℝ) : ℂ) / (rho : ℂ))
          (((sourceVisitQ q N i : ℝ) : ℂ) / (rho : ℂ) ^ 2)
          (-((sourceVisitEta q N i : ℝ) : ℂ) *
            (Vbig g : ℂ) / (rho : ℂ))
          (Green64Fock.sourceBirthNu
            (fun p : BP g => (muBig g p : ℂ)))
          ((x.2 g).2) ((y.2 g).2)
    rw [← Fintype.prod_sum factor]
    apply Finset.prod_congr rfl
    intro g hg
    exact ghostWitnessKernel_eq_raw
      (Green64Fock.fockToList ((x.2 g).2))
      (Green64Fock.fockToList ((y.2 g).2))
      (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
      (cap g)
      (-((sourceVisitEta q N i : ℝ) : ℂ) / (rho : ℂ))
      (((sourceVisitQ q N i : ℝ) : ℂ) / (rho : ℂ) ^ 2)
      (-((sourceVisitEta q N i : ℝ) : ℂ) *
        (Vbig g : ℂ) / (rho : ℂ))
      (Green64Fock.sourceBirthNu
        (fun p : BP g => (muBig g p : ℂ)))
  · simp [physicalGWitnessKernel,physicalGBranchTerm,
      physicalVisitGKernel,hf]

end Green64FullPhysicalE

end

/-! ## PhysicalGhostMarkedG -/

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
variable (M : ℕ) (cap : BG → ℕ)

/-- Exactly the numerical prime VALUES born inside one G_i
joint witness, in independent group/fresh-slot order. OLD
deletions contribute no new births; groupwise duplicates survive
until this GLOBAL test, not in the original G operator. -/
noncomputable def physicalGhostFreshBirths
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x) : List ℕ :=
  (Finset.univ : Finset BG).toList.flatMap (fun g =>
    (List.ofFn ((c g).2.2)).map (fun z => bigMod g z.1))

def physicalGhostBatchEligible
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (seen : Finset ℕ)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x) : Prop :=
  (physicalGhostFreshBirths SP smallMod BP bigMod M cap x c).Nodup ∧
    Disjoint seen
      (physicalGhostFreshBirths SP smallMod BP bigMod M cap x c).toFinset

/-- Literal primitive all-group G_i expansion retaining all
individual OLD-zero/fresh-atom witnesses and the global seen set,
but without yet filtering. Every real source branch keeps its
multiplicity even when endpoints or birth values coincide. -/
noncomputable def physicalGUnrestrictedWitnessRow
    (q rho : ℝ) (N i : ℕ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod M →
      Finset ℕ → ℂ) : ℂ :=
  ∑ y : FullPhysicalState SP smallMod BP bigMod M cap,
    ∑ c : FullGhostWitness SP smallMod BP bigMod M cap x,
      physicalGBranchTerm SP smallMod BP bigMod M cap
        q rho N i Vbig muBig x y c *
      F (physicalFockProjection SP smallMod BP bigMod M cap y)
        (seen ∪ (physicalGhostFreshBirths
          SP smallMod BP bigMod M cap x c).toFinset)

/-- Requiring a fresh G batch is the exact GLOBAL distinct-birth
indicator inserted at the raw witness stage; the primitive
G source coefficient itself is never modified. -/
noncomputable def physicalGBirthMarkedRow
    (q rho : ℝ) (N i : ℕ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod M →
      Finset ℕ → ℂ) : ℂ :=
  ∑ y : FullPhysicalState SP smallMod BP bigMod M cap,
    ∑ c : FullGhostWitness SP smallMod BP bigMod M cap x,
      if physicalGhostBatchEligible SP smallMod BP bigMod M cap
          x seen c then
        physicalGBranchTerm SP smallMod BP bigMod M cap
          q rho N i Vbig muBig x y c *
        F (physicalFockProjection SP smallMod BP bigMod M cap y)
          (seen ∪ (physicalGhostFreshBirths
            SP smallMod BP bigMod M cap x c).toFinset)
      else 0

/-- CRITICAL exact bridge: forgetting the seen-history data after
expanding the original G_i witnesses recovers the true physical
all-group source G_i, not a surrogate transition kernel.
The only difference in the marked version is the actual GLOBAL
distinct-birth indicator on the retained NEW prime-value batch. -/
theorem physicalGUnrestricted_forget_births
    (q rho : ℝ) (N i : ℕ)
    (Vbig : BG → ℝ) (muBig : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP smallMod BP bigMod M cap)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod M → ℂ) :
    physicalGUnrestrictedWitnessRow SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x seen (fun y _ => F y) =
    physicalVisitGRow SP smallMod BP bigMod M cap
      q rho N i Vbig muBig
      (fun y => F (physicalFockProjection SP smallMod BP bigMod M cap y))
      x := by
  unfold physicalGUnrestrictedWitnessRow physicalVisitGRow
  apply Finset.sum_congr rfl
  intro y hy
  simp only
  rw [← Finset.sum_mul]
  exact congrArg (fun t : ℂ =>
    t * F (physicalFockProjection SP smallMod BP bigMod M cap y))
    (physicalGWitnessKernel_eq_source
      SP smallMod BP bigMod M cap q rho N i Vbig muBig x y)

end Green64FullPhysicalE

end

/-! ## PhysicalGhostPendingUniqueness -/

section

open Classical
open scoped BigOperators

namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]

/-- The TRUE G_i old-index deletion, then ordered fresh ghost births,
preserves distinct numerical prime labels in the pending list.
The ambient Fock space still supports repetitions; only the
distinct-birth compatible subpaths have this invariant. -/
theorem original_ghost_afterGhost_prime_nodup
    (old : List (Green64Fock.Atom P modulus))
    (A : Finset (Fin old.length))
    {b : ℕ} (fresh : Fin b → Green64Fock.Atom P modulus)
    (hOld : (old.map fun z => z.1).Nodup)
    (hFresh : ((List.ofFn fresh).map fun z => z.1).Nodup)
    (hDisj : ∀ a ∈ old.map (fun z => z.1),
      ∀ v ∈ (List.ofFn fresh).map (fun z => z.1), a ≠ v) :
    ((Green64MemoryGhostOp.afterGhost old A fresh).map
      (fun z => z.1)).Nodup := by
  classical
  let kept := (List.finRange old.length).filter (fun i => i ∉ A)
  have hGet : Function.Injective
      (fun i : Fin old.length => (old.get i).1) := by
    intro i j he
    let ii : Fin (old.map (fun z => z.1)).length :=
      ⟨i.val, by simpa using i.isLt⟩
    let jj : Fin (old.map (fun z => z.1)).length :=
      ⟨j.val, by simpa using j.isLt⟩
    have hEq : (old.map (fun z => z.1)).get ii =
        (old.map (fun z => z.1)).get jj := by
      simpa [ii, jj] using he
    have hij := (List.nodup_iff_injective_get.mp hOld) hEq
    have hval : ii.val = jj.val :=
      congrArg (fun t : Fin (old.map (fun z => z.1)).length => t.val) hij
    exact Fin.ext (by simpa [ii, jj] using hval)
  have hKeep :
      (kept.map (fun i : Fin old.length => (old.get i).1)).Nodup := by
    apply List.Nodup.map hGet
    simpa [kept] using (List.nodup_finRange old.length).filter
      (fun i => i ∉ A)
  have hKeepOld (v : P)
      (hv : v ∈ kept.map (fun i : Fin old.length => (old.get i).1)) :
      v ∈ old.map (fun z => z.1) := by
    rcases List.mem_map.mp hv with ⟨i,hi,rfl⟩
    exact List.mem_map.mpr
      ⟨old.get i, List.get_mem old i, rfl⟩
  have hSep :
      ∀ a ∈ kept.map (fun i : Fin old.length => (old.get i).1),
      ∀ v ∈ (List.ofFn fresh).map (fun z => z.1), a ≠ v := by
    intro a ha v hv
    exact hDisj a (hKeepOld a ha) v hv
  have hFull :
      ((kept.map (fun i : Fin old.length => (old.get i).1)) ++
        ((List.ofFn fresh).map (fun z => z.1))).Nodup :=
    (List.nodup_append).mpr ⟨hKeep, hFresh, hSep⟩
  simpa [Green64MemoryGhostOp.afterGhost, kept,
    List.map_append, List.map_map, Function.comp_def] using hFull

end Green64FullPhysicalE

end

/-! ## PhysicalGhostWitnessOperational -/

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
variable (M : ℕ) (cap : BG → ℕ)

/-- A NONZERO actual G_i physical witness MUST use exactly the
source's OLD-zero deletion followed by its own fresh ghost atoms.
This is not a stipulated transition: it follows from the literal
source ghostWitnessTerm in the original G_i coefficient. -/
theorem physical_nonzero_ghost_witness_is_operational
    (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod M cap)
    (c : FullGhostWitness SP smallMod BP bigMod M cap x)
    (hterm : physicalGBranchTerm SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y c ≠ 0) :
    (x.1 = y.1 ∧ ∀ g : BG, (x.2 g).1 = (y.2 g).1) ∧
      ∀ g : BG,
        Green64MemoryGhostOp.afterGhost
          (Green64Fock.fockToList ((x.2 g).2))
          (c g).1.1 (c g).2.2 =
        Green64Fock.fockToList ((y.2 g).2) := by
  have hstate :
      x.1 = y.1 ∧ ∀ g : BG, (x.2 g).1 = (y.2 g).1 := by
    by_contra h
    have heq : physicalGBranchTerm SP smallMod BP bigMod M cap
      q rho N i Vbig muBig x y c = 0 := by
      simp [physicalGBranchTerm, h]
    exact hterm heq
  have hprod :
      (∏ g : BG, ghostWitnessTerm
        (Green64Fock.fockToList ((x.2 g).2))
        (Green64Fock.fockToList ((y.2 g).2))
        (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
        (cap g)
        (-((sourceVisitEta q N i : ℝ) : ℂ) / (rho : ℂ))
        (((sourceVisitQ q N i : ℝ) : ℂ) / (rho : ℂ)^2)
        (-((sourceVisitEta q N i : ℝ) : ℂ) *
          (Vbig g : ℂ) / (rho : ℂ))
        (Green64Fock.sourceBirthNu
          (fun p : BP g => (muBig g p : ℂ)))
        (c g)) ≠ 0 := by
    simpa only [physicalGBranchTerm, if_pos hstate] using hterm
  refine ⟨hstate, ?_⟩
  intro g
  have hfactor := (Finset.prod_ne_zero_iff.mp hprod) g
    (Finset.mem_univ g)
  by_contra hwrong
  have hzero :
      ghostWitnessTerm
        (Green64Fock.fockToList ((x.2 g).2))
        (Green64Fock.fockToList ((y.2 g).2))
        (fun z : Green64Fock.Atom (BP g) (bigMod g) => z.2 = 0)
        (cap g)
        (-((sourceVisitEta q N i : ℝ) : ℂ) / (rho : ℂ))
        (((sourceVisitQ q N i : ℝ) : ℂ) / (rho : ℂ)^2)
        (-((sourceVisitEta q N i : ℝ) : ℂ) *
          (Vbig g : ℂ) / (rho : ℂ))
        (Green64Fock.sourceBirthNu
          (fun p : BP g => (muBig g p : ℂ)))
        (c g) = 0 := by
    simp [ghostWitnessTerm, hwrong]
  exact hfactor hzero

end Green64FullPhysicalE

end

/-! ## MemorySourceBirthCount -/

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
set_option maxHeartbeats 700000

/-- The ORIGINAL pattern has at most ell+m unshared slots, independent of J. -/
theorem memory_source_unshared_count (pat : SourcePattern BG J m) (g : BG) :
    (orientedUnshared (J+ell) (sourceBigShared J ell m pat g)).card ≤ ell+m := by
  classical
  let S := orientedUnshared (J+ell) (sourceBigShared J ell m pat g)
  have hfree (i : ↥S) (hi : i.val.val < J) :
      (⟨i.val.val,hi⟩ : Fin J) ∈ pat.free g := by
    have hn : i.val ∉ sourceBigShared J ell m pat g := (Finset.mem_sdiff.mp i.property).2
    have hv : i.val.val ∈ (pat.free g).image Fin.val := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,h⟩)
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hv
    have hj' : j = ⟨i.val.val,hi⟩ := Fin.ext he
    simpa only [hj'] using hj
  let f : ↥S → (Fin ell ⊕ ↥(pat.free g)) := fun i =>
    if hi : i.val.val < J then Sum.inr ⟨⟨i.val.val,hi⟩,hfree i hi⟩
    else Sum.inl ⟨i.val.val-J,by have h := i.val.isLt; omega⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    apply Fin.ext
    by_cases hi : i.val.val < J <;> by_cases hj : j.val.val < J
    · simp only [f,dif_pos hi,dif_pos hj,Sum.inr.injEq] at he
      exact congrArg (fun z : ↥(pat.free g) => z.val.val) he
    · simp only [f,dif_pos hi,dif_neg hj] at he
      cases he
    · simp only [f,dif_neg hi,dif_pos hj] at he
      cases he
    · simp only [f,dif_neg hi,dif_neg hj,Sum.inl.injEq] at he
      have hv := congrArg Fin.val he
      dsimp only at hv
      omega
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe,Fintype.card_sum,Fintype.card_fin] at hc
  exact hc.trans (Nat.add_le_add_left (pat.free_bound g) ell)

/-- Literal ghost deletion/birth cannot increase memory by more than its birth count. -/
theorem memory_original_afterGhost_length {A : Type} [Fintype A] [DecidableEq A]
    (old : List A) (drop : Finset (Fin old.length)) {b : ℕ} (fresh : Fin b → A) :
    (Green64MemoryGhostOp.afterGhost old drop fresh).length ≤ old.length+b := by
  unfold Green64MemoryGhostOp.afterGhost
  simp only [List.length_append,List.length_map,List.length_ofFn]
  have h := List.length_filter_le (fun j : Fin old.length => j ∉ drop) (List.finRange old.length)
  simpa only [List.length_finRange] using Nat.add_le_add_right h b

/-- Genuine original G-step source count, derived from its nonzero literal coefficient. -/
theorem memory_actual_G_occupation_step
    (cap : BG → ℕ) (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (hn : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho N i Vbig muBig x y c ≠ 0) (g : BG) :
    ((y.2 g).2).1.val ≤ ((x.2 g).2).1.val + (c g).2.1.val := by
  have ho := (physical_nonzero_ghost_witness_is_operational SP smallMod BP bigMod
    (J+ell) cap q rho N i Vbig muBig x y c hn).2 g
  have hl := memory_original_afterGhost_length
    (Green64Fock.fockToList ((x.2 g).2)) (c g).1.1 (c g).2.2
  rw [ho] at hl
  simpa only [Green64Fock.fockToList,List.length_ofFn] using hl

/-- The original oriented E-step contributes at most ell+m stored particles
per BIG group; permutations do not turn this into J+ell. -/
theorem memory_actual_E_store_count
    (cap : BG → ℕ)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (o k : ℤ) (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x)
    (hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns x o k z)
    (g : BG) :
    (((z.2.2.1.bigChoice g).2).1).card ≤ ell+m := by
  have hs := (hz.2.2.2.1 g).stores_unshared
  exact (Finset.card_le_card hs).trans (memory_source_unshared_count J ell m (patterns z.1) g)
end Green64FullPhysicalE

end

end

/-! ## MemoryPromotionAbsoluteBound -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 600000

/-- Exact factorial/geometric majorant for the source ordered promotions. -/
theorem memory_promotion_damping_bound (rho : ℝ) (hr : 0 < rho) (hr1 : rho < 1)
    (z a : ℕ) :
    (z.descFactorial a : ℝ) * rho ^ (z-a) ≤
      (a.factorial : ℝ) / (1-rho) ^ (a+1) := by
  have hn : ‖rho‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hr] using hr1
  by_cases ha : a ≤ z
  · have hs := hasSum_choose_mul_geometric_of_norm_lt_one a hn
    have hh := Summable.sum_le_tsum ({z-a} : Finset ℕ)
      (fun n _ => show 0 ≤ ((n+a).choose a : ℝ) * rho^n from by positivity) hs.summable
    rw [hs.tsum_eq] at hh
    have hb : (z.choose a : ℝ) * rho ^ (z-a) ≤ 1/(1-rho)^(a+1) := by
      simpa only [Finset.sum_singleton, Nat.sub_add_cancel ha] using hh
    have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ (a.factorial : ℝ) from by positivity)
    simpa [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_assoc, div_eq_mul_inv] using h
  · have hz : z < a := Nat.lt_of_not_ge ha
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_eq_zero_of_lt hz]
    simp only [mul_zero, Nat.cast_zero, zero_mul]
    positivity

/-- Finite uniform constant depending on ell+m, never on J or the OLD length. -/
def memoryPromotionDampingConstant (rho : ℝ) (d : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (d+1), (a.factorial : ℝ) / (1-rho) ^ (a+1)

theorem memory_promotion_damping_uniform (rho : ℝ) (hr : 0 < rho) (hr1 : rho < 1)
    (z a d : ℕ) (ha : a ≤ d) :
    (z.descFactorial a : ℝ) * rho ^ (z-a) ≤ memoryPromotionDampingConstant rho d := by
  apply (memory_promotion_damping_bound rho hr hr1 z a).trans
  unfold memoryPromotionDampingConstant
  exact Finset.single_le_sum
    (f := fun b : ℕ => (b.factorial : ℝ) / (1-rho) ^ (b+1))
    (s := Finset.range (d+1)) (fun b _ => by positivity)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- In the ORIGINAL oriented source choice, promotions are at most ell+m. -/
theorem memory_actual_E_promotion_count
    (cap : BG → ℕ) (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (o k : ℤ) (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x)
    (hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns x o k z)
    (g : BG) :
    (((z.2.2.1.bigChoice g).2).2.1).card ≤ ell+m := by
  have hs := (hz.2.2.2.1 g).promotes_unshared
  exact (Finset.card_le_card hs).trans (memory_source_unshared_count J ell m (patterns z.1) g)

/-- The literal source promotion factor is bounded independently of J and memory. -/
theorem memory_actual_E_promotion_damping_bound
    (cap : BG → ℕ) (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (o k : ℤ) (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x)
    (hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns x o k z)
    (g : BG) (Z : ℕ) (rho : ℝ) (hr : 0 < rho) (hr1 : rho < 1) :
    (Z.descFactorial (((z.2.2.1.bigChoice g).2).2.1).card : ℝ) *
      rho ^ (Z-(((z.2.2.1.bigChoice g).2).2.1).card) ≤
        memoryPromotionDampingConstant rho (ell+m) := by
  exact memory_promotion_damping_uniform rho hr hr1 Z _ (ell+m)
    (memory_actual_E_promotion_count SP smallMod BP bigMod J ell m patterns cap x o k z hz g)
end Green64FullPhysicalE

end

end

/-! ## MemorySmallConditioningEnvelope -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

/-- The exact SMALL conditioning multiplier: omega zero coordinates,
J shared distinct active slots and ell omitted ones. No exponential
factor in J survives after the original Haar/mark normalization. -/
theorem memory_small_conditioning_envelope
    (q V : ℝ) (hq : 0 < q) (hq1 : q < 1) (hV : 0 < V)
    (J ell z : ℕ) (hz : J+ell ≤ z) :
    (q^(z-(J+ell)) *
      ((z-J).descFactorial ell : ℝ)) / V^ell ≤
      (ell.factorial : ℝ) / ((1-q)^(ell+1)*V^ell) := by
  have hpow : (z-J)-ell = z-(J+ell) := by omega
  have hmain := memory_promotion_damping_bound q hq hq1 (z-J) ell
  rw [hpow] at hmain
  have hden : 0 ≤ 1 / V^ell := by positivity
  have hmul := mul_le_mul_of_nonneg_right hmain hden
  simpa only [div_eq_mul_inv, mul_inv_rev, one_mul, mul_one,
    mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Actual source physical SMALL state (not any invalid mark list):
omega >= J+ell and the same conditioning envelope holds. -/
theorem memory_small_physical_conditioning_envelope
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
    (q V : ℝ) (hq : 0 < q) (hq1 : q < 1) (hV : 0 < V)
    (J ell : ℕ)
    (x : Green64SmallHaar.SmallState modulus (J+ell)) :
    (q^(Green64SmallHaar.omega modulus
         (Green64SmallHaar.residues modulus (J+ell) x) - (J+ell)) *
     ((Green64SmallHaar.omega modulus
        (Green64SmallHaar.residues modulus (J+ell) x)-J).descFactorial ell : ℝ)) /
      V^ell ≤
      (ell.factorial : ℝ) / ((1-q)^(ell+1)*V^ell) := by
  exact memory_small_conditioning_envelope q V hq hq1 hV J ell _
    (Green64SmallHaar.omega_ge_M modulus (J+ell) x)
end Green64FullPhysicalE

end

end

/-! ## MemorySourcePromotionCount -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 800000

/-- OLD indices remain distinct even when their atom values coincide. -/
def memoryEmbeddingInto {A I : Type} [Fintype A] [Fintype I]
    (Z : Finset I) : {f : A ↪ I // ∀ a, f a ∈ Z} ≃ (A ↪ ↥Z) where
  toFun f := ⟨fun a => ⟨f.1 a, f.2 a⟩, fun a b h => f.1.injective (congrArg Subtype.val h)⟩
  invFun f := ⟨⟨fun a => (f a).1, fun a b h => f.injective (Subtype.ext h)⟩,
    fun a => (f a).2⟩
  left_inv f := by apply Subtype.ext; apply Function.Embedding.ext; intro a; rfl
  right_inv f := by apply Function.Embedding.ext; intro a; rfl

/-- Exact number of ordered retrievals from the ORIGINAL OLD-index zero set. -/
theorem memory_embedding_zero_count {A I : Type} [Fintype A] [Fintype I]
    [DecidableEq I] (Z : Finset I) :
    ((Finset.univ : Finset (A ↪ I)).filter (fun f => ∀ a, f a ∈ Z)).card =
      Z.card.descFactorial (Fintype.card A) := by
  rw [← Fintype.card_coe]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Fintype.card_congr (memoryEmbeddingInto (A := A) Z)]
  simp only [Fintype.card_embedding_eq, Fintype.card_coe]

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)

/-- The actual OLD particles whose translated residue is zero. -/
def memoryTranslatedOldZero (x : BigState modulus M B) (step : ℤ) :
    Finset (Fin x.2.1.val) :=
  Finset.univ.filter (fun j => (x.2.2 j).2 +
    (step : ZMod (modulus (x.2.2 j).1)) = 0)

/-- Legality implies the ORIGINAL promotion injection lands in this set. -/
theorem memory_legal_promotion_into_zero
    (x : BigState modulus M B) (target : Fin M → P)
    (shared : Finset (Fin M)) (sigma tau : Equiv.Perm (Fin M))
    (D : ℕ) (step : ℤ) (c : BigEdgeChoice modulus M B x)
    (hc : OrientedBigEdgeLegal modulus M B x target shared sigma tau D step c) :
    ∀ a, c.2.2 a ∈ memoryTranslatedOldZero modulus M B x step := by
  intro a
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.promoted_zero a⟩

/-- Complete weighted retrieval sum: no old-memory or cutoff-dependent constant. -/
theorem memory_actual_promotion_sum_bound
    (x : BigState modulus M B) (step : ℤ) (A : Finset (Fin M))
    (rho : ℝ) (hr : 0 < rho) (hr1 : rho < 1) (d : ℕ) (hA : A.card ≤ d) :
    (∑ f ∈ (Finset.univ : Finset (↥A ↪ Fin x.2.1.val)).filter
      (fun f => ∀ a, f a ∈ memoryTranslatedOldZero modulus M B x step),
      rho ^ ((memoryTranslatedOldZero modulus M B x step).card - A.card)) ≤
        memoryPromotionDampingConstant rho d := by
  rw [Finset.sum_const, nsmul_eq_mul, memory_embedding_zero_count]
  simp only [Fintype.card_coe]
  exact memory_promotion_damping_uniform rho hr hr1 _ _ d hA
end Green64FullPhysicalE

end

end

/-! ## MemorySmallSourceCount -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64SmallHaar
set_option maxHeartbeats 0
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M : ℕ)

def memorySmallRemainingLabels (shared : Finset (Fin M))
    (sigma : SlotPerm M) (x : SmallState modulus M) (y : SmallTorus modulus) : Finset P :=
  zeroCoordSet modulus y \ shared.image (fun j => marks modulus M x (sigma j))

/-- Actual target choices inject into ordered distinct labels outside the shared marks. -/
def memorySmallTargetEmbedding
    (shared : Finset (Fin M)) (step : ℤ) (sigma tau : SlotPerm M)
    (x : SmallState modulus M)
    (z : {z : SmallState modulus M // edgeAllowedPerm modulus M shared step sigma tau x z}) :
    (↥(sharedᶜ) ↪ ↥(memorySmallRemainingLabels modulus M shared sigma x
      (translate modulus step (residues modulus M x)))) where
  toFun j := ⟨marks modulus M z.1 (tau j), by
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← z.2.1]
      exact marked_zero modulus M z.1 (tau j)
    · intro hp
      obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
      have he' : marks modulus M z.1 (tau k) = marks modulus M z.1 (tau j) := by
        rw [← z.2.2 k hk]
        exact he
      have hkj : k = j.val := tau.injective (marks_injective modulus M z.1 he')
      exact (Finset.mem_compl.mp j.2) (hkj ▸ hk)⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact tau.injective (marks_injective modulus M z.1 (congrArg Subtype.val h))

theorem memory_small_target_embedding_injective
    (shared : Finset (Fin M)) (step : ℤ) (sigma tau : SlotPerm M)
    (x : SmallState modulus M) :
    Function.Injective (memorySmallTargetEmbedding modulus M shared step sigma tau x) := by
  intro z w h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact z.2.1.trans w.2.1.symm
  · funext j
    obtain ⟨i, rfl⟩ := tau.surjective j
    by_cases hi : i ∈ shared
    · exact (z.2.2 i hi).symm.trans (w.2.2 i hi)
    · have he := congrArg (fun f => (f ⟨i, Finset.mem_compl.mpr hi⟩).val) h
      exact he

/-- The shared labels already consume exactly |shared| translated zero coordinates. -/
theorem memory_small_remaining_card
    (shared : Finset (Fin M)) (step : ℤ) (sigma tau : SlotPerm M)
    (x z : SmallState modulus M)
    (hz : edgeAllowedPerm modulus M shared step sigma tau x z) :
    (memorySmallRemainingLabels modulus M shared sigma x
      (translate modulus step (residues modulus M x))).card =
      omega modulus (residues modulus M z) - shared.card := by
  have hs : shared.image (fun j => marks modulus M x (sigma j)) ⊆
      zeroCoordSet modulus (translate modulus step (residues modulus M x)) := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hz.1, hz.2 j hj]
    exact marked_zero modulus M z (tau j)
  unfold memorySmallRemainingLabels
  rw [Finset.card_sdiff_of_subset hs]
  have hi : Function.Injective (fun j => marks modulus M x (sigma j)) := by
    intro a b h
    exact sigma.injective (marks_injective modulus M x h)
  rw [Finset.card_image_of_injective shared hi]
  rw [← hz.1]
  rfl

/-- Source-exact cardinal majorant for the entire SMALL target fibre. -/
theorem memory_small_allowed_target_count
    (shared : Finset (Fin M)) (step : ℤ) (sigma tau : SlotPerm M)
    (x z : SmallState modulus M)
    (hz : edgeAllowedPerm modulus M shared step sigma tau x z) :
    Fintype.card {w : SmallState modulus M // edgeAllowedPerm modulus M shared step sigma tau x w} ≤
      (omega modulus (residues modulus M z)-shared.card).descFactorial (unsharedSlots M shared) := by
  have h := Fintype.card_le_of_injective _
    (memory_small_target_embedding_injective modulus M shared step sigma tau x)
  rw [Fintype.card_embedding_eq, Fintype.card_coe,
    memory_small_remaining_card modulus M shared step sigma tau x z hz] at h
  simpa only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, unsharedSlots] using h
end Green64SmallHaar

end

end

/-! ## MemorySmallSourceRow -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64SmallHaar
set_option maxHeartbeats 0
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M : ℕ)

def memorySmallAllowed (shared : Finset (Fin M)) (step : ℤ) (sigma tau : SlotPerm M)
    (x : SmallState modulus M) : Finset (SmallState modulus M) :=
  Finset.univ.filter (edgeAllowedPerm modulus M shared step sigma tau x)

def memorySmallScalarRow (q V : ℝ) (shared : Finset (Fin M)) (step : ℤ)
    (sigma tau : SlotPerm M) (x : SmallState modulus M) : ℝ :=
  ∑ z ∈ memorySmallAllowed modulus M shared step sigma tau x, edgeScalar modulus M q V shared x z

/-- Depends on the number of unshared slots, never on the number of fixed/shared slots. -/
def memorySmallRowConstant (q V : ℝ) (t : ℕ) : ℝ :=
  (1/V^t) * ((t.factorial:ℝ)/(1-Real.sqrt q)^(t+1))

theorem memory_small_allowed_card
    (shared : Finset (Fin M)) (step : ℤ) (sigma tau : SlotPerm M)
    (x z : SmallState modulus M) (hz : edgeAllowedPerm modulus M shared step sigma tau x z) :
    (memorySmallAllowed modulus M shared step sigma tau x).card ≤
      (omega modulus (residues modulus M z)-shared.card).descFactorial (unsharedSlots M shared) := by
  have h := memory_small_allowed_target_count modulus M shared step sigma tau x z hz
  simpa only [memorySmallAllowed, ← Fintype.card_coe, Finset.mem_filter,
    Finset.mem_univ, true_and] using h

theorem memory_small_allowed_scalar_eq
    (q V : ℝ) (shared : Finset (Fin M)) (step : ℤ) (sigma tau : SlotPerm M)
    (x z w : SmallState modulus M)
    (hz : edgeAllowedPerm modulus M shared step sigma tau x z)
    (hw : edgeAllowedPerm modulus M shared step sigma tau x w) :
    edgeScalar modulus M q V shared x w = edgeScalar modulus M q V shared x z := by
  have h := hw.1.trans hz.1.symm
  simp only [edgeScalar, endpointDamping, h]

/-- Full original SMALL weighted row, including arbitrary source/target permutations. -/
theorem memory_original_SMALL_E_absolute_row_bound
    (q V : ℝ) (hq : 0 < q) (hq1 : q < 1) (hV : 0 < V)
    (shared : Finset (Fin M)) (step : ℤ) (sigma tau : SlotPerm M)
    (x : SmallState modulus M) :
    memorySmallScalarRow modulus M q V shared step sigma tau x ≤
      memorySmallRowConstant q V (unsharedSlots M shared) := by
  have hr : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hr1 : Real.sqrt q < 1 := by nlinarith [Real.sq_sqrt hq.le, Real.sqrt_nonneg q]
  have hC : 0 ≤ memorySmallRowConstant q V (unsharedSlots M shared) := by
    unfold memorySmallRowConstant
    positivity
  by_cases hn : (memorySmallAllowed modulus M shared step sigma tau x).Nonempty
  · obtain ⟨z,hz⟩ := hn
    have hz0 : edgeAllowedPerm modulus M shared step sigma tau x z := (Finset.mem_filter.mp hz).2
    have he : memorySmallScalarRow modulus M q V shared step sigma tau x =
        ((memorySmallAllowed modulus M shared step sigma tau x).card:ℝ) *
          edgeScalar modulus M q V shared x z := by
      unfold memorySmallScalarRow
      calc
        _ = ∑ _w ∈ memorySmallAllowed modulus M shared step sigma tau x,
            edgeScalar modulus M q V shared x z := by
          apply Finset.sum_congr rfl
          intro w hw
          exact memory_small_allowed_scalar_eq modulus M q V shared step sigma tau x z w
            hz0 (Finset.mem_filter.mp hw).2
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((memorySmallAllowed modulus M shared step sigma tau x).card:ℝ) ≤
        ((omega modulus (residues modulus M z)-shared.card).descFactorial (unsharedSlots M shared):ℝ) := by
      exact_mod_cast memory_small_allowed_card modulus M shared step sigma tau x z hz0
    have hOmega := omega_ge_M modulus M z
    have hShared : shared.card ≤ M := by simpa using Finset.card_le_univ shared
    have hsub : omega modulus (residues modulus M z)-shared.card-unsharedSlots M shared =
        omega modulus (residues modulus M z)-M := by
      unfold unsharedSlots
      omega
    have hp := Green64FullPhysicalE.memory_promotion_damping_bound (Real.sqrt q) hr hr1
      (omega modulus (residues modulus M z)-shared.card) (unsharedSlots M shared)
    rw [hsub] at hp
    rw [he]
    calc
      _ ≤ ((omega modulus (residues modulus M z)-shared.card).descFactorial (unsharedSlots M shared):ℝ) *
          edgeScalar modulus M q V shared x z :=
        mul_le_mul_of_nonneg_right hc (edgeScalar_nonneg modulus M q V hV shared x z)
      _ ≤ (1/V^(unsharedSlots M shared)) *
          (((omega modulus (residues modulus M z)-shared.card).descFactorial (unsharedSlots M shared):ℝ) *
            (Real.sqrt q)^(omega modulus (residues modulus M z)-M)) := by
        have hh := mul_le_mul_of_nonneg_left (endpointDamping_le_one modulus M q hq.le hq1.le x)
          (show 0 ≤ ((omega modulus (residues modulus M z)-shared.card).descFactorial
            (unsharedSlots M shared):ℝ) * (1/V^(unsharedSlots M shared)) *
            (Real.sqrt q)^(omega modulus (residues modulus M z)-M) from by positivity)
        simpa only [edgeScalar, endpointDamping, mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using hh
      _ ≤ memorySmallRowConstant q V (unsharedSlots M shared) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [memorySmallScalarRow, he, Finset.sum_empty]
    exact hC

/-- The actual complex SMALL kernel pays its global multiplier once. -/
theorem memory_original_SMALL_kernel_absolute_row
    (q V : ℝ) (hq : 0 < q) (hq1 : q < 1) (hV : 0 < V)
    (shared : Finset (Fin M)) (step : ℤ)
    (K : SlotPerm M → SlotPerm M → ℂ) (sigma tau : SlotPerm M)
    (x : SmallState modulus M) :
    (∑ z : SmallState modulus M, ‖permutedKernel modulus M q V shared step K sigma tau x z‖) ≤
      ‖K sigma tau‖ * memorySmallRowConstant q V (unsharedSlots M shared) := by
  have he : (∑ z : SmallState modulus M, ‖permutedKernel modulus M q V shared step K sigma tau x z‖) =
      ‖K sigma tau‖ * memorySmallScalarRow modulus M q V shared step sigma tau x := by
    unfold memorySmallScalarRow memorySmallAllowed
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases h : edgeAllowedPerm modulus M shared step sigma tau x z
    · simp [permutedKernel, h, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (edgeScalar_nonneg modulus M q V hV shared x z)]
    · simp [permutedKernel, h]
  rw [he]
  exact mul_le_mul_of_nonneg_left
    (memory_original_SMALL_E_absolute_row_bound modulus M q V hq hq1 hV shared step sigma tau x)
    (norm_nonneg _)
end Green64SmallHaar

end

end

/-! ## MemorySmallConditioningFibre -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M : ℕ)

/-- Exact source finite fibre for one fixed shared active mark tuple
and one actual SMALL Haar residue y. Invalid tuples have empty fibre. -/
def memorySmallConditionalFibre (shared : Finset (Fin M))
    (d : ↥shared → P)
    (y : Green64SmallHaar.SmallTorus modulus) :
    Finset (Green64SmallHaar.SmallState modulus M) :=
  Finset.univ.filter (fun x =>
    Green64SmallHaar.residues modulus M x = y ∧
    ∀ i : ↥shared, Green64SmallHaar.marks modulus M x i.1 = d i)

/-- A conditional source fibre injects into the SAME original SMALL
physical edge's allowed target list with zero displacement.
No independent sampling of unshared marks is introduced. -/
theorem memory_small_conditional_fibre_card
    (shared : Finset (Fin M))
    (d : ↥shared → P)
    (y : Green64SmallHaar.SmallTorus modulus) :
    (memorySmallConditionalFibre modulus M shared d y).card ≤
      (Green64SmallHaar.omega modulus y - shared.card).descFactorial
        (Green64SmallHaar.unsharedSlots M shared) := by
  let T := memorySmallConditionalFibre modulus M shared d y
  by_cases he : T.Nonempty
  · obtain ⟨x0,hx0⟩ := he
    have h0 := (Finset.mem_filter.mp hx0).2
    let C := Green64SmallHaar.memorySmallAllowed modulus M shared 0
      (Equiv.refl _) (Equiv.refl _) x0
    have hsub : T ⊆ C := by
      intro x hx
      have h1 := (Finset.mem_filter.mp hx).2
      change x ∈ Green64SmallHaar.memorySmallAllowed modulus M shared
        0 (Equiv.refl _) (Equiv.refl _) x0
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      constructor
      · rw [h1.1, h0.1]
        exact (Green64SmallHaar.translate_zero modulus y).symm
      · intro j hj
        have h01 := h0.2 ⟨j,hj⟩
        have h11 := h1.2 ⟨j,hj⟩
        simpa only [Equiv.refl_apply] using h01.trans h11.symm
    have ha : Green64SmallHaar.edgeAllowedPerm modulus M shared 0
        (Equiv.refl _) (Equiv.refl _) x0 x0 := by
      constructor
      · exact (Green64SmallHaar.translate_zero modulus _).symm
      · intro j hj
        rfl
    have hcount := Green64SmallHaar.memory_small_allowed_card
      modulus M shared 0 (Equiv.refl _) (Equiv.refl _) x0 x0 ha
    exact (Finset.card_le_card hsub).trans
       (by simpa only [h0.1] using hcount)
  · have hh : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    change T.card ≤ _
    rw [hh, Finset.card_empty]
    exact Nat.zero_le _
end Green64FullPhysicalE

end

end

/-! ## MemorySmallConditionalWeight -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]

/-- TRUE source SMALL conditional one-group coefficient, divided
by the unchanged physical state mass Haar(y)*V^(-(J+ell)).
Its physical square multiplier is q^(omega-M)/V^ell. -/
def memorySmallConditionalRatio
    (J ell : ℕ) (q V : ℝ)
    (y : Green64SmallHaar.SmallTorus modulus) : ℝ :=
  q ^ (Green64SmallHaar.omega modulus y - (J+ell)) / V^ell

/-- For every actual physical shared-label tuple d and Haar residue
y, the squared conditioning map costs at most the fixed source
factor ell!/(V^ell*(1-q)^(ell+1)), INDEPENDENT of J. -/
theorem memory_small_conditional_fibre_weight_bound
    (J ell : ℕ) (q V : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hV : 0 < V)
    (shared : Finset (Fin (J+ell))) (hshared : shared.card = J)
    (d : ↥shared → P) (y : Green64SmallHaar.SmallTorus modulus) :
    memorySmallConditionalRatio modulus J ell q V y *
      ((memorySmallConditionalFibre modulus (J+ell) shared d y).card : ℝ) ≤
    (ell.factorial : ℝ) / ((1-q)^(ell+1)*V^ell) := by
  let T := memorySmallConditionalFibre modulus (J+ell) shared d y
  have hrest : Green64SmallHaar.unsharedSlots (J+ell) shared = ell := by
    unfold Green64SmallHaar.unsharedSlots
    rw [hshared]
    omega
  have hn := memory_small_conditional_fibre_card modulus
      (J+ell) shared d y
  rw [hshared, hrest] at hn
  have hh : (T.card : ℝ) ≤
      ((Green64SmallHaar.omega modulus y - J).descFactorial ell : ℝ) := by
    exact_mod_cast hn
  have hpos : 0 ≤ q ^ (Green64SmallHaar.omega modulus y-(J+ell)) :=
    pow_nonneg hq.le _
  have hden : 0 ≤ V^ell := pow_nonneg hV.le _
  have hbound : (q^(Green64SmallHaar.omega modulus y-(J+ell)) *
      (T.card : ℝ)) / V^ell ≤
    (q^(Green64SmallHaar.omega modulus y-(J+ell)) *
      ((Green64SmallHaar.omega modulus y-J).descFactorial ell : ℝ)) /
      V^ell := by
    apply div_le_div_of_nonneg_right _ hden
    exact mul_le_mul_of_nonneg_left hh hpos
  by_cases he : T.Nonempty
  · obtain ⟨x,hx⟩ := he
    have hxres := (Finset.mem_filter.mp hx).2.1
    have hz : J+ell ≤ Green64SmallHaar.omega modulus y := by
      rw [← hxres]
      exact Green64SmallHaar.omega_ge_M modulus (J+ell) x
    have hmain := memory_small_conditioning_envelope q V
        hq hq1 hV J ell (Green64SmallHaar.omega modulus y) hz
    dsimp only [memorySmallConditionalRatio]
    change (q ^ (Green64SmallHaar.omega modulus y - (J+ell)) / V^ell) *
       (T.card : ℝ) ≤ _
    calc
      _ = (q^(Green64SmallHaar.omega modulus y-(J+ell)) *
         (T.card:ℝ)) / V^ell := by ring
      _ ≤ _ := hbound
      _ ≤ _ := hmain
  · have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    change memorySmallConditionalRatio modulus J ell q V y *
      (T.card:ℝ) ≤ _
    rw [hT]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero]
    positivity
end Green64FullPhysicalE

end

end

/-! ## MemoryOriginalSmallSourceEndpointSquare -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (J ell : ℕ)

/-- The actual SOURCE one-endpoint half-kernel in a SMALL
group; exact V^-ell/2 and q^((omega-M)/2), not an
independently manufactured probability density. -/
noncomputable def memoryOriginalSmallPhysicalEndpointHalf
    (q V : ℝ)
    (y : Green64SmallHaar.SmallTorus modulus) : ℝ :=
  (Real.sqrt (1 / V^ell)) *
    (Real.sqrt q)^(Green64SmallHaar.omega modulus y-(J+ell))

/-- Source endpoint half is a REAL square root of the
existing exact SMALL physical conditioning ratio, for ALL
Haar residues (also where physical fibres are empty).
No J-dependent factor is introduced. -/
theorem memory_original_small_physical_endpoint_half_sq
    (q V : ℝ) (hq : 0 ≤ q) (hV : 0 < V)
    (y : Green64SmallHaar.SmallTorus modulus) :
    (memoryOriginalSmallPhysicalEndpointHalf
       modulus J ell q V y)^2 =
    memorySmallConditionalRatio modulus J ell q V y := by
  let n := Green64SmallHaar.omega modulus y-(J+ell)
  have hv : 0 ≤ 1/V^ell := by positivity
  have hsqv : (Real.sqrt (1/V^ell))^2 = 1/V^ell :=
    Real.sq_sqrt hv
  have hsqq : (Real.sqrt q)^2 = q := Real.sq_sqrt hq
  have hp : ((Real.sqrt q)^n)^2 = q^n := by
    calc
      _ = ((Real.sqrt q)^2)^n := by
        rw [←pow_mul, ←pow_mul]
        congr 1
        omega
      _ = _ := by rw [hsqq]
  unfold memoryOriginalSmallPhysicalEndpointHalf
    memorySmallConditionalRatio
  change (Real.sqrt (1/V^ell) * (Real.sqrt q)^n)^2 =
    q^n / V^ell
  rw [mul_pow, hsqv, hp]
  ring

/-- The TRUE SOURCE physical SMALL edgeScalar is exactly
the product of TWO ENDPOINT HALF KERNELS, independently
of the two permuted shared-slot lists. This is the
normalization required for a genuine two-sided P_d map. -/
theorem memory_original_small_edge_scalar_half_exact
    (q V : ℝ) (hq : 0 ≤ q) (hV : 0 < V)
    (shared : Finset (Fin (J+ell)))
    (hshared : shared.card = J)
    (x z : Green64SmallHaar.SmallState modulus (J+ell)) :
    Green64SmallHaar.edgeScalar modulus (J+ell)
      q V shared x z =
    memoryOriginalSmallPhysicalEndpointHalf modulus J ell q V
      (Green64SmallHaar.residues modulus (J+ell) x) *
    memoryOriginalSmallPhysicalEndpointHalf modulus J ell q V
      (Green64SmallHaar.residues modulus (J+ell) z) := by
  have hsize : Green64SmallHaar.unsharedSlots (J+ell)
      shared = ell := by
    unfold Green64SmallHaar.unsharedSlots
    rw [hshared]
    omega
  let yx := Green64SmallHaar.residues modulus (J+ell) x
  let yz := Green64SmallHaar.residues modulus (J+ell) z
  have hv : 0 ≤ 1/V^ell := by positivity
  have hs : (Real.sqrt (1/V^ell))^2 = 1/V^ell :=
    Real.sq_sqrt hv
  unfold Green64SmallHaar.edgeScalar
    Green64SmallHaar.endpointDamping
    memoryOriginalSmallPhysicalEndpointHalf
  rw [hsize]
  change (1/V^ell) * (Real.sqrt q)^
      (Green64SmallHaar.omega modulus yx-(J+ell)) *
      (Real.sqrt q)^
      (Green64SmallHaar.omega modulus yz-(J+ell)) =
    (Real.sqrt (1/V^ell) *
      (Real.sqrt q)^(Green64SmallHaar.omega modulus yx-(J+ell))) *
    (Real.sqrt (1/V^ell) *
      (Real.sqrt q)^(Green64SmallHaar.omega modulus yz-(J+ell)))
  calc
    _ = (Real.sqrt (1/V^ell))^2 *
      (Real.sqrt q)^(Green64SmallHaar.omega modulus yx-(J+ell)) *
      (Real.sqrt q)^(Green64SmallHaar.omega modulus yz-(J+ell)) := by
        rw [hs]
    _ = _ := by ring
end Green64FullPhysicalE

end

end

/-! ## MemorySmallConditioningActualMap -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]

/-- Condition the TRUE source SMALL M-mark Hilbert vector at a fixed
shared J-tuple and the full original Haar residue y. The scale is
precisely the squared source P_d multiplier after cancelling the
original physical Haar*V^(-M) input mass. -/
theorem memory_small_actual_conditioning_map_norm_sq
    (J ell : ℕ) (q V : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hV : 0 < V)
    (shared : Finset (Fin (J+ell))) (hshared : shared.card = J)
    (w : Green64SmallHaar.SmallState modulus (J+ell) → ℂ) :
    (∑ d : ↥shared → P, ∑ y : Green64SmallHaar.SmallTorus modulus,
      memorySmallConditionalRatio modulus J ell q V y *
      ‖∑ x ∈ memorySmallConditionalFibre
         modulus (J+ell) shared d y, w x‖^2) ≤
    ((ell.factorial : ℝ) / ((1-q)^(ell+1)*V^ell)) *
      (∑ x : Green64SmallHaar.SmallState modulus (J+ell),
        ‖w x‖^2) := by
  let label := fun (x : Green64SmallHaar.SmallState modulus (J+ell)) =>
    (fun i : ↥shared => Green64SmallHaar.marks modulus (J+ell) x i.1)
  let residue := fun (x : Green64SmallHaar.SmallState modulus (J+ell)) =>
    Green64SmallHaar.residues modulus (J+ell) x
  let a := memorySmallConditionalRatio modulus J ell q V
  let C : ℝ := (ell.factorial : ℝ)/((1-q)^(ell+1)*V^ell)
  have hqpos : 0 < 1-q := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha (y : Green64SmallHaar.SmallTorus modulus) : 0 ≤ a y := by
    unfold a memorySmallConditionalRatio
    positivity
  have hfibre (d : ↥shared → P)
      (y : Green64SmallHaar.SmallTorus modulus) :
      memoryFiniteConditionalFibre label residue d y =
      memorySmallConditionalFibre modulus (J+ell) shared d y := by
    ext x
    simp only [memoryFiniteConditionalFibre,
      memorySmallConditionalFibre, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hd,hy⟩
      exact ⟨hy, fun i => congrFun hd i⟩
    · rintro ⟨hy,hd⟩
      exact ⟨funext hd,hy⟩
  have hbound (d : ↥shared → P)
      (y : Green64SmallHaar.SmallTorus modulus) :
      a y * ((memoryFiniteConditionalFibre label residue d y).card : ℝ)
      ≤ C := by
    rw [hfibre d y]
    exact memory_small_conditional_fibre_weight_bound
      modulus J ell q V hq hq1 hV shared hshared d y
  have hnorm := memory_finite_conditioning_norm_sq label residue
       a ha C hC hbound w
  simpa only [a, C, hfibre] using hnorm
end Green64FullPhysicalE

end

end

/-! ## MemoryOriginalSmallSourceConditionalEdge -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M : ℕ)

/-- Genuine labelled shared slots after the original independent
source and target permutations; not the same ordered slot family. -/
def memoryOriginalSmallSharedLabels
    (shared : Finset (Fin M)) (σ : Equiv.Perm (Fin M))
    (x : Green64SmallHaar.SmallState modulus M) :
    ↥shared → P :=
  fun j => Green64SmallHaar.marks modulus M x (σ j.val)

/-- Source-correct SMALL physical edge conditional character:
the shared labels agree AND the full Haar residue is translated
by the source signed integer displacement. -/
theorem memory_original_small_edge_allowed_conditional_iff
    (shared : Finset (Fin M)) (step : ℤ)
    (σ τ : Equiv.Perm (Fin M))
    (x z : Green64SmallHaar.SmallState modulus M) :
    Green64SmallHaar.edgeAllowedPerm modulus M
      shared step σ τ x z ↔
    memoryOriginalSmallSharedLabels modulus M shared σ x =
      memoryOriginalSmallSharedLabels modulus M shared τ z ∧
    Green64SmallHaar.residues modulus M z =
      Green64SmallHaar.translate modulus step
        (Green64SmallHaar.residues modulus M x) := by
  unfold Green64SmallHaar.edgeAllowedPerm
    Green64SmallHaar.sameSharedPerm
    memoryOriginalSmallSharedLabels
  constructor
  · rintro ⟨hr,hs⟩
    refine ⟨funext ?_, hr⟩
    intro j
    exact hs j.val j.property
  · rintro ⟨hs,hr⟩
    refine ⟨hr, ?_⟩
    intro j hj
    exact congrFun hs ⟨j,hj⟩

/-- Actual source SMALL conditional fibre with its independent
permutation: labels d are attached to pattern SHARED slots, and
the residue y is the literal original Haar coordinate. -/
def memoryOriginalSmallPermutedFibre
    (shared : Finset (Fin M)) (σ : Equiv.Perm (Fin M))
    (d : ↥shared → P)
    (y : Green64SmallHaar.SmallTorus modulus) :
    Finset (Green64SmallHaar.SmallState modulus M) :=
  memoryFiniteConditionalFibre
    (memoryOriginalSmallSharedLabels modulus M shared σ)
    (Green64SmallHaar.residues modulus M) d y

/-- Each actual oriented SMALL physical edge is in one and only one
pair of original shared-label/residue fibres; both endpoint
permutations and the true signed step are present. -/
theorem memory_original_small_physical_edge_iff_fibres
    (shared : Finset (Fin M)) (step : ℤ)
    (σ τ : Equiv.Perm (Fin M))
    (x z : Green64SmallHaar.SmallState modulus M) :
    Green64SmallHaar.edgeAllowedPerm modulus M
      shared step σ τ x z ↔
      ∃ (d : ↥shared → P)
        (y : Green64SmallHaar.SmallTorus modulus),
          x ∈ memoryOriginalSmallPermutedFibre
            modulus M shared σ d y ∧
          z ∈ memoryOriginalSmallPermutedFibre
            modulus M shared τ d
              (Green64SmallHaar.translate modulus step y) := by
  rw [memory_original_small_edge_allowed_conditional_iff]
  constructor
  · rintro ⟨hs,hr⟩
    refine ⟨memoryOriginalSmallSharedLabels modulus M shared σ x,
      Green64SmallHaar.residues modulus M x, ?_, ?_⟩
    · simp [memoryOriginalSmallPermutedFibre,
        memoryFiniteConditionalFibre]
    · simp [memoryOriginalSmallPermutedFibre,
        memoryFiniteConditionalFibre, ←hs, hr]
  · rintro ⟨d,y,hx,hz⟩
    have hx' :
        memoryOriginalSmallSharedLabels modulus M shared σ x = d ∧
        Green64SmallHaar.residues modulus M x = y := by
      simpa only [memoryOriginalSmallPermutedFibre,
        memoryFiniteConditionalFibre, Finset.mem_filter,
        Finset.mem_univ, true_and] using hx
    have hz' :
        memoryOriginalSmallSharedLabels modulus M shared τ z = d ∧
        Green64SmallHaar.residues modulus M z =
          Green64SmallHaar.translate modulus step y := by
      simpa only [memoryOriginalSmallPermutedFibre,
        memoryFiniteConditionalFibre, Finset.mem_filter,
        Finset.mem_univ, true_and] using hz
    exact ⟨hx'.1.trans hz'.1.symm, by rw [hz'.2, hx'.2]⟩
end Green64FullPhysicalE

end

end

/-! ## MemoryOriginalSmallPhysicalTwoEndpointPairing -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M : ℕ)

/-- EXACT whole ORIGINAL physical SMALL source/target pairing,
for ARBITRARY complex coefficients H(x,z), with the genuine
two INDEPENDENT sampled endpoint permutations and original
signed integer displacement. No replacement of SMALL Haar
states by independent residues, no dropped legality or
per-source maximal amplitude hypotheses. Every edge occurs
in exactly one true common shared tuple and translated
Haar residue fibre. -/
theorem memory_original_small_physical_two_endpoint_pairing
    (shared : Finset (Fin M)) (step : ℤ)
    (σ τ : Equiv.Perm (Fin M))
    (H : Green64SmallHaar.SmallState modulus M →
      Green64SmallHaar.SmallState modulus M → ℂ) :
    (∑ x : Green64SmallHaar.SmallState modulus M,
       ∑ z : Green64SmallHaar.SmallState modulus M,
         if Green64SmallHaar.edgeAllowedPerm modulus M
              shared step σ τ x z then H x z else 0) =
    ∑ d : ↥shared → P,
       ∑ y : Green64SmallHaar.SmallTorus modulus,
         ∑ x ∈ memoryOriginalSmallPermutedFibre
             modulus M shared σ d y,
           ∑ z ∈ memoryOriginalSmallPermutedFibre
             modulus M shared τ d
               (Green64SmallHaar.translate modulus step y),
              H x z := by
  classical
  have h := memory_finite_two_endpoint_conditioning
    (memoryOriginalSmallSharedLabels modulus M shared σ)
    (memoryOriginalSmallSharedLabels modulus M shared τ)
    (Green64SmallHaar.residues modulus M)
    (Green64SmallHaar.residues modulus M)
    (Green64SmallHaar.translate modulus step) H
  convert h using 1
  · apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    have hc := memory_original_small_edge_allowed_conditional_iff
      modulus M shared step σ τ x z
    by_cases he : Green64SmallHaar.edgeAllowedPerm modulus M
        shared step σ τ x z
    · simp [he, hc.mp he]
    · have hn : ¬(memoryOriginalSmallSharedLabels modulus M shared σ x =
            memoryOriginalSmallSharedLabels modulus M shared τ z ∧
          Green64SmallHaar.residues modulus M z =
            Green64SmallHaar.translate modulus step
              (Green64SmallHaar.residues modulus M x)) :=
        fun hh => he (hc.mpr hh)
      simp [he, hn]
  · rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryOriginalSmallGroupSourceConditional -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)]
  [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ)
  [∀ g p, NeZero (smallMod g p)]
variable (M : ℕ)

/-- The actual original SMALL pattern-shared labels, one
per group, after the independent source endpoint permutation. -/
def memoryOriginalSmallGroupSharedLabels
    (shared : SG → Finset (Fin M))
    (σ : Green64SmallHaar.GroupPermFamily (G := SG) M)
    (x : Green64SmallHaar.GroupState SP smallMod M) :
    (g : SG) → ↥(shared g) → SP g :=
  fun g => memoryOriginalSmallSharedLabels
    (smallMod g) M (shared g) (σ g) (x g)
/-- Original SMALL per-group full Haar residue, without
replacement by independently sampled root residues. -/
def memoryOriginalSmallGroupResidue
    (x : Green64SmallHaar.GroupState SP smallMod M) :
    Green64SmallHaar.GroupTorus SP smallMod :=
  fun g => Green64SmallHaar.residues (smallMod g) M (x g)

/-- EXACT all-group SMALL legal source physical edge criterion:
original shared-label equality AND one common integer translation
of the actual entire torus. Both source/target permutations are
independent; no disjointness between groups is postulated. -/
theorem memory_original_small_group_edge_conditional_iff
    (shared : SG → Finset (Fin M)) (step : ℤ)
    (σ τ : Green64SmallHaar.GroupPermFamily (G := SG) M)
    (x z : Green64SmallHaar.GroupState SP smallMod M) :
    Green64SmallHaar.groupEdgeAllowedPerm SP smallMod M
      shared step σ τ x z ↔
    memoryOriginalSmallGroupSharedLabels SP smallMod M
       shared σ x =
    memoryOriginalSmallGroupSharedLabels SP smallMod M
       shared τ z ∧
    memoryOriginalSmallGroupResidue SP smallMod M z =
      Green64SmallHaar.groupTranslate SP smallMod step
        (memoryOriginalSmallGroupResidue SP smallMod M x) := by
  constructor
  · intro h
    constructor
    · funext g i
      exact congrFun
        (((memory_original_small_edge_allowed_conditional_iff
          (smallMod g) M (shared g) step
          (σ g) (τ g) (x g) (z g)).mp (h g)).1) i
    · funext g
      exact ((memory_original_small_edge_allowed_conditional_iff
          (smallMod g) M (shared g) step
          (σ g) (τ g) (x g) (z g)).mp (h g)).2
  · rintro ⟨hd,hy⟩ g
    apply (memory_original_small_edge_allowed_conditional_iff
      (smallMod g) M (shared g) step
      (σ g) (τ g) (x g) (z g)).mpr
    constructor
    · exact congrFun hd g
    · exact congrFun hy g

/-- The literal two-endpoint source SMALL fibre, indexed by all
group shared d and full original Haar residue y.
No conditional probability law is postulated here. -/
def memoryOriginalSmallGroupPermutedFibre
    (shared : SG → Finset (Fin M))
    (σ : Green64SmallHaar.GroupPermFamily (G := SG) M)
    (d : (g : SG) → ↥(shared g) → SP g)
    (y : Green64SmallHaar.GroupTorus SP smallMod) :
    Finset (Green64SmallHaar.GroupState SP smallMod M) :=
  memoryFiniteConditionalFibre
    (memoryOriginalSmallGroupSharedLabels SP smallMod M shared σ)
    (memoryOriginalSmallGroupResidue SP smallMod M) d y
end Green64FullPhysicalE

end

end

