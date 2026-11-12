module

public import Green64.Library.Correlation.Part010
public import Green64.Library.Correlation.Part009
public import Green64.Library.Correlation.Part006
public import Green64.Library.Correlation.Part005

@[expose] public section

/-!
# Correlation / Part011

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemorySourceTraceFold -/

section

open Classical
open scoped BigOperators

set_option maxHeartbeats 550000

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

variable (q rho : ℝ) (Vsmall : SG → ℝ)
variable (Vbig : BG → ℝ)
variable (muBig : (g : BG) → BP g → ℝ)
variable (Knu : SourcePatternK BP J ell m patterns)
variable (zeta theta : ℝ) (k : ℤ) (N : ℕ)

/-- Fixed zeta and reversed K retained in ONE exact recursive unfolding of the complete original
finite G_iE_i...G_N indexed witness tree. Its next orbital state and
seen-birth register depend on the ACTUAL indexed oriented E output.
All original conditional Fock weights remain in the GE scalar. -/
theorem memory_source_indexed_trace_sum_succ
    (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) :
    memorySourceIndexedTraceSum SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N (remaining+1) start y seen =
    ∑ ab ∈ physicalOrientedGEIndexedCarrier SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign start) k y seen,
      physicalOrientedGEIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho N start Vsmall Vbig muBig
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign start)) zeta theta
        (physicalAlternatingSign start) k y ab *
      memorySourceIndexedTraceSum SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig Knu
        zeta theta k N remaining (start+1)
        (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
          J ell m cap patterns
          (physicalAlternatingSign start) k ab)
        (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
          J ell m cap patterns seen ab) := by
  unfold memorySourceIndexedTraceSum
  letI : (ab : PhysicalOrientedGEIndex SP smallMod BP bigMod
      J ell m cap patterns
      (physicalAlternatingSign start) k y seen) →
    Fintype (physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
        J ell m cap patterns
        (physicalAlternatingSign start) k ab.val)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
        J ell m cap patterns seen ab.val)) := fun ab =>
    physicalOrientedIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
        J ell m cap patterns
        (physicalAlternatingSign start) k ab.val)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
        J ell m cap patterns seen ab.val)
  simp only [physicalOrientedIndexedTrace, memorySourceIndexedTraceWeight, Fintype.sum_sigma]
  let S := physicalOrientedGEIndexedCarrier SP smallMod BP bigMod
    J ell m cap patterns (physicalAlternatingSign start) k y seen
  let f : (Σ g : PhysicalOrientedGWitnessIndex SP smallMod
      BP bigMod J ell cap,
      PhysicalOrientedEWitnessIndex SP smallMod BP bigMod
        J ell m cap patterns) → ℂ := fun ab =>
    physicalOrientedGEIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho N start Vsmall Vbig muBig
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign start)) zeta theta
      (physicalAlternatingSign start) k y ab *
    memorySourceIndexedTraceSum SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig muBig Knu
      zeta theta k N remaining (start+1)
      (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
        J ell m cap patterns (physicalAlternatingSign start) k ab)
      (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
        J ell m cap patterns seen ab)
  change
    (∑ ab : PhysicalOrientedGEIndex SP smallMod BP bigMod
      J ell m cap patterns
      (physicalAlternatingSign start) k y seen,
      ∑ tail : physicalOrientedIndexedTrace SP smallMod BP
        bigMod J ell m cap patterns 1 k remaining (start+1)
        (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
          J ell m cap patterns
          (physicalAlternatingSign start) k ab.val)
        (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
          J ell m cap patterns seen ab.val),
        physicalOrientedGEIndexedWeight SP smallMod BP bigMod
          J ell m cap patterns q rho N start Vsmall Vbig muBig
          (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign start)) zeta theta
          (physicalAlternatingSign start) k y ab.val *
        memorySourceIndexedTraceWeight SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig muBig Knu
          zeta theta k N remaining (start+1)
          (physicalOrientedGEIndexedOutput SP smallMod BP bigMod
            J ell m cap patterns
            (physicalAlternatingSign start) k ab.val)
          (physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
            J ell m cap patterns seen ab.val) tail) =
    ∑ ab ∈ S, f ab
  calc
    _ = ∑ ab : PhysicalOrientedGEIndex SP smallMod BP bigMod
        J ell m cap patterns
        (physicalAlternatingSign start) k y seen,
      f ab.val := by
      apply Finset.sum_congr rfl
      intro ab hab
      dsimp only [f, memorySourceIndexedTraceSum]
      rw [Finset.mul_sum]
    _ = ∑ ab ∈ S, f ab :=
      finite_indexed_legal_subtype_sum S f

end Green64FullPhysicalE

end

/-! ## MemorySourceChainIndexedExact -/

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
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Complete indexed expansion of the CURRENT source-faithful chain.
All conditional input Fock averages, OLD injections, ghost birth factorials,
Nu labels, auxiliary draws and both vacua are retained; no fibre theorem
or lifespan reconstruction is assumed. Every edge uses fixed zeta and the
source-correct reversed K callback. -/
theorem memory_source_chain_full_indexed_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (muBig : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ) :
    memorySourceGEChain SP smallMod BP bigMod J ell m patterns cap
      q rho Vsmall Vbig muBig Knu zeta theta k N remaining start
      (fun out _ => physicalVacuum SP smallMod BP bigMod J ell out) y seen =
    memorySourceIndexedTraceSum SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig muBig Knu zeta theta k N remaining start y seen := by
  induction remaining generalizing start y seen with
  | zero =>
    change physicalMarkedSymmetricG SP smallMod BP bigMod J ell cap
      q rho N start Vsmall Vbig muBig y seen
      (fun out _ => physicalVacuum SP smallMod BP bigMod J ell out) = _
    rw [← physicalRawWitnessVisit_eq_source]
    exact physical_oriented_terminal_G_indexed_exact SP smallMod BP bigMod
      J ell cap q rho Vsmall Vbig muBig N start y seen
  | succ r ih =>
    change physicalMarkedSymmetricG SP smallMod BP bigMod J ell cap
      q rho N start Vsmall Vbig muBig y seen
      (fun yg sg => physicalOrientedMarkedSymmetricE SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig muBig
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign start))
        zeta theta (physicalAlternatingSign start) k yg sg
        (memorySourceGEChain SP smallMod BP bigMod J ell m patterns cap
          q rho Vsmall Vbig muBig Knu zeta theta k N r (start+1)
          (fun out _ => physicalVacuum SP smallMod BP bigMod J ell out))) = _
    rw [← physicalOrientedRawWitnessGE_eq_source]
    rw [physical_oriented_GE_indexed_sigma_exact]
    rw [memory_source_indexed_trace_sum_succ]
    apply Finset.sum_congr rfl
    intro ab hab
    rw [ih]
end Green64FullPhysicalE

end

end

/-! ## MemorySourceRootInitialSum -/

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

/-- Push the REPAIRED 1/j! finite Hilbert vacuum mass to RAW
physical initial representatives. The initial global birth test
is preserved exactly: initial ordered active prime lists, not
auxiliary D draws or memory atoms, define the initial seen-set. -/
theorem memory_source_root_initial_state_sum
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    memorySourceRoot SP smallMod BP bigMod
      J ell m patterns cap q rho Vsmall Vbig
      Knu zeta theta k R =
    let N := 2 * R
    let mu := physicalSourceMuTilde BP bigMod q N Vbig
    (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
      ∑ x : FullPhysicalState SP smallMod BP bigMod (J + ell) cap,
        (fullPhysicalMass SP smallMod BP bigMod
          (J + ell) cap Vsmall mu x : ℂ) *
        star (physicalVacuum SP smallMod BP bigMod J ell
          (physicalFockProjection SP smallMod BP bigMod
            (J + ell) cap x)) *
        (if (physicalInitialBirths SP smallMod BP bigMod
             J ell cap x).Nodup then
          memorySourceGEChain SP smallMod BP bigMod
            J ell m patterns cap q rho Vsmall Vbig mu
            Knu zeta theta k N N 0
            (fun out _seen =>
              physicalVacuum SP smallMod BP bigMod J ell out)
            (physicalFockProjection SP smallMod BP bigMod
              (J + ell) cap x)
            (physicalInitialBirths SP smallMod BP bigMod
              J ell cap x).toFinset
         else 0) := by
  classical
  unfold memorySourceRoot
  dsimp only
  simp only [mul_assoc]
  rw [physicalOrbitMass_global_pushforward
    SP smallMod BP bigMod J ell cap Vsmall
    (physicalSourceMuTilde BP bigMod q (2 * R) Vbig)
    (fun y =>
      star (physicalVacuum SP smallMod BP bigMod J ell y) *
        (if (physicalOutputInitialBirths SP smallMod BP bigMod
             J ell y).Nodup then
           memorySourceGEChain SP smallMod BP bigMod
             J ell m patterns cap q rho Vsmall Vbig
             (physicalSourceMuTilde BP bigMod q (2 * R) Vbig)
             Knu zeta theta k (2 * R) (2 * R) 0
             (fun out _seen =>
               physicalVacuum SP smallMod BP bigMod J ell out)
             y (physicalOutputInitialBirths SP smallMod BP bigMod
               J ell y).toFinset
         else 0))]
  simp only [physicalOutputInitialBirths_source_exact]
  rfl

end Green64FullPhysicalE

end

/-! ## MemorySourceRootIndexedWeight -/

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

/-- Fixed-zeta, reversed-K SOURCE-FAITHFUL root scalar on one completely indexed REAL
oriented source witness: b_p product once, true initial Hilbert
mass, source vacuum on initial Fock sector, true global initial
birth-Nodup test, all indexed G/E scalars with Fock conditional
ratios and final G_N vacuum. No cancellation of zero factors. -/
noncomputable def memorySourceRootIndexedWeight
    (q rho : ℝ) (Vsmall : SG → ℝ)
    (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bigMod q N Vbig
  (physicalSourceBaselineProduct BP bigMod q N : ℂ) *
  (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap
    Vsmall mu xt.1 : ℂ) *
  star (physicalVacuum SP smallMod BP bigMod J ell
    (physicalFockProjection SP smallMod BP bigMod
      (J+ell) cap xt.1)) *
  (if (physicalInitialBirths SP smallMod BP bigMod
    J ell cap xt.1).Nodup then
      memorySourceIndexedTraceWeight SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig mu Knu
        zeta theta k N N 0
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap xt.1)
        (physicalInitialBirths SP smallMod BP bigMod
          J ell cap xt.1).toFinset xt.2
    else 0)

end Green64FullPhysicalE

end

/-! ## MemorySourceRootIndexedSum -/

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

/-- Actual exhaustive oriented SOURCE ROOT sum over its recursively
constructed finite Fock/G/E witness tree, including genuine Hilbert
initial mass, SMALL Haar, global b_p and terminal G_N vacuum.
No arbitrary finite input family, postulated Markov kernel or
numerical-prime-set quotient is used. -/
noncomputable def memorySourceFullRootIndexedSum
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  letI : Fintype (PhysicalOrientedRootIndexedTrace
      SP smallMod BP bigMod J ell m cap patterns k R) :=
    physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns k R
  ∑ xt : PhysicalOrientedRootIndexedTrace
      SP smallMod BP bigMod J ell m cap patterns k R,
    memorySourceRootIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R xt

end Green64FullPhysicalE

end

/-! ## MemorySourceRootIndexedExact -/

section

open Classical
open scoped BigOperators

set_option maxHeartbeats 650000

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

/-- SOURCE-FAITHFUL fixed-zeta and reversed-K FULL ROOT COMPLETENESS of the ORIGINAL FINITE
PERMUTATION-CORRECTED physical G_0 E_0 ... G_N source moment.
The root equals the explicit finite sum over recursively indexed
REAL oriented source G/E witnesses and initial ordered Hilbert
states, with terminal vacuum G_N and one numerical birth condition
at every stage.

NO arbitrary W-family completeness assumption, no replacement
of OLD Fock multiplicities by prime sets, no invented Markov kernel.

This is finite root-to-indexed-physical-witness completeness,
NOT the final global lifetime/literal-history pushforward. -/
theorem memory_source_finite_root_full_indexed_exact
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    memorySourceRoot SP smallMod BP bigMod
      J ell m patterns cap q rho Vsmall Vbig Knu
      zeta theta k R =
    memorySourceFullRootIndexedSum SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R := by
  let N := 2*R
  let mu := physicalSourceMuTilde BP bigMod q N Vbig
  let X := FullPhysicalState SP smallMod BP bigMod (J+ell) cap
  let T : X → Type := fun x =>
    physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k N 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset
  letI : (x : X) → Fintype (T x) := fun x =>
    physicalOrientedIndexedTraceFintype SP smallMod BP bigMod
      J ell m cap patterns 1 k N 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset
  let b : ℂ := (physicalSourceBaselineProduct BP bigMod q N : ℂ)
  let a : X → ℂ := fun x =>
    (fullPhysicalMass SP smallMod BP bigMod
      (J+ell) cap Vsmall mu x : ℂ)
  let v : X → ℂ := fun x =>
    star (physicalVacuum SP smallMod BP bigMod J ell
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x))
  let ok : X → Prop := fun x =>
    (physicalInitialBirths SP smallMod BP bigMod
      J ell cap x).Nodup
  let w : (x : X) → T x → ℂ := fun x t =>
    memorySourceIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig mu Knu
      zeta theta k N N 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset t
  have hChain (x : X) :
      memorySourceGEChain SP smallMod BP bigMod
        J ell m patterns cap q rho Vsmall Vbig mu Knu
        zeta theta k N N 0
        (fun out _seen => physicalVacuum SP smallMod BP bigMod
          J ell out)
        (physicalFockProjection SP smallMod BP bigMod
          (J+ell) cap x)
        (physicalInitialBirths SP smallMod BP bigMod
          J ell cap x).toFinset =
      ∑ t : T x, w x t := by
    exact memory_source_chain_full_indexed_exact
      SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig mu Knu zeta theta k N N 0
      (physicalFockProjection SP smallMod BP bigMod
        (J+ell) cap x)
      (physicalInitialBirths SP smallMod BP bigMod
        J ell cap x).toFinset
  have hFubini :=
    finite_root_sigma_trace_fubini
      (X := X) (Y := T) b a v ok w
  calc
    memorySourceRoot SP smallMod BP bigMod
        J ell m patterns cap q rho Vsmall Vbig Knu
        zeta theta k R =
      b * (∑ x : X, (a x * v x) *
        (if ok x then ∑ t : T x, w x t else 0)) := by
      rw [memory_source_root_initial_state_sum]
      change b * (∑ x : X, (a x * v x) *
        (if ok x then
          memorySourceGEChain SP smallMod BP bigMod
            J ell m patterns cap q rho Vsmall Vbig mu Knu
            zeta theta k N N 0
            (fun out _seen => physicalVacuum SP smallMod BP bigMod
              J ell out)
            (physicalFockProjection SP smallMod BP bigMod
              (J+ell) cap x)
            (physicalInitialBirths SP smallMod BP bigMod
              J ell cap x).toFinset
        else 0)) = _
      apply congrArg (fun z : ℂ => b*z)
      apply Finset.sum_congr rfl
      intro x hx
      rw [hChain x]
    _ = ∑ xt : (Σ x : X, T x),
        b * a xt.1 * v xt.1 *
          (if ok xt.1 then w xt.1 xt.2 else 0) := by
      convert hFubini using 1
      apply congrArg (fun z : ℂ => b*z)
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hOk : ok x <;> simp [hOk]
      all_goals
        apply Finset.sum_congr (by ext xt; simp)
        intro xt hxt
        by_cases hOk : ok xt.1 <;> simp [hOk]
    _ = memorySourceFullRootIndexedSum SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu
        zeta theta k R := by
      unfold memorySourceFullRootIndexedSum
      apply Finset.sum_congr rfl
      intro xt hxt
      rfl

end Green64FullPhysicalE

end

/-! ## MemorySourceBridgeExpectedStatements -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- No support/reconstruction premise: every schedule obligation below follows
from the literal nonzero frozen coefficient. -/
theorem memory_nonzero_frozen_schedule_operations
    (p : ℕ) (eta : ℕ → ℝ) (h : ℕ → ZMod p) (A : Finset ℕ)
    (N : ℕ) (l : MemoryLifespanChoice (N+1))
    (hn : memoryFrozenPrimeTerm p eta h A (N+1) l ≠ 0) (i : ℕ) :
    (memoryScheduleAfter A l i ↔
      (memoryScheduleBefore A l i ∧ ¬ memoryScheduleTerminate A l i) ∨
        memoryScheduleGhostBirth A l i) ∧
    (memoryScheduleBefore A l (i+1) ↔
      (memoryScheduleAfter A l i ∨ memoryScheduleStore A l i) ∧
        ¬ memorySchedulePromote A l i) ∧
    (memorySchedulePromote A l i →
      memoryScheduleAfter A l i ∧ ¬ memoryScheduleStore A l i) ∧
    (¬ memoryScheduleBefore A l 0 ∧ ¬ memoryScheduleAfter A l N) := by
  have hs := memory_frozen_nonzero_schedule_support p eta h A (N+1) l hn
  exact ⟨memory_schedule_G_exact p h A l hs i,
    memory_schedule_E_exact p h A l hs i,
    memory_schedule_promotion_is_old p h A l hs i,
    memory_schedule_vacua A l⟩

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Trusted expected shape of the corrected root expansion, stated independently
of its proof. This is not the missing MemoryIdentityTarget theorem. -/
theorem memory_source_root_expected_statement
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    memorySourceRoot SP smallMod BP bigMod J ell m patterns cap
      q rho Vsmall Vbig Knu zeta theta k R =
    memorySourceFullRootIndexedSum SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R :=
  memory_source_finite_root_full_indexed_exact SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R

/-- Head-edge schedule audit: the source root expansion must use this fixed
zeta and this reverse-argument callback at EVERY start, including start=0. -/
theorem memory_source_head_schedule_expected_statement
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N n start : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (seen : Finset ℕ) :
    memorySourceGEChain SP smallMod BP bigMod J ell m patterns cap
      q rho Vsmall Vbig mu Knu zeta theta k N (n+1) start F y seen =
    physicalMarkedSymmetricG SP smallMod BP bigMod J ell cap
      q rho N start Vsmall Vbig mu y seen
      (fun yg sg => physicalOrientedMarkedSymmetricE SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig mu
        (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign start))
        zeta theta (physicalAlternatingSign start) k yg sg
        (memorySourceGEChain SP smallMod BP bigMod J ell m patterns cap
          q rho Vsmall Vbig mu Knu zeta theta k N n (start+1) F)) := rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryCanonicalFockRepresentative -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]

/-- Actual prime-residue atoms, not a proxy pending-prime set. -/
def memoryCanonicalPendingList (A : P → Finset ℕ) {n : ℕ}
    (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ)
    (before : Bool) (i : ℕ) : List (Green64Fock.Atom P modulus) :=
  ((Finset.univ : Finset P).filter (fun p =>
    if before then memoryScheduleBefore (A p) (life p) i
    else memoryScheduleAfter (A p) (life p) i)).toList.map
      (fun p => ⟨p, memoryScheduleResidue (modulus p)
        (fun t => (offset t : ZMod (modulus p))) (life p) i⟩)

theorem memory_canonical_pending_length_bound
    (A : P → Finset ℕ) {n : ℕ} (life : P → MemoryLifespanChoice n)
    (offset : ℕ → ℤ) (before : Bool) (i : ℕ) :
    (memoryCanonicalPendingList modulus A life offset before i).length ≤ Fintype.card P := by
  simp only [memoryCanonicalPendingList, List.length_map, Finset.length_toList]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

/-- Source saturated cap produces a REAL ordered Fock representative of the
canonical atom list, including its residues, without a reconstruction axiom. -/
def memoryCanonicalPendingFock (A : P → Finset ℕ) {n : ℕ}
    (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ)
    (before : Bool) (i cap : ℕ) (hcap : Fintype.card P ≤ cap) :
    Green64Fock.FockState (Green64Fock.Atom P modulus) cap :=
  (physicalFockStateListEquiv (Green64Fock.Atom P modulus) cap).symm
    ⟨memoryCanonicalPendingList modulus A life offset before i,
      (memory_canonical_pending_length_bound modulus A life offset before i).trans hcap⟩

theorem memory_canonical_Fock_list_exact
    (A : P → Finset ℕ) {n : ℕ} (life : P → MemoryLifespanChoice n)
    (offset : ℕ → ℤ) (before : Bool) (i cap : ℕ) (hcap : Fintype.card P ≤ cap) :
    Green64Fock.fockToList (memoryCanonicalPendingFock modulus A life offset before i cap hcap) =
      memoryCanonicalPendingList modulus A life offset before i := by
  exact congrArg Subtype.val
    ((physicalFockStateListEquiv (Green64Fock.Atom P modulus) cap).apply_symm_apply _)

theorem memory_canonical_Fock_multiset_exact
    (A : P → Finset ℕ) {n : ℕ} (life : P → MemoryLifespanChoice n)
    (offset : ℕ → ℤ) (before : Bool) (i cap : ℕ) (hcap : Fintype.card P ≤ cap) :
    Green64Fock.fockMultiset (memoryCanonicalPendingFock modulus A life offset before i cap hcap) =
      (memoryCanonicalPendingList modulus A life offset before i : Multiset (Green64Fock.Atom P modulus)) := by
  exact congrArg (fun l : List (Green64Fock.Atom P modulus) => (l : Multiset (Green64Fock.Atom P modulus)))
    (memory_canonical_Fock_list_exact modulus A life offset before i cap hcap)

/-- Both boundary memories are empty for every lifespan assignment. -/
theorem memory_canonical_pending_vacua (A : P → Finset ℕ) {N : ℕ}
    (life : P → MemoryLifespanChoice (N+1)) (offset : ℕ → ℤ) :
    memoryCanonicalPendingList modulus A life offset true 0 = [] ∧
      memoryCanonicalPendingList modulus A life offset false N = [] := by
  have hb (p : P) := (memory_schedule_vacua (A p) (life p)).1
  have ha (p : P) := (memory_schedule_vacua (A p) (life p)).2
  simp [memoryCanonicalPendingList, hb, ha]
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveGGroupLift -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

def memoryGhostBirthSet : Finset P :=
  Finset.univ.filter (fun p => memoryScheduleGhostBirth (A p) (life p) i)

def memoryGhostDeathIndices (old : List (Green64Fock.Atom P modulus)) :
    Finset (Fin old.length) :=
  Finset.univ.filter (fun j => memoryScheduleTerminate
    (A (old.get j).1) (life (old.get j).1) i)

theorem memory_pending_mem_iff (before : Bool) (z : Green64Fock.Atom P modulus) :
    z ∈ memoryCanonicalPendingList modulus A life offset before i ↔
      (if before then memoryScheduleBefore (A z.1) (life z.1) i
       else memoryScheduleAfter (A z.1) (life z.1) i) ∧
      z.2 = memoryScheduleResidue (modulus z.1)
        (fun t => (offset t : ZMod (modulus z.1))) (life z.1) i := by
  unfold memoryCanonicalPendingList
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, he⟩
    cases he
    exact ⟨hp, rfl⟩
  · rintro ⟨hp, hr⟩
    refine ⟨z.1, hp, ?_⟩
    exact Sigma.ext rfl (heq_of_eq hr.symm)

theorem memory_pending_primes_nodup (before : Bool) :
    ((memoryCanonicalPendingList modulus A life offset before i).map
      (fun z => z.1)).Nodup := by
  simp only [memoryCanonicalPendingList, List.map_map, Function.comp_def]
  simpa using (Finset.univ.filter (fun p : P =>
    if before then memoryScheduleBefore (A p) (life p) i
    else memoryScheduleAfter (A p) (life p) i)).nodup_toList

theorem memory_ordered_pending_get_spec
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (j : Fin old.length) :
    memoryScheduleBefore (A (old.get j).1) (life (old.get j).1) i ∧
      (old.get j).2 = memoryScheduleResidue (modulus (old.get j).1)
        (fun t => (offset t : ZMod (modulus (old.get j).1)))
        (life (old.get j).1) i := by
  exact (memory_pending_mem_iff modulus A life offset i true (old.get j)).mp
    (hOld.mem_iff.mp (old.get_mem j))

theorem memory_ghost_death_indices_legal
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i)) :
    memoryGhostDeathIndices modulus A life i old ∈
      (Green64MemoryGhostOp.zeroOld old
        (fun z : Green64Fock.Atom P modulus => z.2 = 0)).powerset := by
  apply Finset.mem_powerset.mpr
  intro j hj
  have hd : memoryScheduleTerminate (A (old.get j).1) (life (old.get j).1) i :=
    (Finset.mem_filter.mp hj).2
  have hr := (memory_ordered_pending_get_spec modulus A life offset i old hOld j).2
  have hz := memory_schedule_ghost_endpoints_zero (modulus (old.get j).1)
    (fun t => (offset t : ZMod (modulus (old.get j).1)))
    (A (old.get j).1) (life (old.get j).1) (hs _) i (Or.inl hd)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.trans hz⟩

def memoryGhostFreshAtoms
    (e : Fin (memoryGhostBirthSet A life i).card ≃ ↥(memoryGhostBirthSet A life i)) :
    Fin (memoryGhostBirthSet A life i).card → Green64Fock.Atom P modulus :=
  fun j => Green64Fock.zeroAtom (e j).1

theorem memory_ghost_birth_card_bound :
    (memoryGhostBirthSet A life i).card ≤ Fintype.card P :=
  (Finset.card_le_card (Finset.subset_univ _)).trans_eq Finset.card_univ

/-- The source OLD subset is generated from deaths for this ordering.
Fresh births carry exactly zero residues and the ORIGINAL source b bound. -/
def memoryGhostLiftChoice
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (cap : ℕ) (hcap : Fintype.card P ≤ cap)
    (e : Fin (memoryGhostBirthSet A life i).card ≃ ↥(memoryGhostBirthSet A life i)) :
    GhostWitnessChoice old (fun z : Green64Fock.Atom P modulus => z.2 = 0) cap :=
  ⟨⟨memoryGhostDeathIndices modulus A life i old,
    memory_ghost_death_indices_legal modulus A life offset i hs old hOld⟩,
   ⟨⟨(memoryGhostBirthSet A life i).card,
     Nat.lt_succ_iff.mpr ((memory_ghost_birth_card_bound A life i).trans hcap)⟩,
    memoryGhostFreshAtoms modulus A life i e⟩⟩

theorem memory_ghost_after_primes_nodup
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (e : Fin (memoryGhostBirthSet A life i).card ≃ ↥(memoryGhostBirthSet A life i)) :
    ((Green64MemoryGhostOp.afterGhost old
      (memoryGhostDeathIndices modulus A life i old)
      (memoryGhostFreshAtoms modulus A life i e)).map (fun z => z.1)).Nodup := by
  have hpr : (old.map (fun z => z.1)).Nodup :=
    (hOld.map (fun z => z.1)).nodup_iff.mpr
      (memory_pending_primes_nodup modulus A life offset i true)
  have hget : Function.Injective (fun j : Fin old.length => (old.get j).1) := by
    apply List.nodup_ofFn.mp
    have he : List.ofFn (fun j : Fin old.length => (old.get j).1) =
        old.map (fun z => z.1) := by
      calc
        _ = (List.ofFn old.get).map (fun z => z.1) := List.map_ofFn.symm
        _ = _ := by rw [List.ofFn_get]
    rw [he]
    exact hpr
  unfold Green64MemoryGhostOp.afterGhost
  simp only [List.map_append, List.map_map, Function.comp_def, List.map_ofFn]
  apply List.nodup_append.mpr
  refine ⟨List.Nodup.map hget ((List.nodup_finRange _).filter _), ?_, ?_⟩
  · apply List.nodup_ofFn.mpr
    intro a b he
    apply e.injective
    exact Subtype.ext he
  · intro p hp q hq heq
    obtain ⟨j, hj, hjp⟩ := List.mem_map.mp hp
    obtain ⟨k, hkq⟩ := List.mem_ofFn.mp hq
    have hb := (memory_ordered_pending_get_spec modulus A life offset i old hOld j).1
    have hf : memoryScheduleGhostBirth (A (e k).1) (life (e k).1) i :=
      (Finset.mem_filter.mp (e k).2).2
    have hpq : (old.get j).1 = (e k).1 := hjp.trans (heq.trans hkq.symm)
    rw [hpq] at hb
    cases hl : life (e k).1 with
    | none => simp [hl, memoryScheduleBefore] at hb
    | some jd =>
      simp only [hl, memoryScheduleBefore] at hb
      simp only [hl, memoryScheduleGhostBirth] at hf
      omega

theorem memory_ghost_after_length_bound
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (e : Fin (memoryGhostBirthSet A life i).card ≃ ↥(memoryGhostBirthSet A life i)) :
    (Green64MemoryGhostOp.afterGhost old
      (memoryGhostDeathIndices modulus A life i old)
      (memoryGhostFreshAtoms modulus A life i e)).length ≤ Fintype.card P := by
  have h := (memory_ghost_after_primes_nodup modulus A life offset i old hOld e).length_le_card
  simpa only [List.length_map] using h
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveGOutput -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

theorem memory_ghost_fresh_mem_iff
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (e : Fin (memoryGhostBirthSet A life i).card ≃ ↥(memoryGhostBirthSet A life i))
    (z : Green64Fock.Atom P modulus) :
    z ∈ List.ofFn (memoryGhostFreshAtoms modulus A life i e) ↔
      memoryScheduleGhostBirth (A z.1) (life z.1) i ∧
      z.2 = memoryScheduleResidue (modulus z.1)
        (fun t => (offset t : ZMod (modulus z.1))) (life z.1) i := by
  constructor
  · intro hz
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hz
    have hb := (Finset.mem_filter.mp (e j).2).2
    have hzero := memory_schedule_ghost_endpoints_zero (modulus (e j).1)
      (fun t => (offset t : ZMod (modulus (e j).1)))
      (A (e j).1) (life (e j).1) (hs _) i (Or.inr hb)
    rw [← hj]
    exact ⟨hb, hzero.symm⟩
  · rintro ⟨hb, hr⟩
    let p : ↥(memoryGhostBirthSet A life i) :=
      ⟨z.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
    refine List.mem_ofFn.mpr ⟨e.symm p, ?_⟩
    have hz := memory_schedule_ghost_endpoints_zero (modulus z.1)
      (fun t => (offset t : ZMod (modulus z.1))) (A z.1) (life z.1)
      (hs _) i (Or.inr hb)
    have he : (e (e.symm p)).1 = z.1 := congrArg Subtype.val (e.apply_symm_apply p)
    unfold memoryGhostFreshAtoms
    rw [he]
    exact Sigma.ext rfl (heq_of_eq (hr.trans hz).symm)

theorem memory_ghost_survivor_mem_iff
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (z : Green64Fock.Atom P modulus) :
    z ∈ ((List.finRange old.length).filter
      (fun j => j ∉ memoryGhostDeathIndices modulus A life i old)).map old.get ↔
      memoryScheduleBefore (A z.1) (life z.1) i ∧
      ¬ memoryScheduleTerminate (A z.1) (life z.1) i ∧
      z.2 = memoryScheduleResidue (modulus z.1)
        (fun t => (offset t : ZMod (modulus z.1))) (life z.1) i := by
  constructor
  · intro hz
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hz
    have hnot : ¬ memoryScheduleTerminate (A (old.get j).1) (life (old.get j).1) i := by
      have hn : j ∉ memoryGhostDeathIndices modulus A life i old := by
        simpa using (List.mem_filter.mp hj).2
      simpa [memoryGhostDeathIndices] using hn
    have hspec := memory_ordered_pending_get_spec modulus A life offset i old hOld j
    rw [← he]
    exact ⟨hspec.1, hnot, hspec.2⟩
  · rintro ⟨hb, hd, hr⟩
    have hz : z ∈ old := hOld.mem_iff.mpr
      ((memory_pending_mem_iff modulus A life offset i true z).mpr ⟨hb, hr⟩)
    obtain ⟨j, he⟩ := List.mem_iff_get.mp hz
    refine List.mem_map.mpr ⟨j, ?_, he⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange j, ?_⟩
    have hn : j ∉ memoryGhostDeathIndices modulus A life i old := by
      intro hj
      have ht := (Finset.mem_filter.mp hj).2
      rw [he] at ht
      exact hd ht
    exact decide_eq_true hn

/-- Exact atom multiset of the constructed source G output for EVERY
input representative and EVERY ordering of the ghost-born batch. -/
theorem memory_ghost_after_perm_canonical
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (e : Fin (memoryGhostBirthSet A life i).card ≃ ↥(memoryGhostBirthSet A life i)) :
    (Green64MemoryGhostOp.afterGhost old
      (memoryGhostDeathIndices modulus A life i old)
      (memoryGhostFreshAtoms modulus A life i e)).Perm
        (memoryCanonicalPendingList modulus A life offset false i) := by
  apply (List.perm_ext_iff_of_nodup
    ((memory_ghost_after_primes_nodup modulus A life offset i old hOld e).of_map
      (fun z => z.1))
    ((memory_pending_primes_nodup modulus A life offset i false).of_map
      (fun z => z.1))).mpr
  intro z
  rw [Green64MemoryGhostOp.afterGhost, List.mem_append,
    memory_ghost_survivor_mem_iff modulus A life offset i old hOld,
    memory_ghost_fresh_mem_iff modulus A life offset i hs e,
    memory_pending_mem_iff modulus A life offset i false]
  have hg := memory_schedule_G_exact (modulus z.1)
    (fun t => (offset t : ZMod (modulus z.1))) (A z.1) (life z.1) (hs _) i
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hg]
  tauto

/-- A real bounded Fock state, carrying the exact source output LIST. -/
def memoryGhostOutputFock
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (cap : ℕ) (hcap : Fintype.card P ≤ cap)
    (e : Fin (memoryGhostBirthSet A life i).card ≃ ↥(memoryGhostBirthSet A life i)) :
    Green64Fock.FockState (Green64Fock.Atom P modulus) cap :=
  (physicalFockStateListEquiv (Green64Fock.Atom P modulus) cap).symm
    ⟨Green64MemoryGhostOp.afterGhost old
      (memoryGhostDeathIndices modulus A life i old)
      (memoryGhostFreshAtoms modulus A life i e),
     (memory_ghost_after_length_bound modulus A life offset i old hOld e).trans hcap⟩

theorem memory_ghost_output_list_exact
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (cap : ℕ) (hcap : Fintype.card P ≤ cap)
    (e : Fin (memoryGhostBirthSet A life i).card ≃ ↥(memoryGhostBirthSet A life i)) :
    Green64Fock.fockToList (memoryGhostOutputFock modulus A life offset i old hOld cap hcap e) =
      Green64MemoryGhostOp.afterGhost old (memoryGhostDeathIndices modulus A life i old)
        (memoryGhostFreshAtoms modulus A life i e) := by
  exact congrArg Subtype.val ((physicalFockStateListEquiv
    (Green64Fock.Atom P modulus) cap).apply_symm_apply _)
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveGLiftTarget -/

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
variable (J ell : ℕ) (cap : BG → ℕ)
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

def memoryBornBeforeValues : Finset ℕ :=
  ((Finset.univ : Finset (Sigma BP)).filter (fun gp =>
    match life gp.1 gp.2 with
    | none => False
    | some jd => jd.1.val < i)).image (fun gp => bigMod gp.1 gp.2)

 /-- Chronological input seen set at G_i: active births at visit i have
already occurred in the preceding E row (or the initial active root).
Ghost births at i have not yet occurred. -/
def memorySeenBeforeGValues : Finset ℕ :=
  ((Finset.univ : Finset (Sigma BP)).filter (fun gp =>
    match life gp.1 gp.2 with
    | none => False
    | some jd => jd.1.val < i ∨ (jd.1.val = i ∧ i ∈ A gp.1 gp.2))).image
      (fun gp => bigMod gp.1 gp.2)

/-- Concrete source witness in the original dependent FULL carrier. -/
def memoryPrimitiveGWitness
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
      ↥(memoryGhostBirthSet (A g) (life g) i)) :
    FullGhostWitness SP smallMod BP bigMod (J+ell) cap x :=
  fun g => memoryGhostLiftChoice (bigMod g) (A g) (life g) offset i
    (hs g) _ (hOld g) (cap g) (hcap g) (e g)

def memoryPrimitiveGOutput
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
      ↥(memoryGhostBirthSet (A g) (life g) i)) :
    FullPhysicalState SP smallMod BP bigMod (J+ell) cap :=
  (x.1, fun g => ((x.2 g).1,
    memoryGhostOutputFock (bigMod g) (A g) (life g) offset i
      _ (hOld g) (cap g) (hcap g) (e g)))

theorem memory_primitive_G_fresh_list_exact
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
      ↥(memoryGhostBirthSet (A g) (life g) i)) :
    physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap x
      (memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap A life offset i hs x hOld hcap e) =
      (Finset.univ : Finset BG).toList.flatMap
        (fun g => List.ofFn (fun j => bigMod g (e g j).1)) := by
  unfold physicalGhostFreshBirths memoryPrimitiveGWitness memoryGhostLiftChoice
  simp only [memoryGhostFreshAtoms, List.map_ofFn, Function.comp_def, Green64Fock.zeroAtom]

/-- Birth distinctness follows from the SOURCE numerical-group injectivity,
not from a new assertion about an augmented occurrence map. -/
theorem memory_primitive_G_batch_eligible
    (hinj : Function.Injective (fun gp : Sigma BP => bigMod gp.1 gp.2))
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
      ↥(memoryGhostBirthSet (A g) (life g) i)) :
    physicalGhostBatchEligible SP smallMod BP bigMod (J+ell) cap x
      (memorySeenBeforeGValues BP bigMod A life i)
      (memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap A life offset i hs x hOld hcap e) := by
  unfold physicalGhostBatchEligible
  rw [memory_primitive_G_fresh_list_exact]
  constructor
  · apply List.nodup_flatMap.mpr
    constructor
    · intro g hg
      apply List.nodup_ofFn.mpr
      intro j k he
      have hv : (⟨g, (e g j).1⟩ : Sigma BP) = ⟨g, (e g k).1⟩ := hinj he
      apply (e g).injective
      exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp hv).2)
    · apply (Finset.univ : Finset BG).nodup_toList.imp
      intro g h hne
      intro v hv hw
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hv
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hw
      have he : (⟨g, (e g j).1⟩ : Sigma BP) = ⟨h, (e h k).1⟩ :=
        hinj (hj.trans hk.symm)
      exact hne (congrArg Sigma.fst he)
  · apply Finset.disjoint_left.mpr
    intro v hv hf
    obtain ⟨gp, hgp, hgv⟩ := Finset.mem_image.mp hv
    have hbefore := (Finset.mem_filter.mp hgp).2
    have hf' := List.mem_toFinset.mp hf
    obtain ⟨g, hg, hvg⟩ := List.mem_flatMap.mp hf'
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hvg
    have he : gp = (⟨g, (e g j).1⟩ : Sigma BP) := hinj (hgv.trans hj.symm)
    rw [he] at hbefore
    have hbirth : memoryScheduleGhostBirth (A g (e g j).1) (life g (e g j).1) i :=
      (Finset.mem_filter.mp (e g j).2).2
    cases hl : life g (e g j).1 with
    | none => simp [hl, memoryScheduleGhostBirth] at hbirth
    | some jd =>
      simp only [hl] at hbefore
      simp only [hl, memoryScheduleGhostBirth] at hbirth
      rcases hbefore with hb | ⟨hb, ha⟩
      · omega
      · exact hbirth.2 ha

/-- BOTH conjuncts of the exact indexed G carrier, with its exact ordered output. -/
theorem memory_primitive_G_indexed_eligible
    (hinj : Function.Injective (fun gp : Sigma BP => bigMod gp.1 gp.2))
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
      ↥(memoryGhostBirthSet (A g) (life g) i)) :
    (⟨x, memoryPrimitiveGOutput SP smallMod BP bigMod J ell cap A life offset i x hOld hcap e,
      memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap A life offset i hs x hOld hcap e⟩ :
      Σ x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      Σ yg : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      FullGhostWitness SP smallMod BP bigMod (J+ell) cap x) ∈
      physicalGIndexedEligibleFibre SP smallMod BP bigMod J ell cap
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
        (memorySeenBeforeGValues BP bigMod A life i) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, rfl, ?_⟩
  exact memory_primitive_G_batch_eligible SP smallMod BP bigMod J ell cap
    A life offset i hinj hs x hOld hcap e
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveGCounts -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

def memoryGhostDeathSet : Finset P :=
  Finset.univ.filter (fun p => memoryScheduleTerminate (A p) (life p) i)

def memoryZeroBeforeSet : Finset P :=
  Finset.univ.filter (fun p => memoryScheduleBefore (A p) (life p) i ∧
    memoryScheduleResidue (modulus p) (fun t => (offset t : ZMod (modulus p))) (life p) i = 0)

def memoryContinuingZeroSet : Finset P :=
  memoryZeroBeforeSet modulus A life offset i \ memoryGhostDeathSet A life i

theorem memory_schedule_termination_is_before
    (p : ℕ) (h : ℕ → ZMod p) (B : Finset ℕ)
    (l : MemoryLifespanChoice n) (hs : MemoryFrozenScheduleSupport p h B l)
    (ht : memoryScheduleTerminate B l i) :
    memoryScheduleBefore B l i := by
  cases l with
  | none => simp [memoryScheduleTerminate] at ht
  | some jd =>
    simp only [memoryScheduleTerminate] at ht
    simp only [memoryScheduleBefore]
    have hneq : jd.1.val ≠ jd.2.val := by
      intro he
      exact ht.2 (ht.1 ▸ (he ▸ hs.2.2.2 he))
    exact ⟨by have := hs.1; omega, by omega, ht.2⟩

theorem memory_ghost_deaths_subset_zero_before
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p)) :
    memoryGhostDeathSet A life i ⊆ memoryZeroBeforeSet modulus A life offset i := by
  intro p hp
  have hd := (Finset.mem_filter.mp hp).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact ⟨memory_schedule_termination_is_before i (modulus p)
    (fun t => (offset t : ZMod (modulus p))) (A p) (life p) (hs p) hd,
    memory_schedule_ghost_endpoints_zero (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p) (hs p) i (Or.inl hd)⟩

/-- Ordered OLD prime indices have canonical finite-set cardinalities. -/
theorem memory_pending_filtered_indices_card
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (pred : P → Prop) :
    (Finset.univ.filter (fun j : Fin old.length => pred (old.get j).1)).card =
      (Finset.univ.filter (fun p : P =>
        memoryScheduleBefore (A p) (life p) i ∧ pred p)).card := by
  have hpr : (old.map (fun z => z.1)).Nodup :=
    (hOld.map (fun z => z.1)).nodup_iff.mpr
      (memory_pending_primes_nodup modulus A life offset i true)
  have hget : Function.Injective (fun j : Fin old.length => (old.get j).1) := by
    apply List.nodup_ofFn.mp
    have he : List.ofFn (fun j : Fin old.length => (old.get j).1) =
        old.map (fun z => z.1) := by
      calc
        _ = (List.ofFn old.get).map (fun z => z.1) := List.map_ofFn.symm
        _ = _ := by rw [List.ofFn_get]
    rw [he]; exact hpr
  apply Finset.card_bij (fun j _ => (old.get j).1)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (memory_ordered_pending_get_spec modulus A life offset i old hOld j).1,
      (Finset.mem_filter.mp hj).2⟩
  · intro j hj k hk he
    exact hget he
  · intro p hp
    have hb := (Finset.mem_filter.mp hp).2
    let z : Green64Fock.Atom P modulus := ⟨p,
      memoryScheduleResidue (modulus p) (fun t => (offset t : ZMod (modulus p))) (life p) i⟩
    have hz : z ∈ old := hOld.mem_iff.mpr
      ((memory_pending_mem_iff modulus A life offset i true z).mpr ⟨hb.1, rfl⟩)
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hz
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [hj]; exact hb.2
    · exact congrArg Sigma.fst hj

theorem memory_ghost_death_count_exact
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i)) :
    (memoryGhostDeathIndices modulus A life i old).card = (memoryGhostDeathSet A life i).card := by
  rw [memoryGhostDeathIndices, memory_pending_filtered_indices_card modulus A life offset i old hOld
    (fun p => memoryScheduleTerminate (A p) (life p) i)]
  congr 1
  apply Finset.filter_congr
  intro p hp
  exact ⟨And.right, fun hd => ⟨memory_schedule_termination_is_before i (modulus p)
    (fun t => (offset t : ZMod (modulus p))) (A p) (life p) (hs p) hd, hd⟩⟩

theorem memory_ghost_zero_count_exact
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i)) :
    (Green64MemoryGhostOp.zeroOld old (fun z : Green64Fock.Atom P modulus => z.2 = 0)).card =
      (memoryZeroBeforeSet modulus A life offset i).card := by
  unfold Green64MemoryGhostOp.zeroOld memoryZeroBeforeSet
  have he : (Finset.univ.filter (fun j : Fin old.length => (old.get j).2 = 0)) =
      Finset.univ.filter (fun j : Fin old.length =>
        memoryScheduleResidue (modulus (old.get j).1)
          (fun t => (offset t : ZMod (modulus (old.get j).1))) (life (old.get j).1) i = 0) := by
    apply Finset.filter_congr
    intro j hj
    rw [(memory_ordered_pending_get_spec modulus A life offset i old hOld j).2]
  rw [he]
  convert memory_pending_filtered_indices_card modulus A life offset i old hOld
    (fun p => memoryScheduleResidue (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (life p) i = 0) using 1
  all_goals
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem memory_ghost_continuing_zero_count_exact
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i)) :
    (Green64MemoryGhostOp.zeroOld old (fun z : Green64Fock.Atom P modulus => z.2 = 0)).card -
      (memoryGhostDeathIndices modulus A life i old).card =
        (memoryContinuingZeroSet modulus A life offset i).card := by
  rw [memory_ghost_zero_count_exact modulus A life offset i old hOld,
    memory_ghost_death_count_exact modulus A life offset i hs old hOld]
  exact (Finset.card_sdiff_of_subset
    (memory_ghost_deaths_subset_zero_before modulus A life offset i hs)).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveGCoefficient -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

/-- Exact primitive source coefficient, not a rescaled proxy; independent
of the incoming order and the chosen ordering of the ghost batch. -/
theorem memory_ghost_lift_coefficient_exact
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (cap : ℕ) (hcap : Fintype.card P ≤ cap)
    (e : Fin (memoryGhostBirthSet A life i).card ≃ ↥(memoryGhostBirthSet A life i))
    (alpha chi gamma : ℂ) (mu : P → ℝ) :
    ghostWitnessTerm old
      (Green64Fock.fockToList (memoryGhostOutputFock modulus A life offset i old hOld cap hcap e))
      (fun z : Green64Fock.Atom P modulus => z.2 = 0) cap alpha chi gamma
      (Green64Fock.sourceBirthNu (fun p => (mu p : ℂ)))
      (memoryGhostLiftChoice modulus A life offset i hs old hOld cap hcap e) =
    alpha ^ (memoryGhostDeathSet A life i).card *
    chi ^ (memoryContinuingZeroSet modulus A life offset i).card *
    (1 / (Nat.factorial (memoryGhostBirthSet A life i).card : ℂ)) *
    gamma ^ (memoryGhostBirthSet A life i).card *
      ∏ p ∈ memoryGhostBirthSet A life i, (mu p : ℂ) := by
  rw [memory_ghost_output_list_exact]
  unfold ghostWitnessTerm
  simp only [memoryGhostLiftChoice, ↓reduceIte, Green64MemoryGhostOp.sourceGhostTerm]
  rw [memory_ghost_continuing_zero_count_exact modulus A life offset i hs old hOld,
    memory_ghost_death_count_exact modulus A life offset i hs old hOld]
  congr 1
  simp only [memoryGhostFreshAtoms, Green64Fock.sourceBirthNu, Green64Fock.birthMass_zero]
  exact ((e.prod_comp (fun p => (mu p.1 : ℂ))).trans
    (Finset.prod_coe_sort (memoryGhostBirthSet A life i) (fun p => (mu p : ℂ))))

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- Literal all-group source G branch coefficient in the ACTUAL FULL carrier. -/
theorem memory_primitive_G_branch_coefficient_exact
    (A : (g : BG) → BP g → Finset ℕ)
    (life : (g : BG) → BP g → MemoryLifespanChoice n)
    (offset : ℕ → ℤ) (i : ℕ)
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
      ↥(memoryGhostBirthSet (A g) (life g) i))
    (q rho : ℝ) (N : ℕ) (Vbig : BG → ℝ) (mu : (g : BG) → BP g → ℝ) :
    physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho N i Vbig mu x
      (memoryPrimitiveGOutput SP smallMod BP bigMod J ell cap A life offset i x hOld hcap e)
      (memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap A life offset i hs x hOld hcap e) =
    ∏ g : BG,
      (-((sourceVisitEta q N i : ℝ) : ℂ) / (rho : ℂ)) ^
        (memoryGhostDeathSet (A g) (life g) i).card *
      (((sourceVisitQ q N i : ℝ) : ℂ) / (rho : ℂ)^2) ^
        (memoryContinuingZeroSet (bigMod g) (A g) (life g) offset i).card *
      (1 / (Nat.factorial (memoryGhostBirthSet (A g) (life g) i).card : ℂ)) *
      (-((sourceVisitEta q N i : ℝ) : ℂ) * (Vbig g : ℂ) / (rho : ℂ)) ^
        (memoryGhostBirthSet (A g) (life g) i).card *
      (∏ p ∈ memoryGhostBirthSet (A g) (life g) i, (mu g p : ℂ)) := by
  unfold physicalGBranchTerm
  rw [if_pos (show x.1 = (memoryPrimitiveGOutput SP smallMod BP bigMod J ell cap
    A life offset i x hOld hcap e).1 ∧
    ∀ g, (x.2 g).1 = ((memoryPrimitiveGOutput SP smallMod BP bigMod J ell cap
      A life offset i x hOld hcap e).2 g).1 from ⟨rfl, fun g => rfl⟩)]
  apply Finset.prod_congr rfl
  intro g hg
  exact memory_ghost_lift_coefficient_exact (bigMod g) (A g) (life g) offset i
    (hs g) _ (hOld g) (cap g) (hcap g) (e g) _ _ _ (mu g)
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveGSourceLift -/

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
variable (J ell : ℕ) (cap : BG → ℕ)

/-- Actual physical coefficient with the source muTilde, all original
rho/V/factorial factors, and canonical prime counts. -/
def memoryPrimitiveGSourceCoefficient (q rho : ℝ) (N i : ℕ) (Vbig : BG → ℝ)
    (A : (g : BG) → BP g → Finset ℕ)
    (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
    (offset : ℕ → ℤ) : ℂ :=
  ∏ g : BG,
    (-((sourceVisitEta q N i : ℝ) : ℂ) / (rho : ℂ)) ^
      (memoryGhostDeathSet (A g) (life g) i).card *
    (((sourceVisitQ q N i : ℝ) : ℂ) / (rho : ℂ)^2) ^
      (memoryContinuingZeroSet (bigMod g) (A g) (life g) offset i).card *
    (1 / (Nat.factorial (memoryGhostBirthSet (A g) (life g) i).card : ℂ)) *
    (-((sourceVisitEta q N i : ℝ) : ℂ) * (Vbig g : ℂ) / (rho : ℂ)) ^
      (memoryGhostBirthSet (A g) (life g) i).card *
    (∏ p ∈ memoryGhostBirthSet (A g) (life g) i,
      (physicalSourceMuTilde BP bigMod q N Vbig g p : ℂ))

/-- The first missing G lifting obligation is discharged on the REAL dependent
carrier. Support, cap and numerical injectivity are derived from the literal
nonzero frozen terms and the original MemorySourceDomain. This proves a local
forward lift for every ordered input and ghost ordering, not exhaustive inverse
or MemoryIdentityTarget. -/
theorem memory_source_primitive_G_lift
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (k : ℤ) (R : ℕ)
    (hdomain : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (N i : ℕ) (A : (g : BG) → BP g → Finset ℕ)
    (life : (g : BG) → BP g → MemoryLifespanChoice (N+1))
    (offset : ℕ → ℤ)
    (hn : ∀ g p, memoryFrozenPrimeTerm (bigMod g p) (sourceVisitEta q N)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (N+1) (life g p) ≠ 0)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i))
    (e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
      ↥(memoryGhostBirthSet (A g) (life g) i)) :
    ∃ yg : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
    ∃ c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x,
      (⟨x, yg, c⟩ :
        Σ xx : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        Σ yy : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
          FullGhostWitness SP smallMod BP bigMod (J+ell) cap xx) ∈
        physicalGIndexedEligibleFibre SP smallMod BP bigMod J ell cap
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
          (memorySeenBeforeGValues BP bigMod A life i) ∧
      physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho N i Vbig
        (physicalSourceMuTilde BP bigMod q N Vbig) x yg c =
        memoryPrimitiveGSourceCoefficient BP bigMod q rho N i Vbig A life offset ∧
      (∀ g, Green64Fock.fockToList ((yg.2 g).2) =
        Green64MemoryGhostOp.afterGhost (Green64Fock.fockToList ((x.2 g).2))
          (memoryGhostDeathIndices (bigMod g) (A g) (life g) i
            (Green64Fock.fockToList ((x.2 g).2)))
          (memoryGhostFreshAtoms (bigMod g) (A g) (life g) i (e g))) ∧
      (∀ g, Green64Fock.fockMultiset ((yg.2 g).2) =
        (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i :
          Multiset (Green64Fock.Atom (BP g) (bigMod g)))) := by
  have hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p) :=
    fun g p => memory_frozen_nonzero_schedule_support (bigMod g p) (sourceVisitEta q N)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (N+1) (life g p) (hn g p)
  let yg := memoryPrimitiveGOutput SP smallMod BP bigMod J ell cap A life offset i
    x hOld hdomain.cap_saturated e
  let c := memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap A life offset i
    hs x hOld hdomain.cap_saturated e
  refine ⟨yg, c, ?_, ?_, ?_, ?_⟩
  · exact memory_primitive_G_indexed_eligible SP smallMod BP bigMod J ell cap A life offset i
      hdomain.big_injective hs x hOld hdomain.cap_saturated e
  · exact memory_primitive_G_branch_coefficient_exact SP smallMod BP bigMod J ell cap
      A life offset i hs x hOld hdomain.cap_saturated e q rho N Vbig
      (physicalSourceMuTilde BP bigMod q N Vbig)
  · intro g
    exact memory_ghost_output_list_exact (bigMod g) (A g) (life g) offset i
      _ (hOld g) (cap g) (hdomain.cap_saturated g) (e g)
  · intro g
    change (Green64Fock.fockToList ((yg.2 g).2) :
      Multiset (Green64Fock.Atom (BP g) (bigMod g))) = _
    dsimp only [yg, memoryPrimitiveGOutput]
    rw [memory_ghost_output_list_exact]
    exact Multiset.coe_eq_coe.mpr
      (memory_ghost_after_perm_canonical (bigMod g) (A g) (life g) offset i
        (hs g) _ (hOld g) (e g))
end Green64FullPhysicalE

end

end

/-! ## MemoryGhostCanonicalInverse -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

/-- First actual inverse obligation at G: every source OLD deletion/fresh list
with the two canonical pending multisets and no prior birth is determined by
one ordering of the canonical ghost-birth set. No occurrence bijection premise. -/
theorem memory_ghost_canonical_inverse_support
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (D : Finset (Fin old.length)) {b : ℕ}
    (fresh : Fin b → Green64Fock.Atom P modulus)
    (hOut : (Green64MemoryGhostOp.afterGhost old D fresh).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (hNew : ∀ j, match life (fresh j).1 with
      | none => True
      | some jd => ¬ jd.1.val < i) :
    D = memoryGhostDeathIndices modulus A life i old ∧
    (∀ j, memoryScheduleGhostBirth (A (fresh j).1) (life (fresh j).1) i ∧
      (fresh j).2 = 0) ∧
    Function.Bijective (fun j : Fin b =>
      (⟨(fresh j).1, by
        have hm : fresh j ∈ Green64MemoryGhostOp.afterGhost old D fresh :=
          List.mem_append.mpr (Or.inr (List.mem_ofFn.mpr ⟨j, rfl⟩))
        have hh := (memory_pending_mem_iff modulus A life offset i false (fresh j)).mp
          (hOut.mem_iff.mp hm)
        have hb := hNew j
        cases hl : life (fresh j).1 with
        | none => simp [hl, memoryScheduleAfter] at hh
        | some jd =>
          have hbefore : ¬ jd.1.val < i := by simpa [hl] using hb
          have ha : jd.1.val ≤ i ∧ i < jd.2.val ∧ i ∉ A (fresh j).1 := by
            simpa [hl, memoryScheduleAfter] using hh.1
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            simp only [hl, memoryScheduleGhostBirth]
            exact ⟨by omega, ha.2.2⟩⟩
      ⟩ : ↥(memoryGhostBirthSet A life i))) := by
  have hFresh : ∀ j, memoryScheduleGhostBirth (A (fresh j).1) (life (fresh j).1) i ∧
      (fresh j).2 = 0 := by
    intro j
    have hm : fresh j ∈ Green64MemoryGhostOp.afterGhost old D fresh :=
      List.mem_append.mpr (Or.inr (List.mem_ofFn.mpr ⟨j, rfl⟩))
    have hh := (memory_pending_mem_iff modulus A life offset i false (fresh j)).mp
      (hOut.mem_iff.mp hm)
    have hb := hNew j
    have hbirth : memoryScheduleGhostBirth (A (fresh j).1) (life (fresh j).1) i := by
      cases hl : life (fresh j).1 with
      | none => simp [hl, memoryScheduleAfter] at hh
      | some jd =>
        have hbefore : ¬ jd.1.val < i := by simpa [hl] using hb
        have ha : jd.1.val ≤ i ∧ i < jd.2.val ∧ i ∉ A (fresh j).1 := by
          simpa [hl, memoryScheduleAfter] using hh.1
        exact ⟨by omega, ha.2.2⟩
    exact ⟨hbirth, hh.2.trans (memory_schedule_ghost_endpoints_zero (modulus (fresh j).1)
      (fun t => (offset t : ZMod (modulus (fresh j).1))) _ _ (hs _) i (Or.inr hbirth))⟩
  have hNoFreshOld : ∀ j k, (old.get j).1 ≠ (fresh k).1 := by
    intro j k he
    have hb := (memory_ordered_pending_get_spec modulus A life offset i old hOld j).1
    rw [he] at hb
    have hf := (hFresh k).1
    cases hl : life (fresh k).1 with
    | none => simp only [hl, memoryScheduleBefore] at hb
    | some jd =>
      simp only [hl, memoryScheduleBefore] at hb
      simp only [hl, memoryScheduleGhostBirth] at hf
      omega
  have hGet : Function.Injective (fun j : Fin old.length => (old.get j).1) := by
    apply List.nodup_ofFn.mp
    have he : List.ofFn (fun j : Fin old.length => (old.get j).1) =
        old.map (fun z => z.1) := by
      calc
        _ = (List.ofFn old.get).map (fun z => z.1) := List.map_ofFn.symm
        _ = _ := by rw [List.ofFn_get]
    rw [he]
    exact (hOld.map (fun z => z.1)).nodup_iff.mpr
      (memory_pending_primes_nodup modulus A life offset i true)
  have hDeath : D = memoryGhostDeathIndices modulus A life i old := by
    ext j
    simp only [memoryGhostDeathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      by_contra hd
      have hsp := memory_ordered_pending_get_spec modulus A life offset i old hOld j
      have ha := (memory_schedule_G_exact (modulus (old.get j).1)
        (fun t => (offset t : ZMod (modulus (old.get j).1))) _ _ (hs _) i).mpr
          (Or.inl ⟨hsp.1, hd⟩)
      have hm := hOut.mem_iff.mpr
        ((memory_pending_mem_iff modulus A life offset i false (old.get j)).mpr ⟨ha, hsp.2⟩)
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
        have hkj : k = j := hGet (congrArg Sigma.fst he)
        subst k
        have hn : j ∉ D := by simpa using (List.mem_filter.mp hk).2
        exact hn hj
      · obtain ⟨k, hk⟩ := List.mem_ofFn.mp hm
        exact hNoFreshOld j k (congrArg Sigma.fst hk.symm)
    · intro hd
      by_contra hj
      have hm : old.get j ∈ Green64MemoryGhostOp.afterGhost old D fresh := by
        apply List.mem_append.mpr
        exact Or.inl (List.mem_map.mpr ⟨j,
          List.mem_filter.mpr ⟨List.mem_finRange j, decide_eq_true hj⟩, rfl⟩)
      have ha := ((memory_pending_mem_iff modulus A life offset i false (old.get j)).mp
        (hOut.mem_iff.mp hm)).1
      have hb := (memory_ordered_pending_get_spec modulus A life offset i old hOld j).1
      change memoryScheduleBefore (A (old.get j).1) (life (old.get j).1) i at hb
      change memoryScheduleAfter (A (old.get j).1) (life (old.get j).1) i at ha
      cases hl : life (old.get j).1 with
      | none => simp only [hl, memoryScheduleBefore] at hb
      | some jd =>
        simp only [hl, memoryScheduleAfter] at ha
        simp only [hl, memoryScheduleTerminate] at hd
        omega
  refine ⟨hDeath, hFresh, ?_, ?_⟩
  · intro j k he
    have hnod : ((Green64MemoryGhostOp.afterGhost old D fresh).map (fun z => z.1)).Nodup :=
      (hOut.map (fun z => z.1)).nodup_iff.mpr
        (memory_pending_primes_nodup modulus A life offset i false)
    have hf : (List.ofFn (fun j => (fresh j).1)).Nodup := by
      simp only [Green64MemoryGhostOp.afterGhost, List.map_append, List.map_ofFn] at hnod
      exact (List.nodup_append.mp hnod).2.1
    exact (List.nodup_ofFn.mp hf) (congrArg Subtype.val he)
  · intro p
    have hb : memoryScheduleGhostBirth (A p.1) (life p.1) i :=
      (Finset.mem_filter.mp p.2).2
    have ha := (memory_schedule_G_exact (modulus p.1)
      (fun t => (offset t : ZMod (modulus p.1))) _ _ (hs _) i).mpr (Or.inr hb)
    let z : Green64Fock.Atom P modulus := ⟨p.1,
      memoryScheduleResidue (modulus p.1)
        (fun t => (offset t : ZMod (modulus p.1))) (life p.1) i⟩
    have hm : z ∈ Green64MemoryGhostOp.afterGhost old D fresh :=
      hOut.mem_iff.mpr ((memory_pending_mem_iff modulus A life offset i false z).mpr ⟨ha, rfl⟩)
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
      have hkprime : (old.get k).1 = p.1 := congrArg Sigma.fst he
      have hbefore := (memory_ordered_pending_get_spec modulus A life offset i old hOld k).1
      rw [hkprime] at hbefore
      cases hl : life p.1 with
      | none => simp only [hl, memoryScheduleBefore] at hbefore
      | some jd =>
        simp only [hl, memoryScheduleBefore] at hbefore
        simp only [hl, memoryScheduleGhostBirth] at hb
        omega
    · obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
      exact ⟨j, Subtype.ext (congrArg Sigma.fst hj)⟩
end Green64FullPhysicalE

end

end

/-! ## MemoryGhostCanonicalRecovery -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

theorem memory_ghost_lift_order_injective
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (cap : ℕ) (hcap : Fintype.card P ≤ cap) :
    Function.Injective (memoryGhostLiftChoice modulus A life offset i hs old hOld cap hcap) := by
  intro e f he
  have hv := congrArg (fun c : GhostWitnessChoice old
    (fun z : Green64Fock.Atom P modulus => z.2 = 0) cap =>
      List.ofFn c.2.2) he
  have hl : memoryGhostFreshAtoms modulus A life i e =
      memoryGhostFreshAtoms modulus A life i f := List.ofFn_injective hv
  apply Equiv.ext
  intro j
  exact Subtype.ext (congrArg Sigma.fst (congrFun hl j))

/-- Exhaustive, UNIQUE recovery of the real dependent OLD/birth-count/atom
witness. The hypotheses describe its actual pending fibre, not an abstract
history map or a prescribed OLD subset. -/
theorem memory_ghost_canonical_witness_recovery
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (old : List (Green64Fock.Atom P modulus))
    (hOld : old.Perm (memoryCanonicalPendingList modulus A life offset true i))
    (cap : ℕ) (hcap : Fintype.card P ≤ cap)
    (c : GhostWitnessChoice old (fun z : Green64Fock.Atom P modulus => z.2 = 0) cap)
    (hOut : (Green64MemoryGhostOp.afterGhost old c.1.1 c.2.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (hNew : ∀ j, match life (c.2.2 j).1 with
      | none => True
      | some jd => ¬ jd.1.val < i) :
    ∃! e : Fin (memoryGhostBirthSet A life i).card ≃ ↥(memoryGhostBirthSet A life i),
      c = memoryGhostLiftChoice modulus A life offset i hs old hOld cap hcap e := by
  rcases c with ⟨⟨D, hD⟩, ⟨⟨b, hb⟩, fresh⟩⟩
  have hinv := memory_ghost_canonical_inverse_support modulus A life offset i
    hs old hOld D fresh hOut hNew
  let f : Fin b → ↥(memoryGhostBirthSet A life i) := fun j =>
    ⟨(fresh j).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hinv.2.1 j).1⟩⟩
  have hbij : Function.Bijective f := hinv.2.2
  let e0 := Equiv.ofBijective f hbij
  have hcard : b = (memoryGhostBirthSet A life i).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_congr e0
  subst b
  refine ⟨e0, ?_, ?_⟩
  · apply Sigma.ext
    · exact Subtype.ext hinv.1
    · apply heq_of_eq
      apply Sigma.ext
      · exact Fin.ext rfl
      · apply heq_of_eq
        funext j
        apply Sigma.ext
        · rfl
        · exact heq_of_eq (hinv.2.1 j).2
  · intro e he
    apply memory_ghost_lift_order_injective modulus A life offset i hs old hOld cap hcap
    exact he.symm.trans (by
      apply Sigma.ext
      · exact Subtype.ext hinv.1
      · apply heq_of_eq
        apply Sigma.ext
        · exact Fin.ext rfl
        · apply heq_of_eq
          funext j
          apply Sigma.ext
          · rfl
          · exact heq_of_eq (hinv.2.1 j).2)
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveEChoices -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ)
variable (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

def memoryEStoreSlots (x : BigState modulus M B) (sigma : Equiv.Perm (Fin M)) : Finset (Fin M) :=
  Finset.univ.filter (fun j => memoryScheduleStore (A (x.1 (sigma j))) (life (x.1 (sigma j))) i)

def memoryEPromoteSlots (target : Fin M → P) (tau : Equiv.Perm (Fin M)) : Finset (Fin M) :=
  Finset.univ.filter (fun j => memorySchedulePromote (A (target (tau j))) (life (target (tau j))) i)

/-- The OLD atom exists for each scheduled promotion, with its complete source residue.
The codomain is the incoming Fock sector; freshly stored atoms cannot enter it. -/
theorem memory_E_promotion_old_atom_exists
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (x : BigState modulus M B)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (target : Fin M → P) (tau : Equiv.Perm (Fin M))
    (j : ↥(memoryEPromoteSlots M A life i target tau)) :
    ∃ k : Fin x.2.1.val, x.2.2 k =
      (⟨target (tau j.1), memoryScheduleResidue (modulus (target (tau j.1)))
        (fun t => (offset t : ZMod (modulus (target (tau j.1)))))
        (life (target (tau j.1))) i⟩ : Green64Fock.Atom P modulus) := by
  have hp := (Finset.mem_filter.mp j.2).2
  have ha := (memory_schedule_promotion_is_old (modulus (target (tau j.1)))
    (fun t => (offset t : ZMod (modulus (target (tau j.1)))))
    (A (target (tau j.1))) (life (target (tau j.1))) (hs _) i hp).1
  let z : Green64Fock.Atom P modulus :=
    ⟨target (tau j.1), memoryScheduleResidue (modulus (target (tau j.1)))
      (fun t => (offset t : ZMod (modulus (target (tau j.1)))))
      (life (target (tau j.1))) i⟩
  have hz : z ∈ Green64Fock.fockToList x.2 := hOld.mem_iff.mpr
    ((memory_pending_mem_iff modulus A life offset i false z).mpr ⟨ha, rfl⟩)
  exact List.mem_ofFn.mp hz

def memoryEPromotionIndex
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (x : BigState modulus M B)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (target : Fin M → P) (tau : Equiv.Perm (Fin M))
    (j : ↥(memoryEPromoteSlots M A life i target tau)) : Fin x.2.1.val :=
  Classical.choose (memory_E_promotion_old_atom_exists modulus M B A life offset i hs x hOld target tau j)

theorem memory_E_promotion_index_atom_exact
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (x : BigState modulus M B)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (target : Fin M → P) (tau : Equiv.Perm (Fin M))
    (j : ↥(memoryEPromoteSlots M A life i target tau)) :
    x.2.2 (memoryEPromotionIndex modulus M B A life offset i hs x hOld target tau j) =
      (⟨target (tau j.1), memoryScheduleResidue (modulus (target (tau j.1)))
        (fun t => (offset t : ZMod (modulus (target (tau j.1)))))
        (life (target (tau j.1))) i⟩ : Green64Fock.Atom P modulus) :=
  Classical.choose_spec (memory_E_promotion_old_atom_exists modulus M B A life offset i hs x hOld target tau j)

/-- Distinct target active slots produce a genuine injection into OLD indices. -/
def memoryEPromotionEmbedding
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (x : BigState modulus M B)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (target : Fin M → P) (htarget : Function.Injective target)
    (tau : Equiv.Perm (Fin M)) :
    ↥(memoryEPromoteSlots M A life i target tau) ↪ Fin x.2.1.val where
  toFun := memoryEPromotionIndex modulus M B A life offset i hs x hOld target tau
  inj' := by
    intro a b he
    have ha := congrArg Sigma.fst
      (memory_E_promotion_index_atom_exact modulus M B A life offset i hs x hOld target tau a)
    have hb := congrArg Sigma.fst
      (memory_E_promotion_index_atom_exact modulus M B A life offset i hs x hOld target tau b)
    rw [he] at ha
    exact Subtype.ext (tau.injective (htarget (ha.symm.trans hb)))

/-- Concrete literal E OLD-store/promotion choice. No newly stored OLD index
and no unproved occurrence bijection is used. -/
def memoryPrimitiveEChoice
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (x : BigState modulus M B)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (target : Fin M → P) (htarget : Function.Injective target)
    (sigma tau : Equiv.Perm (Fin M)) : BigEdgeChoice modulus M B x :=
  (memoryEStoreSlots modulus M B A life i x sigma,
    ⟨memoryEPromoteSlots M A life i target tau,
      memoryEPromotionEmbedding modulus M B A life offset i hs x hOld target htarget tau⟩)

theorem memory_E_promoted_matches
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (x : BigState modulus M B)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (target : Fin M → P) (htarget : Function.Injective target)
    (sigma tau : Equiv.Perm (Fin M))
    (j : ↥(memoryEPromoteSlots M A life i target tau)) :
    target (tau j.1) = (x.2.2 ((memoryPrimitiveEChoice modulus M B A life offset i
      hs x hOld target htarget sigma tau).2.2 j)).1 := by
  exact (congrArg Sigma.fst
    (memory_E_promotion_index_atom_exact modulus M B A life offset i hs x hOld target tau j)).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveELegal -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ) (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

theorem memory_E_old_atom_spec
    (x : BigState modulus M B)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (j : Fin x.2.1.val) :
    memoryScheduleAfter (A (x.2.2 j).1) (life (x.2.2 j).1) i ∧
      (x.2.2 j).2 = memoryScheduleResidue (modulus (x.2.2 j).1)
        (fun t => (offset t : ZMod (modulus (x.2.2 j).1))) (life (x.2.2 j).1) i := by
  exact (memory_pending_mem_iff modulus A life offset i false _).mp
    (hOld.mem_iff.mp (List.mem_ofFn.mpr ⟨j, rfl⟩))

theorem memory_E_old_prime_injective
    (x : BigState modulus M B)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i)) :
    Function.Injective (fun j : Fin x.2.1.val => (x.2.2 j).1) := by
  have hh := (hOld.map (fun z => z.1)).nodup_iff.mpr
    (memory_pending_primes_nodup modulus A life offset i false)
  apply List.nodup_ofFn.mp
  simpa only [Green64Fock.fockToList, List.map_ofFn, Function.comp_def] using hh

/-- True source survivor+store output has no repeated prime; cutoff is
derived from source saturation, not imposed as a new choice hypothesis. -/
theorem memory_E_pending_output_prime_nodup
    (x : BigState modulus M B) (hx : Function.Injective x.1)
    (hA : ∀ j, i ∈ A (x.1 j))
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (sigma : Equiv.Perm (Fin M)) (step : ℤ) (c : BigEdgeChoice modulus M B x) :
    ((physicalPendingOutput modulus M B x sigma step c).map (fun z => z.1)).Nodup := by
  unfold physicalPendingOutput survivors newlyStored
  simp only [List.map_append, List.map_map, Function.comp_def,
    Green64PhysicalEdge.translateAtom]
  apply List.nodup_append.mpr
  refine ⟨List.Nodup.map (memory_E_old_prime_injective modulus M B A life offset i x hOld)
      (Finset.nodup_toList _), List.Nodup.map (hx.comp sigma.injective)
        (Finset.nodup_toList _), ?_⟩
  intro p hp q hq he
  obtain ⟨j, hj, hjp⟩ := List.mem_map.mp hp
  obtain ⟨k, hk, hkq⟩ := List.mem_map.mp hq
  have ha := (memory_E_old_atom_spec modulus M B A life offset i x hOld j).1
  have hh : (x.2.2 j).1 = x.1 (sigma k) := hjp.trans (he.trans hkq.symm)
  rw [hh] at ha
  cases hl : life (x.1 (sigma k)) with
  | none => simp [hl, memoryScheduleAfter] at ha
  | some jd =>
      simp only [memoryScheduleAfter, hl] at ha
      exact ha.2.2 (hA (sigma k))

theorem memory_E_output_within_saturated_cutoff
    (x : BigState modulus M B) (hx : Function.Injective x.1)
    (hA : ∀ j, i ∈ A (x.1 j))
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (hcap : Fintype.card P ≤ B)
    (sigma : Equiv.Perm (Fin M)) (step : ℤ) (c : BigEdgeChoice modulus M B x) :
    (physicalPendingOutput modulus M B x sigma step c).length ≤ B := by
  have hh := (memory_E_pending_output_prime_nodup modulus M B A life offset i
    x hx hA hOld sigma step c).length_le_card
  exact (by simpa only [List.length_map] using hh : _ ≤ Fintype.card P).trans hcap

/-- All literal OrientedBigEdgeLegal fields for the concrete scheduled choice.
The two unshared divisor bans are exact source obligations, separately derived
in MemorySourcePrimeExclusions; they are not replaced by abstract legality. -/
theorem memory_E_choice_oriented_legal
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (x : BigState modulus M B) (hx : Function.Injective x.1)
    (hA0 : ∀ j, i ∈ A (x.1 j))
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (target : Fin M → P) (htarget : Function.Injective target)
    (hA1 : ∀ j, i+1 ∈ A (target j))
    (sigma tau : Equiv.Perm (Fin M)) (shared : Finset (Fin M))
    (hcopy : ∀ j ∈ shared, x.1 (sigma j) = target (tau j))
    (D : ℕ) (step : ℤ) (hstep : step = offset (i+1) - offset i)
    (hsourceban : ∀ j ∉ shared, ¬ modulus (x.1 (sigma j)) ∣ D)
    (htargetban : ∀ j ∉ shared, ¬ modulus (target (tau j)) ∣ D)
    (hcap : Fintype.card P ≤ B) :
    OrientedBigEdgeLegal modulus M B x target shared sigma tau D step
      (memoryPrimitiveEChoice modulus M B A life offset i hs x hOld target htarget sigma tau) := by
  let c := memoryPrimitiveEChoice modulus M B A life offset i
    hs x hOld target htarget sigma tau
  have hstore : c.1 ⊆ orientedUnshared M shared := by
    intro j hj
    have ht := (Finset.mem_filter.mp hj).2
    have hn : j ∉ shared := by
      intro hjsh
      have ha := hA1 (tau j)
      rw [← hcopy j hjsh] at ha
      cases hl : life (x.1 (sigma j)) with
      | none => simp [hl, memoryScheduleStore] at ht
      | some jd =>
        simp only [memoryScheduleStore, hl] at ht
        exact ht.2.1 ha
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩
  have hpromote : c.2.1 ⊆ orientedUnshared M shared := by
    intro j hj
    have ht := (Finset.mem_filter.mp hj).2
    have hn : j ∉ shared := by
      intro hjsh
      have ha := hA0 (sigma j)
      rw [hcopy j hjsh] at ha
      cases hl : life (target (tau j)) with
      | none => simp [hl, memorySchedulePromote] at ht
      | some jd =>
        simp only [memorySchedulePromote, hl] at ht
        exact ht.1 ha
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩
  refine ⟨hcopy, hstore, hpromote, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact memory_E_promoted_matches modulus M B A life offset i hs x hOld target htarget sigma tau j
  · intro j
    have he := memory_E_promotion_index_atom_exact modulus M B A life offset i hs x hOld target tau j
    change (x.2.2 (memoryEPromotionIndex modulus M B A life offset i hs x hOld target tau j)).2 +
      (step : ZMod (modulus (x.2.2 (memoryEPromotionIndex modulus M B A life offset i hs x hOld target tau j)).1)) = 0
    rw [he]
    have hp := (Finset.mem_filter.mp j.2).2
    have hz := memory_schedule_active_anchor (modulus (target (tau j.1)))
      (fun t => (offset t : ZMod (modulus (target (tau j.1)))))
      (A (target (tau j.1))) (life (target (tau j.1))) (hs _) (i+1) (hA1 _)
    cases hl : life (target (tau j.1)) with
    | none => simp [hl, memorySchedulePromote] at hp
    | some jd =>
      dsimp only
      rw [hstep, Int.cast_sub]
      rw [memory_schedule_residue_translate (modulus (target (tau j.1)))
        (fun t => (offset t : ZMod (modulus (target (tau j.1)))))
        (A (target (tau j.1))) jd i]
      simpa only [hl] using hz
  · intro j
    have hm := memory_E_promoted_matches modulus M B A life offset i hs x hOld target htarget sigma tau j
    rw [← hm]
    exact htargetban j.1 (Finset.mem_sdiff.mp (hpromote j.2)).2
  · intro j hj
    exact hsourceban j (Finset.mem_sdiff.mp (hstore hj)).2
  · exact memory_E_output_within_saturated_cutoff modulus M B A life offset i x hx hA0 hOld
      hcap sigma step c
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveEOutput -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M B : ℕ) (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

theorem memory_E_selected_old_iff
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (x : BigState modulus M B)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (target : Fin M → P) (htarget : Function.Injective target)
    (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p)
    (sigma tau : Equiv.Perm (Fin M)) (k : Fin x.2.1.val) :
    k ∈ selectedOld modulus M B x
      (memoryPrimitiveEChoice modulus M B A life offset i hs x hOld target htarget sigma tau) ↔
      memorySchedulePromote (A (x.2.2 k).1) (life (x.2.2 k).1) i := by
  constructor
  · intro hk
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hk
    have hm := memory_E_promoted_matches modulus M B A life offset i hs x hOld target htarget sigma tau j
    rw [he] at hm
    have hp := (Finset.mem_filter.mp j.2).2
    rw [hm] at hp
    exact hp
  · intro hp
    have hactive : i+1 ∈ A (x.2.2 k).1 := by
      cases hl : life (x.2.2 k).1 with
      | none => simp [hl, memorySchedulePromote] at hp
      | some jd =>
        simp only [hl, memorySchedulePromote] at hp
        exact hp.2.1
    obtain ⟨j, hj⟩ := (hA1 _).mp hactive
    let jj : ↥(memoryEPromoteSlots M A life i target tau) :=
      ⟨tau.symm j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [tau.apply_symm_apply, hj] using hp⟩⟩
    refine Finset.mem_image.mpr ⟨jj, Finset.mem_univ _, ?_⟩
    apply memory_E_old_prime_injective modulus M B A life offset i x hOld
    exact (memory_E_promoted_matches modulus M B A life offset i hs x hOld target htarget sigma tau jj).symm.trans
      (by simpa [jj] using hj)

theorem memory_E_output_perm_canonical
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (x : BigState modulus M B) (hx : Function.Injective x.1)
    (hA0 : ∀ p, i ∈ A p ↔ ∃ j, x.1 j = p)
    (hOld : (Green64Fock.fockToList x.2).Perm
      (memoryCanonicalPendingList modulus A life offset false i))
    (target : Fin M → P) (htarget : Function.Injective target)
    (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p)
    (sigma tau : Equiv.Perm (Fin M)) (step : ℤ)
    (hstep : step = offset (i+1) - offset i) :
    (physicalPendingOutput modulus M B x sigma step
      (memoryPrimitiveEChoice modulus M B A life offset i hs x hOld target htarget sigma tau)).Perm
      (memoryCanonicalPendingList modulus A life offset true (i+1)) := by
  let c := memoryPrimitiveEChoice modulus M B A life offset i hs x hOld target htarget sigma tau
  have hactive : ∀ j, i ∈ A (x.1 j) := fun j => (hA0 _).mpr ⟨j, rfl⟩
  apply (List.perm_ext_iff_of_nodup
    ((memory_E_pending_output_prime_nodup modulus M B A life offset i x hx hactive hOld sigma step c).of_map
      (fun z => z.1))
    ((memory_pending_primes_nodup modulus A life offset (i+1) true).of_map
      (fun z => z.1))).mpr
  intro z
  rw [memory_pending_mem_iff modulus A life offset (i+1) true]
  simp only [↓reduceIte]
  have hG := memory_schedule_E_exact (modulus z.1)
    (fun t => (offset t : ZMod (modulus z.1))) (A z.1) (life z.1) (hs _) i
  rw [hG]
  unfold physicalPendingOutput survivors newlyStored
  rw [List.mem_append]
  constructor
  · rintro (hz | hz)
    · obtain ⟨k, hk, he⟩ := List.mem_map.mp hz
      have hsurv := Finset.mem_sdiff.mp (Finset.mem_toList.mp hk)
      have hnot : ¬ memorySchedulePromote (A (x.2.2 k).1) (life (x.2.2 k).1) i :=
        fun hp => hsurv.2 ((memory_E_selected_old_iff modulus M B A life offset i hs x hOld
          target htarget hA1 sigma tau k).mpr hp)
      have hold := memory_E_old_atom_spec modulus M B A life offset i x hOld k
      have hpr : (x.2.2 k).1 = z.1 := by
        simpa only [Green64PhysicalEdge.translateAtom] using
          congrArg (fun zz : Green64Fock.Atom P modulus => zz.1) he
      have hres : z.2 = memoryScheduleResidue (modulus z.1)
          (fun t => (offset t : ZMod (modulus z.1))) (life z.1) (i+1) := by
        rw [← he]
        dsimp only [Green64PhysicalEdge.translateAtom]
        rw [hold.2, hstep, Int.cast_sub]
        cases hl : life (x.2.2 k).1 with
        | none => simp [hl, memoryScheduleAfter] at hold
        | some jd =>
          exact memory_schedule_residue_translate (modulus (x.2.2 k).1)
            (fun t => (offset t : ZMod (modulus (x.2.2 k).1)))
            (A (x.2.2 k).1) jd i
      have hafter := hold.1
      rw [hpr] at hafter hnot
      exact ⟨⟨Or.inl hafter, hnot⟩, hres⟩
    · obtain ⟨j, hj, he⟩ := List.mem_map.mp hz
      have hstore := (Finset.mem_filter.mp (Finset.mem_toList.mp hj)).2
      have hpr : x.1 (sigma j) = z.1 := congrArg Sigma.fst he
      have hnot : ¬ memorySchedulePromote (A z.1) (life z.1) i := by
        rw [hpr] at hstore
        intro hp
        cases hl : life z.1 with
        | none => simp [hl, memoryScheduleStore] at hstore
        | some jd =>
          simp only [hl, memoryScheduleStore] at hstore
          simp only [hl, memorySchedulePromote] at hp
          exact hp.1 hstore.1
      have hres : z.2 = memoryScheduleResidue (modulus z.1)
          (fun t => (offset t : ZMod (modulus z.1))) (life z.1) (i+1) := by
        rw [← he]
        dsimp only
        rw [hstep, Int.cast_sub]
        cases hl : life (x.1 (sigma j)) with
        | none => simp [hl, memoryScheduleStore] at hstore
        | some jd =>
          exact memory_schedule_store_resets_same_anchor (modulus (x.1 (sigma j)))
            (fun t => (offset t : ZMod (modulus (x.1 (sigma j)))))
            (A (x.1 (sigma j))) jd (by simpa only [hl] using hs (x.1 (sigma j))) i (by simpa only [hl] using hstore)
      rw [hpr] at hstore
      exact ⟨⟨Or.inr hstore, hnot⟩, hres⟩
  · rintro ⟨⟨ha | ht, hn⟩, hr⟩
    · let zz : Green64Fock.Atom P modulus := ⟨z.1,
        memoryScheduleResidue (modulus z.1)
          (fun t => (offset t : ZMod (modulus z.1))) (life z.1) i⟩
      have hzold : zz ∈ Green64Fock.fockToList x.2 := hOld.mem_iff.mpr
        ((memory_pending_mem_iff modulus A life offset i false zz).mpr ⟨ha, rfl⟩)
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hzold
      apply Or.inl
      refine List.mem_map.mpr ⟨k, Finset.mem_toList.mpr (Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, ?_⟩), ?_⟩
      · rw [memory_E_selected_old_iff modulus M B A life offset i hs x hOld target htarget hA1 sigma tau]
        simpa only [hk] using hn
      · rw [hk]
        unfold zz
        have htres : memoryScheduleResidue (modulus z.1)
            (fun t => (offset t : ZMod (modulus z.1))) (life z.1) i +
            (step : ZMod (modulus z.1)) =
            memoryScheduleResidue (modulus z.1)
              (fun t => (offset t : ZMod (modulus z.1))) (life z.1) (i+1) := by
          rw [hstep, Int.cast_sub]
          cases hl : life z.1 with
          | none => simp [hl, memoryScheduleAfter] at ha
          | some jd =>
            exact memory_schedule_residue_translate (modulus z.1)
              (fun t => (offset t : ZMod (modulus z.1))) (A z.1) jd i
        dsimp only [Green64PhysicalEdge.translateAtom]
        exact Sigma.ext rfl (heq_of_eq (htres.trans hr.symm))
    · have haz : i ∈ A z.1 := by
        cases hl : life z.1 with
        | none => simp [hl, memoryScheduleStore] at ht
        | some jd =>
          simp only [hl, memoryScheduleStore] at ht
          exact ht.1
      obtain ⟨j, hj⟩ := (hA0 _).mp haz
      apply Or.inr
      refine List.mem_map.mpr ⟨sigma.symm j, Finset.mem_toList.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩), ?_⟩
      · simpa only [sigma.apply_symm_apply, hj] using ht
      · try simp only [sigma.apply_symm_apply, hj]
        have hres : (step : ZMod (modulus z.1)) =
            memoryScheduleResidue (modulus z.1)
              (fun t => (offset t : ZMod (modulus z.1))) (life z.1) (i+1) := by
          rw [hstep, Int.cast_sub]
          cases hl : life z.1 with
          | none => simp [hl, memoryScheduleStore] at ht
          | some jd =>
            exact memory_schedule_store_resets_same_anchor (modulus z.1)
              (fun t => (offset t : ZMod (modulus z.1))) (A z.1) jd
              (by simpa only [hl] using hs z.1) i (by simpa only [hl] using ht)
        have hlabel : x.1 (sigma (sigma.symm j)) = z.1 :=
          (congrArg x.1 (sigma.apply_symm_apply j)).trans hj
        have hatom := congrArg (fun p : P =>
          (⟨p, (step : ZMod (modulus p))⟩ : Green64Fock.Atom P modulus)) hlabel
        exact hatom.trans (Sigma.ext rfl (heq_of_eq (hres.trans hr.symm)))
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveESourceLift -/

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
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

/-- Full E constructor retaining the original Nu, auxiliaries, independent
BIG/SMALL sigma/tau, target SMALL Haar state and active target arrays. -/
def memoryPrimitiveESourceChoice
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG := BG) (J+ell))
    (ss st : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)) :
    FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns x :=
  ⟨nu, aux,
    ⟨⟨bs, bt, fun g => ⟨Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g),
        memoryPrimitiveEChoice (bigMod g) (J+ell) (cap g) (A g) (life g) offset i
          (hs g) (x.2 g) (hOld g) _
          (Green64SmallHaar.marks_injective (bigMod g) (J+ell) (iy.2 g))
          (bs g) (bt g)⟩, iy.1⟩, ss, st⟩⟩

/-- Actual full source-oriented E legality. The p-not-D exclusions and SMALL
translation are discharged using the ORIGINAL compatible independent row,
rather than passed as a physical-legal axiom. -/
theorem memory_source_primitive_E_legal
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (k : ℤ) (R : ℕ)
    (hdomain : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ix iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hsmall : x.1 = ix.1)
    (hactive : ∀ g, (x.2 g).1 = Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g))
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) j = p)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG := BG) (J+ell))
    (ss st : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (o : ℤ) (ho : o = 1 ∨ o = -1)
    (hban : memoryIndependentAuxBan SP smallMod BP bigMod J ell m (patterns nu) aux ix iy)
    (hsmallleg : Green64SmallHaar.groupEdgeAllowedPerm SP smallMod (J+ell)
      (sourceSmallShared J ell)
      (o*k*(memoryIndependentD SP smallMod BP bigMod J ell m (patterns nu) aux ix bs ss : ℤ))
      ss st ix.1 iy.1)
    (hbigleg : Green64SmallHaar.groupEdgeAllowedPerm BP bigMod (J+ell)
      (sourceBigShared J ell m (patterns nu))
      (o*k*(memoryIndependentD SP smallMod BP bigMod J ell m (patterns nu) aux ix bs ss : ℤ))
      bs bt ix.2 iy.2)
    (hoff : offset (i+1) - offset i =
      o*k*(memoryIndependentD SP smallMod BP bigMod J ell m (patterns nu) aux ix bs ss : ℤ)) :
    sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns x o k
      (memoryPrimitiveESourceChoice SP smallMod BP bigMod J ell m cap patterns
        A life offset i hs x hOld iy nu aux bs bt ss st) := by
  have hD : sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
      (patterns nu) aux x bs ss =
      memoryIndependentD SP smallMod BP bigMod J ell m (patterns nu) aux ix bs ss := by
    simp only [sourceOrientedPhysicalD, memoryIndependentD, hsmall, hactive]
  unfold sourceOrientedPhysicalLegal
  dsimp only [memoryPrimitiveESourceChoice]
  rw [hD]
  refine ⟨ho, hdomain.k_ne, ?_, ?_, ?_⟩
  · simpa only [sourceAuxAvoidsEndpoints, memoryIndependentAuxBan, hactive] using hban
  · intro g
    apply memory_E_choice_oriented_legal (bigMod g) (J+ell) (cap g) (A g) (life g) offset i
      (hs g) (x.2 g) (by rw [hactive g]; exact Green64SmallHaar.marks_injective _ _ _)
      (fun j => (hA0 g _).mpr ⟨j, by rw [← hactive g]⟩) (hOld g)
      (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
      (Green64SmallHaar.marks_injective _ _ _)
      (fun j => (hA1 g _).mpr ⟨j, rfl⟩) (bs g) (bt g)
      (sourceBigShared J ell m (patterns nu) g)
    · intro j hj
      rw [hactive g]
      exact (hbigleg g).2 j hj
    · simpa only [sourceOrientedStep, hD] using hoff.symm
    · intro j hj
      rw [hactive g]
      exact memory_source_unshared_exit_not_dividing SP smallMod BP bigMod J ell m
        hdomain.small_prime hdomain.big_prime hdomain.big_injective hdomain.disjoint
        (patterns nu) aux ix iy hban bs ss g j hj
    · intro j hj
      exact memory_source_unshared_entry_not_dividing SP smallMod BP bigMod J ell m
        hdomain.small_prime hdomain.big_prime hdomain.big_injective hdomain.disjoint
        (patterns nu) aux ix iy hban bs bt ss (fun g j hj => (hbigleg g).2 j hj) g j hj
    · exact hdomain.cap_saturated g
  · simpa only [hsmall, sourceOrientedStep, hD] using hsmallleg
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveEFresh -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
variable {P : Type} [Fintype P] [DecidableEq P]
variable (M : ℕ) (A : P → Finset ℕ) {n : ℕ}
variable (life : P → MemoryLifespanChoice n) (i : ℕ)

/-- Genuine fresh target slot means a first birth at i+1. Adjacent active
uses are already known to be shared in the original independent row. -/
theorem memory_E_fresh_slot_birth_exact
    (modulus : P → ℕ) (offset : ℕ → ℤ)
    (hs : ∀ p, MemoryFrozenScheduleSupport (modulus p)
      (fun t => (offset t : ZMod (modulus p))) (A p) (life p))
    (source target : Fin M → P) (sigma tau : Equiv.Perm (Fin M))
    (hA0 : ∀ p, i ∈ A p ↔ ∃ j, source j = p)
    (hA1 : ∀ p, i+1 ∈ A p ↔ ∃ j, target j = p)
    (shared : Finset (Fin M))
    (hcont : ∀ j k, source (sigma j) = target (tau k) → j ∈ shared ∧ k = j)
    (j : Fin M)
    (hj : j ∈ orientedFresh M shared (memoryEPromoteSlots M A life i target tau)) :
    memoryScheduleFresh (A (target (tau j))) (life (target (tau j))) i := by
  have hunshared := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hj).1).2
  have hnPromote := (Finset.mem_sdiff.mp hj).2
  have hnot : i ∉ A (target (tau j)) := by
    intro hp
    obtain ⟨k, hk⟩ := (hA0 _).mp hp
    have hmatch : source (sigma (sigma.symm k)) = target (tau j) := by
      simpa only [sigma.apply_symm_apply] using hk
    have hh := hcont _ _ hmatch
    exact hunshared (hh.2 ▸ hh.1)
  have hactive := (hA1 _).mpr ⟨tau j, rfl⟩
  have hentry := (memory_schedule_entry_exact (modulus (target (tau j)))
    (fun t => (offset t : ZMod (modulus (target (tau j)))))
    (A (target (tau j))) (life (target (tau j))) (hs _) i hnot hactive).1
  rcases hentry with hp | hf
  · exact False.elim (hnPromote (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩))
  · exact hf
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveEFullOutput -/

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
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

theorem memory_source_primitive_E_output_exact
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hx : ∀ g, Function.Injective (x.2 g).1)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, (x.2 g).1 j = p)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG := BG) (J+ell))
    (ss st : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (o k : ℤ)
    (hoff : sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns nu) aux x bs ss o k = offset (i+1) - offset i) :
    sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns x o k
      (memoryPrimitiveESourceChoice SP smallMod BP bigMod J ell m cap patterns
        A life offset i hs x hOld iy nu aux bs bt ss st) =
      (iy.1, fun g => (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g),
        (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true (i+1) :
          Multiset (Green64Fock.Atom (BP g) (bigMod g))))) := by
  unfold sourceOrientedPhysicalOutput fullPhysicalBranchOutput bigGroupBranchOutput
    physicalBranchOutput physicalPendingMultiset
  dsimp only [memoryPrimitiveESourceChoice]
  congr 1
  funext g
  congr 1
  exact Multiset.coe_eq_coe.mpr
    (memory_E_output_perm_canonical (bigMod g) (J+ell) (cap g) (A g) (life g) offset i
      (hs g) (x.2 g) (hx g) (hA0 g) (hOld g) _
      (Green64SmallHaar.marks_injective _ _ _) (hA1 g) (bs g) (bt g) _ hoff)

theorem memory_source_primitive_E_birth_eligible
    (hinj : Function.Injective (fun gp : Sigma BP => bigMod gp.1 gp.2))
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, (x.2 g).1 j = p)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG := BG) (J+ell))
    (ss st : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (hcont : ∀ g j k, (x.2 g).1 (bs g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g k) →
      j ∈ sourceBigShared J ell m (patterns nu) g ∧ k = j) :
    orientedEFreshBatchEligible SP smallMod BP bigMod J ell m cap patterns
      (memoryBornBeforeValues BP bigMod life (i+1))
      (memoryPrimitiveESourceChoice SP smallMod BP bigMod J ell m cap patterns
        A life offset i hs x hOld iy nu aux bs bt ss st) := by
  let fresh g := orientedFresh (J+ell) (sourceBigShared J ell m (patterns nu) g)
    (memoryEPromoteSlots (J+ell) (A g) (life g) i
      (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)) (bt g))
  let val g j := bigMod g (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g j))
  have hvalinj (g : BG) : Function.Injective (val g) := by
    intro j k he
    have hh : (⟨g, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g j)⟩ : Sigma BP) =
      ⟨g, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g k)⟩ := hinj he
    exact (bt g).injective (Green64SmallHaar.marks_injective _ _ _
      (eq_of_heq (Sigma.mk.inj_iff.mp hh).2))
  have hbirth (g : BG) (j : Fin (J+ell)) (hj : j ∈ fresh g) :
      memoryScheduleFresh
        (A g (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g j)))
        (life g (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g j))) i :=
    memory_E_fresh_slot_birth_exact (J+ell) (A g) (life g) i (bigMod g) offset
      (hs g) (x.2 g).1 _ (bs g) (bt g) (hA0 g) (hA1 g)
      _ (hcont g) j hj
  unfold orientedEFreshBatchEligible orientedEFreshBirths
  dsimp only [memoryPrimitiveESourceChoice, memoryPrimitiveEChoice]
  change ((Finset.univ : Finset BG).toList.flatMap
    (fun g => (fresh g).toList.map (val g))).Nodup ∧
    Disjoint (memoryBornBeforeValues BP bigMod life (i+1))
      ((Finset.univ : Finset BG).toList.flatMap
        (fun g => (fresh g).toList.map (val g))).toFinset
  constructor
  · apply List.nodup_flatMap.mpr
    refine ⟨fun g hg => List.Nodup.map (hvalinj g) (Finset.nodup_toList _), ?_⟩
    apply (Finset.univ : Finset BG).nodup_toList.imp
    intro g h hne v hv hw
    obtain ⟨j, hj, hjv⟩ := List.mem_map.mp hv
    obtain ⟨k, hk, hkv⟩ := List.mem_map.mp hw
    have hh : (⟨g, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g j)⟩ : Sigma BP) =
      ⟨h, Green64SmallHaar.marks (bigMod h) (J+ell) (iy.2 h) (bt h k)⟩ :=
      hinj (hjv.trans hkv.symm)
    exact hne (congrArg Sigma.fst hh)
  · apply Finset.disjoint_left.mpr
    intro v hv hf
    obtain ⟨gp, hgp, hgv⟩ := Finset.mem_image.mp hv
    have hbefore := (Finset.mem_filter.mp hgp).2
    obtain ⟨g, hg, hvg⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hf)
    obtain ⟨j, hj, hjv⟩ := List.mem_map.mp hvg
    have hh : gp = (⟨g, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g j)⟩ : Sigma BP) :=
      hinj (hgv.trans hjv.symm)
    rw [hh] at hbefore
    have hb := hbirth g j (Finset.mem_toList.mp hj)
    cases hl : life g (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g j)) with
    | none => simp [hl, memoryScheduleFresh] at hb
    | some jd =>
      simp only [hl] at hbefore
      simp only [hl, memoryScheduleFresh] at hb
      omega
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveEIndexedLift -/

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
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n) (offset : ℕ → ℤ) (i : ℕ)

theorem memory_source_primitive_E_indexed_eligible
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (k : ℤ) (R : ℕ)
    (hdomain : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ix iy : MemoryIndependentState SP smallMod BP bigMod J ell)
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hsmall : x.1 = ix.1)
    (hactive : ∀ g, (x.2 g).1 = Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g))
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (hA0 : ∀ g p, i ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) j = p)
    (hA1 : ∀ g p, i+1 ∈ A g p ↔ ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p)
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (bs bt : BigGroupPerm (BG := BG) (J+ell))
    (ss st : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (o : ℤ) (ho : o = 1 ∨ o = -1)
    (hban : memoryIndependentAuxBan SP smallMod BP bigMod J ell m (patterns nu) aux ix iy)
    (hsmallleg : Green64SmallHaar.groupEdgeAllowedPerm SP smallMod (J+ell)
      (sourceSmallShared J ell)
      (o*k*(memoryIndependentD SP smallMod BP bigMod J ell m (patterns nu) aux ix bs ss : ℤ))
      ss st ix.1 iy.1)
    (hbigleg : Green64SmallHaar.groupEdgeAllowedPerm BP bigMod (J+ell)
      (sourceBigShared J ell m (patterns nu))
      (o*k*(memoryIndependentD SP smallMod BP bigMod J ell m (patterns nu) aux ix bs ss : ℤ))
      bs bt ix.2 iy.2)
    (hoff : offset (i+1) - offset i =
      o*k*(memoryIndependentD SP smallMod BP bigMod J ell m (patterns nu) aux ix bs ss : ℤ)) :
    (⟨x, memoryPrimitiveESourceChoice SP smallMod BP bigMod J ell m cap patterns
      A life offset i hs x hOld iy nu aux bs bt ss st⟩ :
      Σ xx : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns xx) ∈
      physicalOrientedEIndexedLegalFibre SP smallMod BP bigMod J ell m cap patterns o k
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
        (memoryBornBeforeValues BP bigMod life (i+1)) := by
  have hA0x : ∀ g p, i ∈ A g p ↔ ∃ j, (x.2 g).1 j = p := by
    intro g p
    simpa only [hactive g] using hA0 g p
  have hcont : ∀ g j l, (x.2 g).1 (bs g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (bt g l) →
      j ∈ sourceBigShared J ell m (patterns nu) g ∧ l = j := by
    intro g j l he
    rw [hactive g] at he
    exact memory_source_active_continuation_is_shared SP smallMod BP bigMod J ell m
      hdomain.small_prime hdomain.big_prime hdomain.big_injective hdomain.disjoint
      (patterns nu) aux ix iy hban bs bt ss o k ho hdomain.k_ne hdomain.big_above_k
      hbigleg g j l he
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, rfl, ?_, ?_⟩
  · exact memory_source_primitive_E_legal SP smallMod BP bigMod J ell m cap patterns
      A life offset i hs q rho Vsmall Vbig k R hdomain ix iy x hsmall hactive hOld
      hA0 hA1 nu aux bs bt ss st o ho hban hsmallleg hbigleg hoff
  · exact memory_source_primitive_E_birth_eligible SP smallMod BP bigMod J ell m cap patterns
      A life offset i hdomain.big_injective hs x hOld iy hA0x hA1 nu aux bs bt ss st hcont
end Green64FullPhysicalE

end

end

/-! ## MemoryPrimitiveGInverse -/

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
variable (J ell : ℕ) (cap : BG → ℕ)
variable (A : (g : BG) → BP g → Finset ℕ) {n : ℕ}
variable (life : (g : BG) → BP g → MemoryLifespanChoice n)
variable (offset : ℕ → ℤ) (i : ℕ)

theorem memory_primitive_G_eligible_no_prior_birth
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (hb : physicalGhostBatchEligible SP smallMod BP bigMod (J+ell) cap x
      (memorySeenBeforeGValues BP bigMod A life i) c) (g : BG) :
    ∀ j, match life g ((c g).2.2 j).1 with
      | none => True
      | some jd => ¬ jd.1.val < i := by
  intro j
  have hn := physical_G_fresh_group_not_seen SP smallMod BP bigMod (J+ell) cap
    x c (memorySeenBeforeGValues BP bigMod A life i) hb g j
  cases hl : life g ((c g).2.2 j).1 with
  | none => trivial
  | some jd =>
    intro hj
    apply hn
    apply Finset.mem_image.mpr
    refine ⟨⟨g, ((c g).2.2 j).1⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simp only [hl]; exact Or.inl hj⟩

/-- Backward classification on the ACTUAL indexed G carrier. In a canonical
before/after pending fibre every nonzero legal branch has exactly one ghost
ordering, and its full output representative is forced, not independently
permuted. The coefficient parameters are the original source G parameters. -/
theorem memory_source_primitive_G_unique_inverse
    (hs : ∀ g p, MemoryFrozenScheduleSupport (bigMod g p)
      (fun t => (offset t : ZMod (bigMod g p))) (A g p) (life g p))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (N : ℕ) (Vbig : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x yg : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (c : FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset true i))
    (hAfter : ∀ g, (Green64Fock.fockToList ((yg.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (life g) offset false i))
    (hEligible : (⟨x, yg, c⟩ :
      Σ xx : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
      Σ yy : FullPhysicalState SP smallMod BP bigMod (J+ell) cap,
        FullGhostWitness SP smallMod BP bigMod (J+ell) cap xx) ∈
      physicalGIndexedEligibleFibre SP smallMod BP bigMod J ell cap
        (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x)
        (memorySeenBeforeGValues BP bigMod A life i))
    (hterm : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
      q rho N i Vbig mu x yg c ≠ 0) :
    ∃! e : (g : BG) → Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
        ↥(memoryGhostBirthSet (A g) (life g) i),
      c = memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap
        A life offset i hs x hOld hcap e ∧
      yg = memoryPrimitiveGOutput SP smallMod BP bigMod J ell cap
        A life offset i x hOld hcap e := by
  have hb := (Finset.mem_filter.mp hEligible).2.2
  have hop := physical_nonzero_ghost_witness_is_operational SP smallMod BP bigMod
    (J+ell) cap q rho N i Vbig mu x yg c hterm
  have hrecovery : ∀ g, ∃! e : Fin (memoryGhostBirthSet (A g) (life g) i).card ≃
      ↥(memoryGhostBirthSet (A g) (life g) i),
      c g = memoryGhostLiftChoice (bigMod g) (A g) (life g) offset i
        (hs g) _ (hOld g) (cap g) (hcap g) e := by
    intro g
    apply memory_ghost_canonical_witness_recovery (bigMod g) (A g) (life g) offset i
      (hs g) _ (hOld g) (cap g) (hcap g) (c g)
    · rw [hop.2 g]
      exact hAfter g
    · exact memory_primitive_G_eligible_no_prior_birth SP smallMod BP bigMod J ell cap
        A life i x c hb g
  let e := fun g => Classical.choose (hrecovery g)
  have hc : c = memoryPrimitiveGWitness SP smallMod BP bigMod J ell cap
      A life offset i hs x hOld hcap e := by
    funext g
    exact (Classical.choose_spec (hrecovery g)).1
  have hy : yg = memoryPrimitiveGOutput SP smallMod BP bigMod J ell cap
      A life offset i x hOld hcap e := by
    apply Prod.ext
    · exact hop.1.1.symm
    · funext g
      apply Prod.ext
      · exact (hop.1.2 g).symm
      · apply (physicalFockStateListEquiv (Green64Fock.Atom (BP g) (bigMod g)) (cap g)).injective
        apply Subtype.ext
        change Green64Fock.fockToList ((yg.2 g).2) =
          Green64Fock.fockToList (memoryGhostOutputFock (bigMod g) (A g) (life g) offset i
            _ (hOld g) (cap g) (hcap g) (e g))
        rw [memory_ghost_output_list_exact, ← hop.2 g, hc]
        rfl
  refine ⟨e, ⟨hc, hy⟩, ?_⟩
  intro f hf
  funext g
  exact (Classical.choose_spec (hrecovery g)).2 (f g) (congrFun hf.1 g)
end Green64FullPhysicalE

end

end

