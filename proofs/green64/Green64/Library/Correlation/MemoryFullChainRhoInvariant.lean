module

public import Green64.Library.Correlation.MemoryGEDampingCancellation
public import Green64.Library.Correlation.Part008

@[expose] public section

/-!
# Correlation / MemoryFullChainRhoInvariant

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryFullChainRhoInvariant -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The OLD multiplier is constant on the true weighted Fock orbit.
No positivity, orbit-cardinality substitution or symmetry assumption is used. -/
private theorem old_orbit_mul434
    (rho : ℝ) (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalState SP smallMod BP bigMod (J+ell) cap → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu
      (fun x => sourceOriginalMemoryOldInput434 SP smallMod BP bigMod
        J ell cap rho x * F x) y =
    sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho y *
      fullPhysicalOrbitAverage SP smallMod BP bigMod (J+ell) cap Vs mu F y := by
  unfold fullPhysicalOrbitAverage
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only
  rw [← source_original_memory_OLD_projection434
    SP smallMod BP bigMod J ell cap rho x, (Finset.mem_filter.mp hx).2]
  ring

/-- Actual marked symmetric G, including the original chronological seen update. -/
theorem source_original_memory_SYMMETRIC_G_rho_cancellation434
    (q rho : ℝ) (hrho : rho ≠ 0) (N i : ℕ)
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho y *
      physicalMarkedSymmetricG SP smallMod BP bigMod J ell cap
        q rho N i Vs Vb mu y seen
        (fun z nextSeen => sourceOriginalMemoryOldOutput434
          SP smallMod BP bigMod J ell rho z * F z nextSeen) =
    physicalMarkedSymmetricG SP smallMod BP bigMod J ell cap
      q 1 N i Vs Vb mu y seen F := by
  unfold physicalMarkedSymmetricG
  rw [← old_orbit_mul434 SP smallMod BP bigMod J ell cap rho Vs mu]
  congr 1
  funext x
  exact source_original_memory_BIRTH_MARKED_G_rho_cancellation434
    SP smallMod BP bigMod J ell cap q rho hrho N i Vb mu x seen F

/-- Actual oriented marked symmetric E, retaining the complete signed Nu sum. -/
theorem source_original_memory_SYMMETRIC_E_OLD_sandwich434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ) :
    physicalOrientedMarkedSymmetricE SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k y seen F =
    sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho y *
      physicalOrientedMarkedSymmetricE SP smallMod BP bigMod J ell m cap patterns
        q 1 Vs Vb mu K zeta theta o k y seen
        (fun z nextSeen => sourceOriginalMemoryOldOutput434
          SP smallMod BP bigMod J ell rho z * F z nextSeen) := by
  unfold physicalOrientedMarkedSymmetricE
  rw [← old_orbit_mul434 SP smallMod BP bigMod J ell cap rho Vs mu]
  congr 1
  funext x
  exact source_original_memory_BIRTH_MARKED_E_OLD_sandwich434
    SP smallMod BP bigMod J ell m cap patterns
    q rho Vs Vb mu K zeta theta o k x seen F

/-- Exact telescoping through the SOURCE-FAITHFUL full signed marked chain.
This uses memorySourceGEChain, hence FIXED zeta and the original reversed
endpoint K on reverse edges, not the inherited start*zeta schedule.
All original G and E birth filters, source randomness, Fock orbit weights,
store/promote choices, complex coefficients and actual nextSeen survive.
No arithmetic smallness, clean-only replacement or norm hypothesis is assumed. -/
theorem source_original_memory_FULL_SOURCE_CHAIN_rho_cancellation434
    (q rho : ℝ) (hrho : rho ≠ 0)
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N n start : ℕ)
    (F : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (seen : Finset ℕ) :
    sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho y *
      memorySourceGEChain SP smallMod BP bigMod J ell m patterns cap
        q rho Vs Vb mu K zeta theta k N n start
        (fun z nextSeen => sourceOriginalMemoryOldOutput434
          SP smallMod BP bigMod J ell rho z * F z nextSeen) y seen =
    memorySourceGEChain SP smallMod BP bigMod J ell m patterns cap
      q 1 Vs Vb mu K zeta theta k N n start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      exact source_original_memory_SYMMETRIC_G_rho_cancellation434
        SP smallMod BP bigMod J ell cap q rho hrho N start Vs Vb mu y seen F
  | succ n ih =>
      simp only [memorySourceGEChain]
      simp_rw [source_original_memory_SYMMETRIC_E_OLD_sandwich434
        SP smallMod BP bigMod J ell m cap patterns q rho Vs Vb mu]
      simp_rw [ih]
      exact source_original_memory_SYMMETRIC_G_rho_cancellation434
        SP smallMod BP bigMod J ell cap q rho hrho N start Vs Vb mu y seen _

private theorem old_mul_vacuum434
    (rho : ℝ) (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) :
    sourceOriginalMemoryOldOutput434 SP smallMod BP bigMod J ell rho y *
      physicalVacuum SP smallMod BP bigMod J ell y =
    physicalVacuum SP smallMod BP bigMod J ell y := by
  by_cases h : ∀ g : BG, (y.2 g).2 = 0
  · simp [physicalVacuum, h, sourceOriginalMemoryOldOutput434]
  · simp [physicalVacuum, h]

/-- Full signed source chain between actual vacuum Fock endpoints, with an
ARBITRARY terminal observable of both physical output and actual birth history.
Consequently forgetting history is not used to obtain rho independence. -/
theorem source_original_memory_VACUUM_HISTORY_CHAIN_rho_invariant434
    (q rho : ℝ) (hrho : rho ≠ 0)
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N n start : ℕ)
    (H : FullPhysicalOutput SP smallMod BP bigMod (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell)) (seen : Finset ℕ)
    (hy : physicalVacuum SP smallMod BP bigMod J ell y = 1) :
    memorySourceGEChain SP smallMod BP bigMod J ell m patterns cap
      q rho Vs Vb mu K zeta theta k N n start
      (fun z nextSeen => physicalVacuum SP smallMod BP bigMod J ell z *
        H z nextSeen) y seen =
    memorySourceGEChain SP smallMod BP bigMod J ell m patterns cap
      q 1 Vs Vb mu K zeta theta k N n start
      (fun z nextSeen => physicalVacuum SP smallMod BP bigMod J ell z *
        H z nextSeen) y seen := by
  have hr := old_mul_vacuum434 SP smallMod BP bigMod J ell rho y
  rw [hy, mul_one] at hr
  have h := source_original_memory_FULL_SOURCE_CHAIN_rho_cancellation434
    SP smallMod BP bigMod J ell m cap patterns q rho hrho Vs Vb mu K
    zeta theta k N n start
    (fun z nextSeen => physicalVacuum SP smallMod BP bigMod J ell z * H z nextSeen)
    y seen
  simp_rw [← mul_assoc, old_mul_vacuum434 SP smallMod BP bigMod J ell rho] at h
  simpa only [hr, one_mul] using h

/-- The actual SOURCE finite root, with the original b_p prefactor,
mu-tilde, initial Nodup rule, fixed-zeta alternating E/E* schedule,
all later marked births and both physical vacua, is rho-independent.
This closes the passage from the local E/G identities to the WHOLE
coherent original finite expression. It does not identify that expression
with the arithmetic root moment, remove cutoffs, or prove transference. -/
theorem source_original_memory_SOURCE_ROOT_rho_invariant434
    (q rho : ℝ) (hrho : rho ≠ 0)
    (Vs : SG → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    memorySourceRoot SP smallMod BP bigMod J ell m patterns cap
      q rho Vs Vb K zeta theta k R =
    memorySourceRoot SP smallMod BP bigMod J ell m patterns cap
      q 1 Vs Vb K zeta theta k R := by
  dsimp only [memorySourceRoot]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : ∀ g : BG, (y.2 g).2 = 0
  · have h := source_original_memory_VACUUM_HISTORY_CHAIN_rho_invariant434
      SP smallMod BP bigMod J ell m cap patterns q rho hrho Vs Vb
      (physicalSourceMuTilde BP bigMod q (2*R) Vb)
      K zeta theta k (2*R) (2*R) 0 (fun _ _ => 1) y
      (physicalOutputInitialBirths SP smallMod BP bigMod J ell y).toFinset
      (by simp [physicalVacuum, hv])
    simp only [mul_one] at h
    rw [h]
  · simp [physicalVacuum, hv]

/-- Both rho values can stay in the original admissible interval.
No estimate at rho=1 is invoked; it was only an algebraic reference. -/
theorem source_original_memory_SOURCE_ROOT_two_rhos434
    (q rho sigma : ℝ) (hrho : rho ≠ 0) (hsigma : sigma ≠ 0)
    (Vs : SG → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    memorySourceRoot SP smallMod BP bigMod J ell m patterns cap
      q rho Vs Vb K zeta theta k R =
    memorySourceRoot SP smallMod BP bigMod J ell m patterns cap
      q sigma Vs Vb K zeta theta k R := by
  rw [source_original_memory_SOURCE_ROOT_rho_invariant434
    SP smallMod BP bigMod J ell m cap patterns q rho hrho Vs Vb K zeta theta k R,
    source_original_memory_SOURCE_ROOT_rho_invariant434
    SP smallMod BP bigMod J ell m cap patterns q sigma hsigma Vs Vb K zeta theta k R]
end Green64FullPhysicalE

end

end

