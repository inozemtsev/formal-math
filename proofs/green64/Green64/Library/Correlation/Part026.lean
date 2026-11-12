module

public import Green64.Library.Correlation.Part025
public import Green64.Library.Correlation.Part018
public import Green64.Library.Correlation.Part023
public import Green64.Library.Correlation.Part022
public import Green64.Library.Correlation.Part013
public import Green64.Library.Correlation.Part010
public import Green64.Library.Correlation.Part024
public import Green64.Library.Correlation.Part019
public import Green64.Library.Correlation.Part012

@[expose] public section

/-!
# Correlation / Part026

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MemoryB1cNonzeroEdgeAllowed -/

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

/-- Every ORIGINAL edge is actually allowed if the unchanged frozen
omega/life source RHS coefficient is nonzero. This is derived from
the literal product of source edge coefficients, without assuming
their nonvanishing separately. -/
theorem memory_source_nonzero_original_all_edges_allowed
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0) :
    ∀ i : Fin (2*R),
      memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns ω k i := by
  have hW := left_ne_zero_of_mul hn
  unfold memoryFrozenSourceWeight at hW
  have hEdgeProd :
      (∏ i : Fin (2*R),
        memoryFrozenSourceEdgeWeight SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k ω i) ≠ 0 :=
    right_ne_zero_of_mul hW
  intro i
  have hi : memoryFrozenSourceEdgeWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω i ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hEdgeProd) i (Finset.mem_univ _)
  by_contra hb
  have hzero : memoryFrozenSourceEdgeWeight SP smallMod BP bigMod J ell m
      patterns q Vsmall Vbig Knu zeta theta k ω i = 0 := by
    unfold memoryFrozenSourceEdgeWeight
    exact if_neg hb
  exact hi hzero
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cNonzeroLiteralRHS -/

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

set_option maxHeartbeats 500000

/-- Complete ORIGINAL nonzero frozen root fibre = exactly one SMALL Haar
 state mass times literal residual E edges, and per-prime true operational
 physical schedule factors each with its own ORIGINAL baseline. The latter
 remain to be identified with the separately checked frozen prime terms. -/
theorem memory_source_nonzero_original_fibre_literal_weight
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0) :
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) then
        memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0) =
    memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω *
    (∏ gp : PhysicalSourcePrime BP,
      (memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (2*R+1) (life gp) : ℂ)) := by
  let b : PhysicalSourcePrime BP → ℂ := fun gp =>
    (physicalSourceBaseline BP bigMod q (2*R) gp.1 gp.2 : ℂ)
  let op : PhysicalSourcePrime BP → ℂ := fun gp =>
    memoryFrozenPrimeOperationalScalar BP bigMod q rho (2*R) Vbig gp.1 gp.2
      (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
      (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp)
  let prime : PhysicalSourcePrime BP → ℂ := fun gp =>
    (memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
      (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
      (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
      (2*R+1) (life gp) : ℂ)
  let S : ℂ := (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ)
  let Res : ℂ := ∏ i : Fin (2*R),
    memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω i
  let B : ℂ := (physicalSourceBaselineProduct BP bigMod q (2*R) : ℂ)
  let V : ℂ := ∏ gp : PhysicalSourcePrime BP,
    (1/(Vbig gp.1 : ℂ))^(memoryFrozenPrimeRuns
      (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (2*R))
  let VB : ℂ := (∏ g : BG, 1/(Vbig g : ℂ)^(J+ell)) *
    (∏ i : Fin (2*R), ∏ g : BG, 1/(Vbig g : ℂ)^
      Green64SmallHaar.unsharedSlots (J+ell)
        (sourceBigShared J ell m (patterns (ω.2.2 i).1.1) g))
  let W : ℂ := memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
    q Vsmall Vbig Knu zeta theta k ω
  have hPrime : (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (2*R+1) (life gp) : ℝ) ≠ 0 := by
    exact_mod_cast right_ne_zero_of_mul hn
  have hs := memory_frozen_source_profile_support SP smallMod BP bigMod
    J ell m patterns ω life k q hPrime
  have hallowed := memory_source_nonzero_original_all_edges_allowed SP smallMod
    BP bigMod J ell m patterns q rho Vsmall Vbig Knu zeta theta k R ω life hn
  have hSource := memory_source_original_nonzero_fibre_frozen_operational_product
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn
  have hAssembly := memory_frozen_source_operational_prime_product_exact
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd ω life hn
  have hV := memory_source_frozen_run_V_normalization SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig k R hd ω life hs hallowed
  have hWeight := memory_frozen_source_weight_residual_factorization SP smallMod
    BP bigMod J ell m patterns q Vsmall Vbig Knu zeta theta k ω
  have hB := memory_source_original_baseline_sigma BP bigMod q (2*R)
  change B = (∏ gp : PhysicalSourcePrime BP, b gp) at hB
  change B * (∏ gp : PhysicalSourcePrime BP, op gp) =
    V * (∏ gp : PhysicalSourcePrime BP, prime gp) at hAssembly
  change V = VB at hV
  change W = (S * VB) * Res at hWeight
  change _ = S * Res * (∏ gp : PhysicalSourcePrime BP, b gp * op gp) at hSource
  calc
    _ = S * Res * (∏ gp : PhysicalSourcePrime BP, b gp * op gp) := hSource
    _ = S * Res * (B * (∏ gp : PhysicalSourcePrime BP, op gp)) := by
      rw [Finset.prod_mul_distrib, ← hB]
    _ = S * Res * (V * (∏ gp : PhysicalSourcePrime BP, prime gp)) := by rw [hAssembly]
    _ = W * (∏ gp : PhysicalSourcePrime BP, prime gp) := by rw [hV,hWeight]; ring
    _ = _ := rfl
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cNonzeroRealRHS -/

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

set_option maxHeartbeats 500000

/-- Complete ORIGINAL nonzero frozen root fibre = exactly one SMALL Haar
 state mass times literal residual E edges, and per-prime true operational
 physical schedule factors each with its own ORIGINAL baseline. The latter
 remain to be identified with the separately checked frozen prime terms. -/
theorem memory_source_nonzero_original_fibre_literal_real_weight
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hn : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k ω *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (2*R+1) (life gp) : ℝ) ≠ 0) :
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some (ω,life) then
        memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0) =
    memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k ω *
    (∏ gp : PhysicalSourcePrime BP,
      (memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (2*R+1) (life gp) : ℝ)) := by
  have hh := memory_source_nonzero_original_fibre_literal_weight SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd ω life hn
  simpa only [Complex.ofReal_prod] using hh
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cGlobalNonzeroProfiles -/

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

/-- The EXACT unchanged MemoryGlobalActualFibreWeight target for EVERY
source profile with original literal frozen RHS nonzero. The only
missing cases for the source global goal are RHS-zero profiles; no
new reconstruction/mass/normalization assumptions are present. -/
theorem memory_source_global_actual_fibre_weight_nonzero_profiles
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R)
    (hn : memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k a.1 *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
          (2*R+1) (a.2 gp) : ℝ) ≠ 0) :
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some a then
        memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0) =
    memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k a.1 *
    (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
        (2*R+1) (a.2 gp) : ℝ) := by
  rcases a with ⟨ω,life⟩
  exact memory_source_nonzero_original_fibre_literal_real_weight SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd ω life hn
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cOutsideImageZero -/

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

/-- The unchanged source GLOBAL actual-fibre goal, with its literal
original RHS, holds for every profile OUTSIDE the original forward
image, including zero-weight and incompatible profiles. The original
nonzero-profile reconstruction proves the RHS vanishes, while the
original source profile map makes the full physical fibre empty. No
new image characterization or cancellation is assumed. -/
theorem memory_source_global_actual_fibre_weight_outside_image
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R)
    (hnot : ∀ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R,
      memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt ≠ some a) :
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some a then
        memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0) =
    memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k a.1 *
    (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
        (2*R+1) (a.2 gp) : ℝ) := by
  letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R) :=
    physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
  have hrhs := memory_frozen_source_profile_outside_image_zero SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd a hnot
  have hlhs :
      (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
        if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R hd xt = some a then
          memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
            q rho Vsmall Vbig Knu zeta theta k R xt else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro xt hmem
    exact if_neg (hnot xt)
  rw [hlhs,hrhs]
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cZeroImageExactReduction -/

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

/-- Precisely the UNPROVED remaining source B zero-image condition:
when original literal frozen coefficient is zero BUT a genuine
source contributing-root image has this profile, its ORIGINAL
fully weighted dependent root fibre must vanish. This is NOT an
axiom and makes no assertion that such profiles exist; it is a
standalone explicit remaining proposition, not a theorem. -/
def MemorySourceZeroImageFibreDebt
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) : Prop :=
  ∀ hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R,
  ∀ a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R,
    memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k a.1 *
    (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
        (2*R+1) (a.2 gp) : ℝ) = 0 →
    (∃ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
       J ell m cap patterns k R,
       memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
         q rho Vsmall Vbig Knu zeta theta k R hd xt = some a) →
    letI : Fintype (PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R) :=
      physicalOrientedRootIndexedTraceFintype SP smallMod BP bigMod J ell m cap patterns k R
    (∑ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
        J ell m cap patterns k R,
      if memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some a then
        memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig Knu zeta theta k R xt else 0) = 0

/-- EXACT logical reduction of the original (unchanged) source
MemoryGlobalActualFibreWeight to its ONLY remaining zero-coefficient
inside-image obligation. Nonzero source fibres and outside-image
zero profiles are already kernel-proved without new hypotheses.
No proof of the zero-image obligation is implied here. -/
theorem memory_global_actual_fibre_weight_iff_zero_image_debt
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    MemoryGlobalActualFibreWeight SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R ↔
    MemorySourceZeroImageFibreDebt SP smallMod BP bigMod J ell m cap patterns
      q rho Vsmall Vbig Knu zeta theta k R := by
  constructor
  · intro hall
    intro hd a hzero himage
    have hh := hall hd a
    simpa only [hzero] using hh
  · intro hzero
    intro hd a
    let rhs : ℂ := memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
        q Vsmall Vbig Knu zeta theta k a.1 *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
          (2*R+1) (a.2 gp) : ℝ)
    by_cases hn : rhs ≠ 0
    · exact memory_source_global_actual_fibre_weight_nonzero_profiles
        SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
        Knu zeta theta k R hd a hn
    · by_cases himage : ∃ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
          J ell m cap patterns k R,
          memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
            q rho Vsmall Vbig Knu zeta theta k R hd xt = some a
      · have hh := hzero hd a (not_ne_iff.mp hn) himage
        change _ = rhs
        rw [hh, not_ne_iff.mp hn]
      · exact memory_source_global_actual_fibre_weight_outside_image
          SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
          Knu zeta theta k R hd a
          (fun xt hx => himage ⟨xt,hx⟩)
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cImageEdgeAllowed -/

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

/-- Every profile inside the actual ORIGINAL source forward image
necessarily has all literal oriented E-edge compatibility conditions.
This holds even when its RHS frozen coefficient vanishes; no edge
nonzero or positive root fibre is added as a premise. -/
theorem memory_source_actual_image_all_original_edges_allowed
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R)
    (himage : ∃ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R,
      memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some a) :
    ∀ i : Fin (2*R),
      memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns a.1 k i := by
  obtain ⟨xt,hp⟩ := himage
  by_cases hw : memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m
      cap patterns q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0
  · let w : MemorySourceContributingRootTrace SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R := ⟨xt,hw⟩
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k (2*R) H
    let l := Classical.choose (memory_source_root_finite_life_readout
      SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R hd.R_pos hd.big_injective w)
    have hpf : memorySourceRootFrozenProfile SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd xt =
        some (ω,fun gp : PhysicalSourcePrime BP => l gp.1 gp.2) := by
      unfold memorySourceRootFrozenProfile
      rw [dif_pos hw]
    have heq : (ω,fun gp : PhysicalSourcePrime BP => l gp.1 gp.2) = a :=
      Option.some.inj (hpf.symm.trans hp)
    have hω : ω = a.1 := congrArg Prod.fst heq
    intro i
    have he := memory_actual_frozen_edge_allowed SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H i
    simpa only [ω,hω] using he
  · have hh : memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m
        cap patterns q rho Vsmall Vbig Knu zeta theta k R hd xt = none := by
      unfold memorySourceRootFrozenProfile
      rw [dif_neg hw]
    rw [hh] at hp
    cases hp
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cImagePrimeSupport -/

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

/-- All literal prime schedules of EVERY original forward-image
profile satisfy the original source finite-lifespan residue support,
even if the scalar of that profile is zero. No assumption of a
nonzero frozen RHS or independent lifespan reconstruction. -/
theorem memory_source_actual_image_original_prime_support
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R)
    (himage : ∃ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R,
      memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some a) :
    ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
        (a.2 gp) := by
  obtain ⟨xt,hp⟩ := himage
  by_cases hw : memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m
      cap patterns q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0
  · let w : MemorySourceContributingRootTrace SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R := ⟨xt,hw⟩
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k (2*R) H
    let l := Classical.choose (memory_source_root_finite_life_readout
      SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R hd.R_pos hd.big_injective w)
    let life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1) :=
      fun gp => l gp.1 gp.2
    have hpf : memorySourceRootFrozenProfile SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd xt =
        some (ω,life) := by
      unfold memorySourceRootFrozenProfile
      rw [dif_pos hw]
    have heq : (ω,life) = a :=
      Option.some.inj (hpf.symm.trans hp)
    have hl := Classical.choose_spec (memory_source_root_finite_life_readout
      SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R hd.R_pos hd.big_injective w)
    have hVac := memory_source_root_to_path_terminal_vacuum SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    intro gp
    have hsp := memory_actual_finite_schedule_support SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H
      hd.big_injective hVac gp.1 (l gp.1) (hl gp.1) gp.2
    rw [← memory_actual_frozen_visits_exact] at hsp
    have hsource : MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (life gp) := by
      apply memory_schedule_support_offset_congr _ _ _ _ _ ?_ hsp
      intro t ht
      exact congrArg (fun z : ℤ => (z : ZMod (bigMod gp.1 gp.2)))
        (memory_actual_frozen_offset_exact SP smallMod BP bigMod J ell m
          cap patterns q rho Vbig mu k (2*R) H t (Nat.le_of_lt_succ ht)).symm
    have hω : ω = a.1 := congrArg Prod.fst heq
    have hlife : life = a.2 := congrArg Prod.snd heq
    simpa only [hω,hlife] using hsource
  · have hh : memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m
        cap patterns q rho Vsmall Vbig Knu zeta theta k R hd xt = none := by
      unfold memorySourceRootFrozenProfile
      rw [dif_neg hw]
    rw [hh] at hp
    cases hp
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cSupportedPrimeNonzero -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- Source visit damping is strictly below 1 at EVERY visit, including
both sqrt-q endpoint visits, under the unchanged source q-range. -/
theorem memory_source_eta_lt_one
    (q : ℝ) (N t : ℕ) (hq : 0 < q) (hq1 : q < 1) :
    sourceVisitEta q N t < 1 := by
  have ht := (memory_source_visit_strict q N t hq hq1).1
  unfold sourceVisitEta
  linarith

/-- Each original source-orphan factor is strictly positive; no
nonzero contribution may vanish due solely to an interior damping
term at a residue hit. -/
theorem memory_source_orphan_factor_pos
    (q : ℝ) (N t : ℕ) (hq : 0 < q) (hq1 : q < 1)
    (hit : Prop) [Decidable hit] :
    0 < 1 - sourceVisitEta q N t *
      (if hit then (1 : ℝ) else 0) := by
  by_cases h : hit
  · simp only [h, if_true, mul_one]
    have he := memory_source_eta_lt_one q N t hq hq1
    linarith
  · simp only [h, if_false, mul_zero, sub_zero]
    norm_num

/-- One genuine original represented lifespan with compatible
residue clock has NONZERO source frozen prime density.
No exceptional cancellation can occur inside a single literal
frozen supported `some` term when 0<q<1. -/
theorem memory_source_supported_some_frozen_prime_ne_zero
    (p : ℕ) [NeZero p] (q : ℝ) (N : ℕ)
    (hq : 0 < q) (hq1 : q < 1)
    (h : ℕ → ZMod p) (A : Finset ℕ)
    (az : Fin (N+1) × Fin (N+1))
    (hs : MemoryFrozenScheduleSupport p h A (some az)) :
    memoryFrozenPrimeTerm p (sourceVisitEta q N) h A (N+1) (some az) ≠ 0 := by
  rw [memory_frozen_prime_supported_normal_form p
    (sourceVisitEta q N) h A (N+1) az hs]
  have he : ∀ t, sourceVisitEta q N t ≠ 0 := by
    intro t
    exact ne_of_gt (memory_source_visit_strict q N t hq hq1).2
  have hA : (if az.1.val ∈ A then (1 : ℝ)
    else -sourceVisitEta q N az.1.val) ≠ 0 := by
    split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr (he az.1.val)
  have hZ : (if az.2.val ∈ A then (1 : ℝ)
    else -sourceVisitEta q N az.2.val) ≠ 0 := by
    split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr (he az.2.val)
  have hcore : (∏ t ∈ Finset.range (N+1),
      if az.1.val < t ∧ t < az.2.val ∧ t ∉ A then
        1 - sourceVisitEta q N t *
          (if h t = h az.1.val then (1 : ℝ) else 0)
      else 1) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    by_cases hc : az.1.val < t ∧ t < az.2.val ∧ t ∉ A
    · simpa [hc] using
        (ne_of_gt (memory_source_orphan_factor_pos q N t hq hq1
          (h t = h az.1.val)))
    · simpa only [hc, if_false] using (one_ne_zero : (1:ℝ) ≠ 0)
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hA hZ) hcore) hp
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cAllSupportedPrimeNonzero -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE

/-- For every original source finite-lifespan choice, a compatible
prime term is nonzero whenever its source absent baseline is nonzero.
There is no hidden assumption that the lifespan is represented. -/
theorem memory_source_supported_frozen_prime_term_ne_zero
    (p : ℕ) [NeZero p] (q : ℝ) (N : ℕ)
    (hq : 0 < q) (hq1 : q < 1)
    (h : ℕ → ZMod p) (A : Finset ℕ)
    (life : MemoryLifespanChoice (N+1))
    (hs : MemoryFrozenScheduleSupport p h A life)
    (hbase : 1 - (∑ t ∈ Finset.range (N+1),
        sourceVisitEta q N t) / (p : ℝ) ≠ 0) :
    memoryFrozenPrimeTerm p (sourceVisitEta q N)
      h A (N+1) life ≠ 0 := by
  cases hl : life with
  | none =>
    have ha : A = ∅ := by
      simpa only [hl,MemoryFrozenScheduleSupport] using hs
    subst A
    simpa [hl,memoryFrozenPrimeTerm,memoryAbsentTerm] using hbase
  | some az =>
    exact memory_source_supported_some_frozen_prime_ne_zero
      p q N hq hq1 h A az
      (by simpa only [hl] using hs)
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cPrimeFullNonzero -/

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

/-- Every original source frozen prime term of a compatible
lifespan is nonzero. This is independent of SMALL phase/K/edge
cancellation and does not assume a nonzero RHS. -/
theorem memory_source_compatible_frozen_prime_all_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (gp : PhysicalSourcePrime BP) :
    memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
      (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
        J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
      (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
      (2*R+1) (life gp) ≠ 0 := by
  have hbase :
      1 - (∑ t ∈ Finset.range (2*R+1),
          sourceVisitEta q (2*R) t) / (bigMod gp.1 gp.2 : ℝ) ≠ 0 := by
    change physicalSourceBaseline BP bigMod q (2*R) gp.1 gp.2 ≠ 0
    exact ne_of_gt (physicalSourceBaseline_positive_above_visits BP bigMod
      q (2*R) gp.1 gp.2 (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one)
      (hd.big_above_visits gp.1 gp.2))
  exact memory_source_supported_frozen_prime_term_ne_zero
    (bigMod gp.1 gp.2) q (2*R) hd.q_pos hd.q_lt_one
    (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
      J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
    (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
    (life gp) (hs gp) hbase

/-- The TRUE original frozen-product prime side is nonzero on all
compatible source lifespans, even if the frozen omega edge coefficient
is zero. Consequently all possible RHS-zero support comes from
the source path edge weight, not a prime Haar/orphan factor. -/
theorem memory_source_compatible_prime_full_product_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp)) :
    (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (2*R+1) (life gp) : ℝ) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro gp hgp
  exact memory_source_compatible_frozen_prime_all_nonzero SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig k R hd ω life hs gp
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cImageRHSOnlyEdgeZero -/

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

/-- Source RHS-zero profile INSIDE the image cannot arise from
any vanishing original prime Haar/lifespan term. This is a
noncircular consequence of the actual physical forward-readout
schedule support and strict source q inequalities. -/
theorem memory_source_actual_image_frozen_prime_product_ne_zero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R)
    (himage : ∃ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R,
      memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some a) :
    (∏ gp : PhysicalSourcePrime BP,
      memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
        (2*R+1) (a.2 gp) : ℝ) ≠ 0 := by
  have hs := memory_source_actual_image_original_prime_support SP smallMod BP
    bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta
    k R hd a himage
  exact memory_source_compatible_prime_full_product_nonzero SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig k R hd a.1 a.2 hs

/-- The remaining original SOURCE zero-image obstruction is EXACTLY
the vanishing of the frozen omega edge weight (not the prime density).
This does NOT prove that the physical fibre vanishes. -/
theorem memory_source_actual_image_rhs_zero_iff_frozen_edge_zero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R)
    (himage : ∃ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R,
      memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some a) :
    (memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k a.1 *
      (∏ gp : PhysicalSourcePrime BP,
        memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
          (2*R+1) (a.2 gp) : ℝ) = 0) ↔
    memoryFrozenSourceWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k a.1 = 0 := by
  have hp := memory_source_actual_image_frozen_prime_product_ne_zero SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd a himage
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · have hzReal : (∏ gp : PhysicalSourcePrime BP,
          memoryFrozenPrimeTerm (bigMod gp.1 gp.2) (sourceVisitEta q (2*R))
            (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
              J ell m patterns a.1 k t : ZMod (bigMod gp.1 gp.2)))
            (memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 gp)
            (2*R+1) (a.2 gp) : ℝ) = 0 := by exact_mod_cast h
      exact False.elim (hp hzReal)
  · intro hz
    rw [hz]
    simp
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cFrameSupportNoWeight -/

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

/-- Original compatible E_i frame WITHOUT any nonzero small
kernel or frozen coefficient hypothesis. The original BIG
residue lift uses actual source lifespan support, while SMALL
Haar support is kept as a separate physical legality premise.
In contrast to the earlier nonzero-Fourier shortcut, this works
even if K or a summed SMALL kernel cancels to zero. -/
theorem memory_source_frozen_frame_compatible_from_actual_small_legal
    {N : ℕ}
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns N)
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (N+1))
    (k : ℤ)
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (i : Fin N)
    (ha : memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns ω k i)
    (hsmall :
      Green64SmallHaar.groupEdgeAllowedPerm SP smallMod (J+ell)
        (sourceSmallShared J ell)
        (physicalAlternatingSign i.val*k*
          (memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω i : ℤ))
        (ω.2.2 i).2.2.2.1 (ω.2.2 i).2.2.2.2
        (ω.1 i.castSucc) (ω.1 i.succ)) :
    ω.2.2 i ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod
      J ell m patterns
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns ω life k hs i.castSucc)
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns ω life k hs i.succ)
      (physicalAlternatingSign i.val) k := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ha.1, ?_, ?_, ?_, ?_⟩
  · exact ha.2.2.1
  · simpa only [memoryIndependentD, memoryFrozenSourceD,
      memoryFrozenSourceIndependentLift, Green64SmallHaar.marks] using hsmall
  · simpa only [memoryIndependentD, memoryFrozenSourceD,
      memoryFrozenSourceIndependentLift, Green64SmallHaar.marks] using
      memory_frozen_source_lift_BIG_edge SP smallMod BP bigMod J ell m
        patterns ω life k hs i ha
  · simpa only [memoryIndependentD, memoryFrozenSourceD,
      memoryFrozenSourceIndependentLift, Green64SmallHaar.marks] using
      (memory_frozen_source_offset_step SP smallMod BP bigMod J ell m
        patterns ω k i.val i.isLt).symm
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cActualSmallSupport -/

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

/-- Every genuine source witness E choice lies in SMALL independent
Haar support of its own ORIGINAL frozen frame, even when the weighted
SMALL kernel or frozen source coefficient is zero. -/
theorem memory_actual_source_frozen_small_support
    (q rho : ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N)
    (i : Fin N) :
    let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H
    Green64SmallHaar.groupEdgeAllowedPerm SP smallMod (J+ell)
      (sourceSmallShared J ell)
      (physicalAlternatingSign i.val*k*
        (memoryFrozenSourceD SP smallMod BP bigMod J ell m patterns ω i : ℤ))
      (ω.2.2 i).2.2.2.1 (ω.2.2 i).2.2.2.2
      (ω.1 i.castSucc) (ω.1 i.succ) := by
  dsimp only
  let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m
    cap patterns q rho Vbig mu k N H
  have hleg := (H.E_legal i.val i.isLt).2.2.2.2
  have hbefore := (memory_actual_beforeE_original_coordinates SP smallMod
    BP bigMod J ell m cap patterns q rho Vbig mu k N H i.val i.isLt).1
  have hD := memory_actual_frozen_D_exact SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k N H i
  have hout : (H.before (i.val+1)).1 =
      (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns
        (H.beforeE i.val) (physicalAlternatingSign i.val) k
        (H.edge i.val)).1 := by
    exact congrArg Prod.fst (H.E_output i.val i.isLt)
  unfold sourceOrientedStep at hleg
  rw [hD]
  dsimp only [ω, memoryActualWitnessFrozenPath, memoryPrimitiveEFrameOf,
    Fin.val_castSucc, Fin.val_succ]
  rw [← hbefore, hout]
  exact hleg
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cImageFrameCompatible -/

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

/-- An ORIGINAL source frozen E frame actually seen in the
nonzero-root forward image is physically compatible with the
source-independent residue lift EVEN WHEN its source Fourier
coefficient vanishes by cancellation. The original SMALL legal
condition is recovered from the contributing source witness, not
from any nonzero source kernel premise. -/
theorem memory_source_actual_image_frozen_E_frame_compatible
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R)
    (himage : ∃ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R,
      memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some a)
    (i : Fin (2*R)) :
    a.1.2.2 i ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod
      J ell m patterns
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns a.1 k) i.val
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns a.1 a.2 k
        (memory_source_actual_image_original_prime_support SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
          hd a himage) i.castSucc)
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns a.1 a.2 k
        (memory_source_actual_image_original_prime_support SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
          hd a himage) i.succ)
      (physicalAlternatingSign i.val) k := by
  obtain ⟨xt,hp⟩ := himage
  by_cases hw : memorySourceRootIndexedWeight SP smallMod BP bigMod J ell m
      cap patterns q rho Vsmall Vbig Knu zeta theta k R xt ≠ 0
  · let w : MemorySourceContributingRootTrace SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R := ⟨xt,hw⟩
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k (2*R) H
    let l := Classical.choose (memory_source_root_finite_life_readout
      SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
      zeta theta k R hd.R_pos hd.big_injective w)
    let life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1) :=
      fun gp => l gp.1 gp.2
    have hpf : memorySourceRootFrozenProfile SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd xt =
        some (ω,life) := by
      unfold memorySourceRootFrozenProfile
      rw [dif_pos hw]
    have heq : (ω,life) = a := Option.some.inj (hpf.symm.trans hp)
    have hω : ω = a.1 := congrArg Prod.fst heq
    have hlife : life = a.2 := congrArg Prod.snd heq
    have hs := memory_source_actual_image_original_prime_support SP smallMod
      BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
      hd a ⟨xt,hp⟩
    have hs' : ∀ gp : PhysicalSourcePrime BP,
        MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
          (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
            J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
          (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
          (life gp) := by
      simpa only [hω,hlife] using hs
    have ha' := memory_actual_frozen_edge_allowed SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k (2*R) H i
    have hsmall' := memory_actual_source_frozen_small_support SP smallMod
      BP bigMod J ell m cap patterns q rho Vbig mu k (2*R) H i
    have hframe := memory_source_frozen_frame_compatible_from_actual_small_legal
      SP smallMod BP bigMod J ell m patterns ω life k hs' i ha' hsmall'
    simpa only [hω,hlife] using hframe
  · have hh : memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m
        cap patterns q rho Vsmall Vbig Knu zeta theta k R hd xt = none := by
      unfold memorySourceRootFrozenProfile
      rw [dif_neg hw]
    rw [hh] at hp
    cases hp
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cFreshScheduleNoWeight -/

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

set_option maxHeartbeats 900000

/-- For an ORIGINAL nonzero frozen source profile, an oriented E_i
fresh BIG slot is precisely a true prime with a fresh ACTIVE lifespan
start at that visit. This is derived from the actual source edge
allowedness (with Nu/aux and permutation compatibility), not postulated
from an arbitrary shared-slots model. -/
theorem memory_source_frozen_E_fresh_from_compatible
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (i : Fin (2*R))
    (hf : ω.2.2 i ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod
      J ell m patterns
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns ω life k hs i.castSucc)
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns ω life k hs i.succ)
      (physicalAlternatingSign i.val) k)
    (g : BG) (j : Fin (J+ell)) :
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
      patterns ω life k hs i.succ
    let f := ω.2.2 i
    let target := Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)
    j ∈ orientedFresh (J+ell)
      (sourceBigShared J ell m (patterns f.1.1) g)
      (memoryEPromoteSlots (J+ell)
        (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun p => life ⟨g,p⟩) i.val target (f.2.2.1 g)) ↔
      memoryScheduleFresh
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω
          ⟨g,target (f.2.2.1 g j)⟩)
        (life ⟨g,target (f.2.2.1 g j)⟩) i.val := by
  dsimp only
  let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
    patterns ω life k hs i.castSucc
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
    patterns ω life k hs i.succ
  let f := ω.2.2 i
  have hA0 (g : BG) (p : BP g) :
      i.val ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩ ↔
      ∃ l, Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) l = p :=
    memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.castSucc g p
  have hA1 (g : BG) (p : BP g) :
      i.val+1 ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩ ↔
      ∃ l, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) l = p :=
    memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.succ g p
  have hshared : ∀ j, j ∈ sourceBigShared J ell m (patterns f.1.1) g →
      Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) (f.2.1 g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (f.2.2.1 g j) := by
    intro j hj
    exact ((Finset.mem_filter.mp hf).2.2.2.2.1 g).2 j hj
  have hcont : ∀ j l,
      Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) (f.2.1 g j) =
      Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) (f.2.2.1 g l) →
      j ∈ sourceBigShared J ell m (patterns f.1.1) g ∧ l = j := by
    intro j l he
    exact memory_source_active_continuation_is_shared SP smallMod BP bigMod
      J ell m hd.small_prime hd.big_prime hd.big_injective hd.disjoint
      (patterns f.1.1) f.1.2 ix iy
      (Finset.mem_filter.mp hf).2.2.1
      f.2.1 f.2.2.1 f.2.2.2.1
      (physicalAlternatingSign i.val) k (Finset.mem_filter.mp hf).2.1
      hd.k_ne hd.big_above_k (Finset.mem_filter.mp hf).2.2.2.2.1 g j l he
  exact memory_E_fresh_slot_iff (J+ell) (bigMod g)
    (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun p => life ⟨g,p⟩)
    (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
    i.val (fun p => hs ⟨g,p⟩)
    (Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g))
    (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
    (f.2.1 g) (f.2.2.1 g) (hA0 g) (hA1 g)
    (sourceBigShared J ell m (patterns f.1.1) g)
    hshared hcont j
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cEVmuFromCompatible -/

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

set_option maxHeartbeats 900000

/-- For the ORIGINAL nonzero frozen source profile, the complete BIG
E_i factor consisting of the promotion V denominators and FRESH
mu_tilde integrations equals the exact product of the corresponding
prime-level lifespan schedule factors. Every original endpoint
permutation and its actual target active state is present in the LHS.
No extra V or permutation factorial is introduced. -/
theorem memory_source_frozen_E_V_mu_prime_from_compatible
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (mu : (g : BG) → BP g → ℝ) (i : Fin (2*R))
    (hf : ω.2.2 i ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod
      J ell m patterns
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns ω life k hs i.castSucc)
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns ω life k hs i.succ)
      (physicalAlternatingSign i.val) k) :
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
      patterns ω life k hs i.succ
    let f := ω.2.2 i
    (∏ g : BG,
      (1 / (Vbig g : ℂ)) ^
        (memoryEPromoteSlots (J+ell)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) i.val
          (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
          (f.2.2.1 g)).card *
      (∏ j ∈ orientedFresh (J+ell)
        (sourceBigShared J ell m (patterns f.1.1) g)
        (memoryEPromoteSlots (J+ell)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) i.val
          (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
          (f.2.2.1 g)),
        (mu g (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)
          (f.2.2.1 g j)) : ℂ))) =
    (∏ gp : PhysicalSourcePrime BP,
      (if memorySchedulePromote
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (life gp) i.val then (1/(Vbig gp.1 : ℂ)) else 1) *
      (if memoryScheduleFresh
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp)
        (life gp) i.val then (mu gp.1 gp.2 : ℂ) else 1)) := by
  dsimp only
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
    patterns ω life k hs i.succ
  let f := ω.2.2 i
  conv_rhs => rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro g hg
  let target := Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)
  have hA1 : ∀ p : BP g,
      i.val+1 ∈ memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩ ↔
      ∃ j, target j = p :=
    fun p => memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.succ g p
  have hFresh (j : Fin (J+ell)) :
      j ∈ orientedFresh (J+ell)
        (sourceBigShared J ell m (patterns f.1.1) g)
        (memoryEPromoteSlots (J+ell)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) i.val target (f.2.2.1 g)) ↔
      memoryScheduleFresh
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω
          ⟨g,target (f.2.2.1 g j)⟩)
        (life ⟨g,target (f.2.2.1 g j)⟩) i.val := by
    exact memory_source_frozen_E_fresh_from_compatible SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta
      k R hd ω life hs i hf g j
  exact memory_B1b_E_V_mu_exact (J+ell)
    (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
    (fun p => life ⟨g,p⟩) i.val target
    (Green64SmallHaar.marks_injective _ _ _)
    (f.2.2.1 g) hA1
    (sourceBigShared J ell m (patterns f.1.1) g)
    hFresh (Vbig g : ℂ) (fun p => (mu g p : ℂ))
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cEBigPrimeNoWeight -/

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

/-- Full TRUE original E_i BIG row, preserving the exact two ordered
OLD rho counts, all promotions and all fresh mu integrations, equals
a product over the genuine source numerical prime/lifespan choices.
No new factor of V, no symmetry normalization, no surrogate E kernel. -/
theorem memory_source_frozen_E_BIG_row_prime_from_compatible
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (mu : (g : BG) → BP g → ℝ) (i : Fin (2*R))
    (hf : ω.2.2 i ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod
      J ell m patterns
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns ω life k hs i.castSucc)
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns ω life k hs i.succ)
      (physicalAlternatingSign i.val) k) :
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
      patterns ω life k hs i.succ
    let f := ω.2.2 i
    (∏ g : BG,
      (rho : ℂ) ^
        ((memoryCanonicalPendingList (bigMod g)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          false i.val).countP (fun z => z.2 = 0) +
         (memoryCanonicalPendingList (bigMod g)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩)
          (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
          true (i.val+1)).countP (fun z => z.2 = 0)) *
      ((1/(Vbig g : ℂ)) ^
        (memoryEPromoteSlots (J+ell)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) i.val
          (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
          (f.2.2.1 g)).card *
      (∏ j ∈ orientedFresh (J+ell)
        (sourceBigShared J ell m (patterns f.1.1) g)
        (memoryEPromoteSlots (J+ell)
          (fun p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
          (fun p => life ⟨g,p⟩) i.val
          (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g))
          (f.2.2.1 g)),
        (mu g (Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g)
          (f.2.2.1 g j)) : ℂ)))) =
    (∏ gp : PhysicalSourcePrime BP,
      memoryOriginalEPerPrimeRow BP bigMod
        (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
        (fun g p => life ⟨g,p⟩)
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k)
        i.val rho Vbig mu gp) := by
  dsimp only
  have hOld := memory_source_frozen_E_rho_group_prime_product SP smallMod
    BP bigMod J ell m patterns ω life k rho i
  have hNew := memory_source_frozen_E_V_mu_prime_from_compatible SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd ω life hs mu i hf
  dsimp only at hOld hNew
  rw [Finset.prod_mul_distrib]
  rw [hOld, hNew]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro gp hgp
  unfold memoryOriginalEPerPrimeRow
  ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cEFrameResidualNoWeight -/

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
set_option maxHeartbeats 900000
set_option maxRecDepth 3000

/-- The ORIGINAL E_i full physical scalar = literal source residual
edge (Nu, auxiliary, four endpoint permutations, orientation, K,
SMALL Haar) times exactly one BIG prime schedule rho/V/mu product.
Source frozen coefficient is assumed nonzero only to derive the
actual frame compatibility and prime support. -/
theorem memory_source_E_frame_residual_prime_from_compatible
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (mu : (g : BG) → BP g → ℝ) (i : Fin (2*R))
    (hf : ω.2.2 i ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod
      J ell m patterns
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns ω life k hs i.castSucc)
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns ω life k hs i.succ)
      (physicalAlternatingSign i.val) k)
    (ha : memoryFrozenSourceEdgeAllowed SP smallMod BP J ell m patterns ω k i) :
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
    let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
      patterns ω life k hs i.castSucc
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m
      patterns ω life k hs i.succ
    memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      A L offset i.val ix iy q rho Vsmall Vbig mu
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i) =
    memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod
      J ell m patterns q Vsmall Vbig Knu zeta theta k ω i *
    (∏ gp : PhysicalSourcePrime BP,
      memoryOriginalEPerPrimeRow BP bigMod A L offset i.val rho Vbig mu gp) := by
  dsimp only
  let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.castSucc
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.succ
  have hbig := memory_source_frozen_E_BIG_row_prime_from_compatible SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R
    hd ω life hs mu i hf
  dsimp only at hbig
  conv_rhs => rw [← hbig]
  unfold memoryPrimitiveEFrameCoefficient memoryFrozenSourceResidualEdgeWeight
  rw [if_pos ha]
  simp only [memoryFrozenSourceIndependentLift, memoryFrozenSourceD,
    memoryIndependentD, Green64SmallHaar.marks]
  ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cImageEFrameResidualExact -/

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

/-- The ORIGINAL primitive E frame coefficient at every genuine
forward-image source path, including all profiles whose SMALL/Fourier
kernel cancels to zero, has the exact original residual coefficient
times the true prime-level OLD/promotion/fresh scalar. There is
NO assumption that frozen weight or any frame coefficient is nonzero. -/
theorem memory_source_actual_image_E_frame_residual_factor
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (a : MemorySourceFrozenRootProfile SP smallMod BP J ell m patterns R)
    (himage : ∃ xt : PhysicalOrientedRootIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns k R,
      memorySourceRootFrozenProfile SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd xt = some a)
    (i : Fin (2*R)) :
    let hs := memory_source_actual_image_original_prime_support SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd a himage
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns a.1 ⟨g,p⟩
    let L := fun g p => a.2 ⟨g,p⟩
    let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns a.1 k
    memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      A L offset i.val
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns a.1 a.2 k hs i.castSucc)
      (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
        J ell m patterns a.1 a.2 k hs i.succ)
      q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k (a.1.2.2 i) =
    memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod
      J ell m patterns q Vsmall Vbig Knu zeta theta k a.1 i *
    (∏ gp : PhysicalSourcePrime BP,
      memoryOriginalEPerPrimeRow BP bigMod A L offset i.val rho Vbig
        (physicalSourceMuTilde BP bigMod q (2*R) Vbig) gp) := by
  dsimp only
  let hs := memory_source_actual_image_original_prime_support SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd a himage
  have hf := memory_source_actual_image_frozen_E_frame_compatible SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta
    k R hd a himage i
  have ha := (memory_source_actual_image_all_original_edges_allowed SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta
    k R hd a himage) i
  exact memory_source_E_frame_residual_prime_from_compatible SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta
    k R hd a.1 a.2 hs
    (physicalSourceMuTilde BP bigMod q (2*R) Vbig) i hf ha
end Green64FullPhysicalE

end

end

/-! ## MemoryB1cZeroWeightResidualExists -/

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

/-- The unchanged source frozen weight can only vanish via an
original E_i residual edge, since all original SMALL input Haar
and every explicit BIG V denominator are strictly nonzero under
the real source domain. This does NOT yet evaluate root fibre sums. -/
theorem memory_source_frozen_weight_zero_has_zero_residual
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hz : memoryFrozenSourceWeight SP smallMod BP bigMod
      J ell m patterns q Vsmall Vbig Knu zeta theta k ω = 0) :
    ∃ i : Fin (2*R),
      memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod
        J ell m patterns q Vsmall Vbig Knu zeta theta k ω i = 0 := by
  classical
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m
    cap patterns ω life k hd.cap_saturated true ⟨0,by omega⟩
  let S : ℂ := (Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vsmall : ℂ)
  let V0 : ℂ := ∏ g : BG, 1/(Vbig g : ℂ)^(J+ell)
  let VE : ℂ := ∏ i : Fin (2*R), ∏ g : BG,
    1/(Vbig g : ℂ)^Green64SmallHaar.unsharedSlots (J+ell)
      (sourceBigShared J ell m (patterns (ω.2.2 i).1.1) g)
  let Res : Fin (2*R) → ℂ := fun i =>
    memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod
      J ell m patterns q Vsmall Vbig Knu zeta theta k ω i
  have hmu : ∀ g p, 0 < mu g p := by
    intro g p
    exact physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R)
      Vbig g p (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one)
      (hd.Vbig_pos g) (hd.big_above_visits g p)
  have hH : (fullPhysicalMass SP smallMod BP bigMod (J+ell)
      cap Vsmall mu x0 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt
      (fullPhysicalMass_pos SP smallMod BP bigMod (J+ell)
        cap Vsmall mu hd.Vsmall_pos hmu x0))
  have hHilbert := memory_source_frozen_initial_physical_mass_prime_exact
    SP smallMod BP bigMod J ell m cap patterns ω life
      k hd.cap_saturated Vsmall mu
  change (fullPhysicalMass SP smallMod BP bigMod (J+ell)
    cap Vsmall mu x0 : ℂ) = S * _ at hHilbert
  rw [hHilbert] at hH
  have hS : S ≠ 0 := left_ne_zero_of_mul hH
  have hVb : ∀ g : BG, (Vbig g : ℂ) ≠ 0 := by
    intro g
    exact_mod_cast ne_of_gt (hd.Vbig_pos g)
  have hV0 : V0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro g hg
    exact div_ne_zero one_ne_zero (pow_ne_zero _ (hVb g))
  have hVE : VE ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro g hg
    exact div_ne_zero one_ne_zero (pow_ne_zero _ (hVb g))
  have hW := memory_frozen_source_weight_residual_factorization SP smallMod
    BP bigMod J ell m patterns q Vsmall Vbig Knu zeta theta k ω
  change _ = (S * (V0*VE)) * (∏ i : Fin (2*R), Res i) at hW
  rw [hW] at hz
  have hres : (∏ i : Fin (2*R), Res i) = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact False.elim ((mul_ne_zero hS (mul_ne_zero hV0 hVE)) h)
    · exact h
  by_contra hn
  have hall : ∀ i : Fin (2*R), Res i ≠ 0 := by
    intro i
    by_contra hi
    exact hn ⟨i,hi⟩
  exact (Finset.prod_ne_zero_iff.mpr (fun i hi => hall i)) hres
end Green64FullPhysicalE

end

end

/-! ## MemoryB2EOrbitNoWeight -/

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

theorem memory_frozen_source_actual_E_orbit_sum_without_weight_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (hf : ∀ i : Fin (2*R),
      ω.2.2 i ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod
        J ell m patterns
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
          J ell m patterns ω life k hs i.castSucc)
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
          J ell m patterns ω life k hs i.succ)
        (physicalAlternatingSign i.val) k)
    (i : Fin (2*R))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated false i.castSucc)) :
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
    let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
      ω life k hs i.castSucc
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
      ω life k hs i.succ
    (∑ xe ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
        (fun xe => physicalFockProjection SP smallMod BP bigMod (J+ell) cap xe =
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap x),
      ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall
        (physicalSourceMuTilde BP bigMod q (2*R) Vbig) xe : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall
          (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x) : ℂ)) *
      (∑ z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
          A L offset i.val xe iy (physicalAlternatingSign i.val) k (ω.2.2 i),
        sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vsmall Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
          (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
          zeta theta (physicalAlternatingSign i.val) k xe z)) =
    memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      A L offset i.val ix iy q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i) := by
  dsimp only
  let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
  let L := fun g p => life ⟨g,p⟩
  let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.castSucc
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.succ
  have hsmall : x.1 = ix.1 := congrArg Prod.fst hx
  have hactive : ∀ g, (x.2 g).1 = Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) :=
    fun g => congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).1) hx
  have hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (L g) offset false i.val) := by
    intro g
    have hm := congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).2) hx
    exact (Multiset.coe_eq_coe.mp hm).trans (List.Perm.of_eq
      (memory_frozen_source_physical_pending SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated false i.castSucc g))
  have hA0 : ∀ g p, i.val ∈ A g p ↔
      ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (ix.2 g) j = p :=
    fun g p => memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.castSucc g p
  have hA1 : ∀ g p, i.val+1 ∈ A g p ↔
      ∃ j, Green64SmallHaar.marks (bigMod g) (J+ell) (iy.2 g) j = p :=
    fun g p => memory_frozen_source_visits_at SP smallMod BP J ell m patterns ω i.succ g p
  exact memory_source_primitive_E_orbit_weighted_fibre SP smallMod BP bigMod
    J ell m cap patterns A L offset i.val (fun g p => hs ⟨g,p⟩)
    q rho Vsmall Vbig k R hd ix iy x hsmall hactive hOld hA0 hA1
    (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    (fun g p => physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R) Vbig g p
      (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one) (hd.Vbig_pos g) (hd.big_above_visits g p))
    (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
    zeta theta (physicalAlternatingSign i.val) (ω.2.2 i)
    (hf i)
end Green64FullPhysicalE

end

end

/-! ## MemoryB2GReadoutNoWeight -/

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

theorem memory_frozen_source_actual_G_slice_readout_no_weight
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (i : Fin (2*R))
    (x : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (hx : physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated true i.castSucc))
    (yc : FullPhysicalState SP smallMod BP bigMod (J+ell) cap ×
      FullGhostWitness SP smallMod BP bigMod (J+ell) cap x)
    (hyc : yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩)
      (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val x)
    (ht : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho (2*R) i.val Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig) x yc.1 yc.2 ≠ 0) :
    physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1 =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap
        (memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
          ω life k hd.cap_saturated false i.castSucc) ∧
    memorySeenBeforeGValues BP bigMod
      (fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩)
      (fun g p => life ⟨g,p⟩) i.val ∪
      (physicalGhostFreshBirths SP smallMod BP bigMod (J+ell) cap x yc.2).toFinset =
      memoryBornBeforeValues BP bigMod (fun g p => life ⟨g,p⟩) (i.val+1) := by
  let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
  let L := fun g p => life ⟨g,p⟩
  let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  have hOld : ∀ g, (Green64Fock.fockToList ((x.2 g).2)).Perm
      (memoryCanonicalPendingList (bigMod g) (A g) (L g) offset true i.val) := by
    intro g
    have hm := congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).2) hx
    exact (Multiset.coe_eq_coe.mp hm).trans (List.Perm.of_eq
      (memory_frozen_source_physical_pending SP smallMod BP bigMod J ell m cap patterns
        ω life k hd.cap_saturated true i.castSucc g))
  have hspec := (Finset.mem_filter.mp hyc).2
  obtain ⟨e,he,hu⟩ := memory_source_primitive_G_unique_inverse SP smallMod BP bigMod
    J ell cap A L offset i.val (fun g p => hs ⟨g,p⟩) hd.cap_saturated
    q rho (2*R) Vbig (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    x yc.1 yc.2 hOld hspec.2 hspec.1 ht
  constructor
  · apply Prod.ext
    · rw [he.2]
      change x.1 = ω.1 i.castSucc
      exact congrArg Prod.fst hx
    · funext g
      apply Prod.ext
      · rw [he.2]
        change (x.2 g).1 = (ω.2.1 i.castSucc g).val
        exact congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
          (yy.2 g).1) hx
      · change (Green64Fock.fockToList ((yc.1.2 g).2) :
          Multiset (Green64Fock.Atom (BP g) (bigMod g))) = _
        rw [Multiset.coe_eq_coe.mpr (hspec.2 g)]
        exact (memory_canonical_Fock_multiset_exact (bigMod g) (A g) (L g) offset
          false i.val (cap g) (hd.cap_saturated g)).symm
  · rw [he.1]
    exact memory_primitive_G_seen_update SP smallMod BP bigMod J ell cap A L offset i.val
      (fun g p => hs ⟨g,p⟩) x hOld hd.cap_saturated e
end Green64FullPhysicalE

end

end

/-! ## MemoryB2GEOrbitNoWeight -/

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

theorem memory_frozen_source_actual_GE_two_orbit_sum_no_weight
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (ω : MemoryFrozenSourcePath SP smallMod BP J ell m patterns (2*R))
    (life : PhysicalSourcePrime BP → MemoryLifespanChoice (2*R+1))
    (hs : ∀ gp : PhysicalSourcePrime BP,
      MemoryFrozenScheduleSupport (bigMod gp.1 gp.2)
        (fun t => (memoryFrozenSourceOffset SP smallMod BP bigMod
          J ell m patterns ω k t : ZMod (bigMod gp.1 gp.2)))
        (memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω gp) (life gp))
    (hf : ∀ i : Fin (2*R),
      ω.2.2 i ∈ memoryPrimitiveECompatibleFrames SP smallMod BP bigMod
        J ell m patterns
        (memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k) i.val
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
          J ell m patterns ω life k hs i.castSucc)
        (memoryFrozenSourceIndependentLift SP smallMod BP bigMod
          J ell m patterns ω life k hs i.succ)
        (physicalAlternatingSign i.val) k)
    (i : Fin (2*R))
 :
    let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
    let L := fun g p => life ⟨g,p⟩
    let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
    let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
      ω life k hd.cap_saturated true i.castSucc
    let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
      ω life k hs i.castSucc
    let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
      ω life k hs i.succ
    let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
    let E := memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
      A L offset i.val ix iy q rho Vsmall Vbig mu
      (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i)
    (∑ x ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
        (fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
          physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0),
      ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ) /
        (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
          (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) : ℂ)) *
      (∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod J ell cap A L offset i.val x,
        physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho (2*R) i.val Vbig mu x yc.1 yc.2 *
        (∑ xe ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
            (fun xe => physicalFockProjection SP smallMod BP bigMod (J+ell) cap xe =
              physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1),
          ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu xe : ℂ) /
            (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
              (physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1) : ℂ)) *
          (∑ z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
              A L offset i.val xe iy (physicalAlternatingSign i.val) k (ω.2.2 i),
            sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
              q rho Vsmall Vbig mu
              (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
              zeta theta (physicalAlternatingSign i.val) k xe z)))) =
    memoryPrimitiveGUnorderedCoefficient BP bigMod A L offset i.val q rho (2*R) Vbig mu * E := by
  dsimp only
  let A := fun g p => memoryFrozenSourceVisits SP smallMod BP J ell m patterns ω ⟨g,p⟩
  let L := fun g p => life ⟨g,p⟩
  let offset := memoryFrozenSourceOffset SP smallMod BP bigMod J ell m patterns ω k
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let x0 := memoryFrozenSourcePhysicalState SP smallMod BP bigMod J ell m cap patterns
    ω life k hd.cap_saturated true i.castSucc
  let iy := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.succ
  let ix := memoryFrozenSourceIndependentLift SP smallMod BP bigMod J ell m patterns
    ω life k hs i.castSucc
  let E := memoryPrimitiveEFrameCoefficient SP smallMod BP bigMod J ell m patterns
    A L offset i.val ix iy q rho Vsmall Vbig mu
    (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
    zeta theta (physicalAlternatingSign i.val) k (ω.2.2 i)
  let S := (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
    (fun x => physicalFockProjection SP smallMod BP bigMod (J+ell) cap x =
      physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0)
  let ratio := fun x => (fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu x : ℂ) /
    (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap x0) : ℂ)
  have hG := memory_source_primitive_G_orbit_weighted_fibre SP smallMod BP bigMod J ell cap
    A L offset i.val hd.big_injective (fun g p => hs ⟨g,p⟩) hd.cap_saturated
    q rho (2*R) Vsmall Vbig mu hd.Vsmall_pos
    (fun g p => physicalSourceMuTilde_pos_above_visits BP bigMod q (2*R) Vbig g p
      (le_of_lt hd.q_pos) (le_of_lt hd.q_lt_one) (hd.Vbig_pos g) (hd.big_above_visits g p))
    x0 (fun g => List.Perm.of_eq (memory_frozen_source_physical_pending SP smallMod BP bigMod
      J ell m cap patterns ω life k hd.cap_saturated true i.castSucc g))
  have hreduce :
      (∑ x ∈ S, ratio x * (∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod
          J ell cap A L offset i.val x,
        physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho (2*R) i.val Vbig mu x yc.1 yc.2 *
        (∑ xe ∈ (Finset.univ : Finset (FullPhysicalState SP smallMod BP bigMod (J+ell) cap)).filter
            (fun xe => physicalFockProjection SP smallMod BP bigMod (J+ell) cap xe =
              physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1),
          ((fullPhysicalMass SP smallMod BP bigMod (J+ell) cap Vsmall mu xe : ℂ) /
            (physicalOrbitMass SP smallMod BP bigMod (J+ell) cap Vsmall mu
              (physicalFockProjection SP smallMod BP bigMod (J+ell) cap yc.1) : ℂ)) *
          (∑ z ∈ memoryPrimitiveEFixedFrameFibre SP smallMod BP bigMod J ell m cap patterns
              A L offset i.val xe iy (physicalAlternatingSign i.val) k (ω.2.2 i),
            sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
              q rho Vsmall Vbig mu
              (memoryOrientationK BP J ell m patterns Knu (physicalAlternatingSign i.val))
              zeta theta (physicalAlternatingSign i.val) k xe z)))) =
      (∑ x ∈ S, ratio x * (∑ yc ∈ memoryPrimitiveGFixedInputFibre SP smallMod BP bigMod
          J ell cap A L offset i.val x,
        physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap q rho (2*R) i.val Vbig mu x yc.1 yc.2)) * E := by
    simp_rw [Finset.sum_mul, mul_assoc]
    apply Finset.sum_congr rfl
    intro x hx
    apply congrArg (fun z : ℂ => ratio x * z)
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro yc hyc
    by_cases ht : physicalGBranchTerm SP smallMod BP bigMod (J+ell) cap
        q rho (2*R) i.val Vbig mu x yc.1 yc.2 = 0
    · rw [ht, zero_mul, zero_mul]
    · have hr := memory_frozen_source_actual_G_slice_readout_no_weight SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd ω life hs i
        x (Finset.mem_filter.mp hx).2 yc hyc ht
      rw [memory_frozen_source_actual_E_orbit_sum_without_weight_nonzero SP smallMod BP bigMod J ell m cap patterns
        q rho Vsmall Vbig Knu zeta theta k R hd ω life hs hf i yc.1 hr.1]
  exact hreduce.trans (congrArg (fun z : ℂ => z * E) hG)
end Green64FullPhysicalE

end

end

/-! ## MemoryB2AllENonzero -/

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

set_option maxHeartbeats 700000

/-- Every ORIGINAL source weighted indexed trace with nonzero total
complex weight has NONZERO complete original E scalar at EACH E
visit. This includes Fourier/K/nu/aux/small-Haar cancellations;
no positivity or non-cancellation of the E frame is assumed. -/
theorem memory_source_trace_all_E_nonzero
    (q rho : ℝ) (N : ℕ) (Vsmall : SG → ℝ)
    (Vbig : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ)
    (remaining start : ℕ)
    (y : FullPhysicalOutput SP smallMod BP bigMod (J+ell))
    (seen : Finset ℕ)
    (t : physicalOrientedIndexedTrace SP smallMod BP bigMod
      J ell m cap patterns 1 k remaining start y seen)
    (hw : memorySourceIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig mu Knu
      zeta theta k N remaining start y seen t ≠ 0)
    (j : Fin remaining) :
    let e := physicalOrientedTraceEWitness SP smallMod BP bigMod
      J ell m cap patterns k remaining start y seen t j
    sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m
      cap patterns q rho Vsmall Vbig mu
      (memoryOrientationK BP J ell m patterns
        Knu (physicalAlternatingSign (start+j.val)))
      zeta theta (physicalAlternatingSign (start+j.val)) k e.1 e.2 ≠ 0 := by
  induction remaining generalizing start y seen with
  | zero => exact j.elim0
  | succ n ih =>
    rcases t with ⟨ab,tail⟩
    let yNext := physicalOrientedGEIndexedOutput SP smallMod BP bigMod
      J ell m cap patterns (physicalAlternatingSign start) k ab.val
    let seenNext := physicalOrientedGEIndexedNextSeen SP smallMod BP bigMod
      J ell m cap patterns seen ab.val
    have hpair : physicalOrientedGEIndexedWeight SP smallMod BP bigMod
      J ell m cap patterns q rho N start Vsmall Vbig mu
      (memoryOrientationK BP J ell m patterns
        Knu (physicalAlternatingSign start)) zeta theta
      (physicalAlternatingSign start) k y ab.val ≠ 0 := by
      intro hz
      apply hw
      simp [memorySourceIndexedTraceWeight,hz]
    have htail : memorySourceIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig mu Knu zeta theta k
      N n (start+1) yNext seenNext tail ≠ 0 := by
      intro hz
      apply hw
      change (physicalOrientedGEIndexedWeight SP smallMod BP bigMod
        J ell m cap patterns q rho N start Vsmall Vbig mu
        (memoryOrientationK BP J ell m patterns
          Knu (physicalAlternatingSign start)) zeta theta
        (physicalAlternatingSign start) k y ab.val) *
        (memorySourceIndexedTraceWeight SP smallMod BP bigMod
          J ell m cap patterns q rho Vsmall Vbig mu Knu
          zeta theta k N n (start+1) yNext seenNext tail) = 0
      rw [hz,mul_zero]
    cases j using Fin.cases with
    | zero =>
      change sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig mu
        (memoryOrientationK BP J ell m patterns Knu
          (physicalAlternatingSign start)) zeta theta
        (physicalAlternatingSign start) k ab.val.2.1 ab.val.2.2 ≠ 0
      intro hz
      apply hpair
      simp [physicalOrientedGEIndexedWeight,hz]
    | succ j =>
      change sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
        J ell m cap patterns q rho Vsmall Vbig mu
        (memoryOrientationK BP J ell m patterns Knu
          (physicalAlternatingSign (start + (j.val+1)))) zeta theta
        (physicalAlternatingSign (start + (j.val+1))) k
        (physicalOrientedTraceEWitness SP smallMod BP bigMod
          J ell m cap patterns k n (start+1) yNext seenNext tail j).1
        (physicalOrientedTraceEWitness SP smallMod BP bigMod
          J ell m cap patterns k n (start+1) yNext seenNext tail j).2 ≠ 0
      have hidx : start + (j.val+1) = (start+1) + j.val := by omega
      rw [hidx]
      exact ih (start+1) yNext seenNext tail htail j
end Green64FullPhysicalE

end

end

/-! ## MemoryB2ActualEResidualFactor -/

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

set_option maxHeartbeats 700000

/-- The ORIGINAL physical E coefficient on an actual nonzero-root
witness has precisely the SAME small/Fourier source residual factor
as the frozen edge weight at its actual profile, times the original
BIG E old/store/fresh scalar. This is a per-WITNESS identity, not an
assumption about the summed E orbit or non-cancellation. -/
theorem memory_actual_source_E_scalar_has_frozen_residual
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (H : PhysicalFiniteActualWitnessPath SP smallMod BP bigMod J ell m cap patterns
      q rho Vbig mu k N) (i : Fin N) :
    let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H
    let x := H.beforeE i.val
    let z := H.edge i.val
    let b := z.2.2.1
    let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns z.1) z.2.1 x b.sigmaBig z.2.2.2.1
      (physicalAlternatingSign i.val) k
    sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig mu
      (memoryOrientationK BP J ell m patterns
        Knu (physicalAlternatingSign i.val)) zeta theta
      (physicalAlternatingSign i.val) k x z =
    memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod
      J ell m patterns q Vsmall Vbig Knu zeta theta k ω i *
    (∏ g : BG, orientedBigBranchCoefficient (bigMod g)
      (J+ell) (cap g) (mu g) (Vbig g) rho
      (x.2 g) (b.bigChoice g).1
      (sourceBigShared J ell m (patterns z.1) g)
      (b.sigmaBig g) (b.tauBig g) step (b.bigChoice g).2) := by
  dsimp only
  let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig mu k N H
  let x := H.beforeE i.val
  let z := H.edge i.val
  let b := z.2.2.1
  let D := sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
    (patterns z.1) z.2.1 x b.sigmaBig z.2.2.2.1
  let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap
    (patterns z.1) z.2.1 x b.sigmaBig z.2.2.2.1
    (physicalAlternatingSign i.val) k
  have ha := memory_actual_frozen_edge_allowed SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k N H i
  have hbefore := memory_actual_beforeE_original_coordinates SP smallMod
    BP bigMod J ell m cap patterns q rho Vbig mu k N H i.val i.isLt
  have hD := memory_actual_frozen_D_exact SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k N H i
  have houtput := H.E_output i.val i.isLt
  have hxb : (ω.1 i.castSucc) = x.1 := by
    change (H.before i.val).1 = (H.beforeE i.val).1
    exact hbefore.1.symm
  have hyb : (ω.1 i.succ) = b.smallTarget := by
    change (H.before (i.val+1)).1 =
      (sourceOrientedPhysicalOutput SP smallMod BP bigMod J ell m cap patterns
        (H.beforeE i.val) (physicalAlternatingSign i.val) k (H.edge i.val)).1
    exact congrArg Prod.fst houtput
  have hmarksBefore (g : BG) :
      (ω.2.1 i.castSucc g).val = (x.2 g).1 := by
    change ((H.before i.val).2 g).1 = ((H.beforeE i.val).2 g).1
    exact (hbefore.2 g).symm
  have hmarksAfter (g : BG) :
      (ω.2.1 i.succ g).val = (b.bigChoice g).1 := by
    change ((H.before (i.val+1)).2 g).1 =
      ((H.edge i.val).2.2.1.bigChoice g).1
    exact congrArg (fun yy : FullPhysicalOutput SP smallMod BP bigMod (J+ell) =>
      (yy.2 g).1) houtput
  have hargsBefore :
      (fun g j => (ω.2.1 i.castSucc g).val (b.sigmaBig g j)) =
      (fun g j => (x.2 g).1 (b.sigmaBig g j)) := by
    funext g j
    exact congrFun (hmarksBefore g) (b.sigmaBig g j)
  have hargsAfter :
      (fun g j => (ω.2.1 i.succ g).val (b.tauBig g j)) =
      (fun g j => (b.bigChoice g).1 (b.tauBig g j)) := by
    funext g j
    exact congrFun (hmarksAfter g) (b.tauBig g j)
  have hframe :
      ω.2.2 i = memoryPrimitiveEFrameOf SP smallMod BP bigMod
        J ell m cap patterns x z := by rfl
  unfold sourceOrientedPhysicalCoefficient memoryFrozenSourceResidualEdgeWeight
  rw [if_pos ha]
  rw [hD,hxb,hyb]
  rw [hframe]
  simp only [memoryPrimitiveEFrameOf]
  rw [hargsBefore,hargsAfter]
  unfold sourceOrientedStep
  ring
end Green64FullPhysicalE

end

end

/-! ## MemoryB2RootAllENonzero -/

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

set_option maxHeartbeats 700000

/-- Every contributing ORIGINAL indexed root weight is nonzero at
each genuine source E witness, including its complete SMALL/Fourier
and OLD/permutation scalar. The actual original E witness is derived
from the source root trace (no new E_nonzero postulate). -/
theorem memory_source_root_all_E_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R)
    (j : Fin (2*R)) :
    let E := physicalOrientedTraceEWitness SP smallMod BP bigMod
      J ell m cap patterns k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap w.val.1).toFinset
      w.val.2 j
    sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryOrientationK BP J ell m patterns Knu
        (physicalAlternatingSign j.val))
      zeta theta (physicalAlternatingSign j.val) k E.1 E.2 ≠ 0 := by
  have htrace : memorySourceIndexedTraceWeight SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      Knu zeta theta k (2*R) (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap w.val.1).toFinset
      w.val.2 ≠ 0 := by
    intro hzero
    apply w.property
    simp [memorySourceRootIndexedWeight,hzero]
  have h := memory_source_trace_all_E_nonzero SP smallMod BP bigMod
    J ell m cap patterns q rho (2*R) Vsmall Vbig
    (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    Knu zeta theta k (2*R) 0
    (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
    (physicalInitialBirths SP smallMod BP bigMod J ell cap w.val.1).toFinset
    w.val.2 htrace j
  simpa only [Nat.zero_add] using h
end Green64FullPhysicalE

end

end

/-! ## MemoryB2ActualEAllNonzero -/

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

/-- Source root's ACTUAL H.beforeE/H.edge witness has a complete
nonzero source E physical coefficient at every visit, with its
exact fixed zeta and reversed K, not a symbolic E-frame assumption. -/
theorem memory_source_contributing_actual_E_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R)
    (i : Fin (2*R)) :
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    sourceOrientedPhysicalCoefficient SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
      (memoryOrientationK BP J ell m patterns Knu
        (physicalAlternatingSign i.val))
      zeta theta (physicalAlternatingSign i.val) k
      (H.beforeE i.val) (H.edge i.val) ≠ 0 := by
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  have he := memory_source_root_all_E_nonzero SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R w i
  dsimp only at he ⊢
  have hi : (⟨i.val % (2*R),Nat.mod_lt i.val (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩ : Fin (2*R)) = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  change sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m
    cap patterns q rho Vsmall Vbig
    (physicalSourceMuTilde BP bigMod q (2*R) Vbig)
    (memoryOrientationK BP J ell m patterns Knu
      (physicalAlternatingSign i.val))
    zeta theta (physicalAlternatingSign i.val) k
    (physicalOrientedTraceEWitness SP smallMod BP bigMod J ell m cap patterns
      k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap w.val.1).toFinset
      w.val.2 (⟨i.val % (2*R),Nat.mod_lt i.val (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩)).1
    (physicalOrientedTraceEWitness SP smallMod BP bigMod J ell m cap patterns
      k (2*R) 0
      (physicalFockProjection SP smallMod BP bigMod (J+ell) cap w.val.1)
      (physicalInitialBirths SP smallMod BP bigMod J ell cap w.val.1).toFinset
      w.val.2 (⟨i.val % (2*R),Nat.mod_lt i.val (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩)).2 ≠ 0
  rw [hi]
  exact he
end Green64FullPhysicalE

end

end

/-! ## MemoryB2RootResidualNonzero -/

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

/-- An actual nonzero original root trace has NONZERO frozen residual
E scalar at every ORIGINAL frame/visit, because each actual original
physical E witness weight factors as frozen residual times the TRUE
BIG E old/store/fresh coefficient. No sum or cancellation premise. -/
theorem memory_source_contributing_root_all_frozen_residual_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R)
    (i : Fin (2*R)) :
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H
    memoryFrozenSourceResidualEdgeWeight SP smallMod BP bigMod
      J ell m patterns q Vsmall Vbig Knu zeta theta k ω i ≠ 0 := by
  dsimp only
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k (2*R) H
  have he := memory_source_contributing_actual_E_nonzero SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu zeta theta
    k R hd w i
  have hfactor := memory_actual_source_E_scalar_has_frozen_residual SP smallMod
    BP bigMod J ell m cap patterns q rho Vsmall Vbig mu
    Knu zeta theta k (2*R) H i
  dsimp only at he hfactor
  rw [hfactor] at he
  exact (mul_ne_zero_iff.mp he).1
end Green64FullPhysicalE

end

end

/-! ## MemoryB2RootFrozenWeightNonzero -/

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

/-- The ACTUAL frozen source E-path scalar from ANY contributing
original source root trace is NONZERO, even before selecting a
lifespan. Its literal SMALL/Fourier edge factors are all nonzero
because they are factors of the actual original nonzero E scalars.
No use of an already asserted Memory fibre identity. -/
theorem memory_source_contributing_root_frozen_weight_nonzero
    (q rho : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ)
    (hd : MemorySourceDomain SP smallMod BP bigMod cap q rho Vsmall Vbig k R)
    (w : MemorySourceContributingRootTrace SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R) :
    let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
      J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
    let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod
      J ell m cap patterns q rho Vbig
      (physicalSourceMuTilde BP bigMod q (2*R) Vbig) k (2*R) H
    memoryFrozenSourceWeight SP smallMod BP bigMod
      J ell m patterns q Vsmall Vbig Knu zeta theta k ω ≠ 0 := by
  dsimp only
  let mu := physicalSourceMuTilde BP bigMod q (2*R) Vbig
  let H := memory_source_root_to_actual_witness_path SP smallMod BP bigMod
    J ell m cap patterns q rho Vsmall Vbig Knu zeta theta k R hd.R_pos w
  let ω := memoryActualWitnessFrozenPath SP smallMod BP bigMod
    J ell m cap patterns q rho Vbig mu k (2*R) H
  intro hz
  obtain ⟨i,hi⟩ := memory_source_frozen_weight_zero_has_zero_residual
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig Knu
    zeta theta k R hd ω (fun _ => none) hz
  exact (memory_source_contributing_root_all_frozen_residual_nonzero
    SP smallMod BP bigMod J ell m cap patterns q rho Vsmall Vbig
    Knu zeta theta k R hd w i) hi
end Green64FullPhysicalE

end

end

