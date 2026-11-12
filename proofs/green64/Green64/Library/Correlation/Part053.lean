module

public import Green64.Library.Weights.Part068
public import Green64.Library.Correlation.Part045

@[expose] public section

/-!
# Correlation / Part053

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualSignedCoherentVisitGram -/

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
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Exact complex first-DIRTY visit amplitude on the shared Fock×seen carrier. -/
def sourceOriginalActualSignedPostGhostVisit434
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R T j : ℕ) : ℂ := by
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N Vb
  let w := sourceOriginalActualSignedInitialWeight434
    SP sm BP bm J ell cap hcap Vs mu
  let f := sourceOriginalActualSignedProjectedTerminalG434
    SP sm BP bm J ell cap q rho Vb mu N N
    (fun out _ => physicalVacuum SP sm BP bm J ell out)
  exact ∑ a : H,
    sourceOriginalActualSignedPostGhostPrefix434
      SP sm BP bm J ell m cap patterns
      q rho Vs Vb mu K zeta theta k N T j w a *
    sourceOriginalActualSignedPostGhostDirtySuffix434
      SP sm BP bm J ell m cap patterns
      q rho Vs Vb mu K zeta theta k N T j f a

/-- All visit cross terms remain complex and signed; none are bounded
by their absolute values or discarded as in a positive TV estimate. -/
theorem source_original_FINITE_coherent_visit_gram434
    {I : Type} (s : Finset I) (v : I → ℂ) :
    star (∑ i ∈ s, v i) * (∑ i ∈ s, v i) =
      ∑ i ∈ s, ∑ j ∈ s, star (v i) * v j := by
  rw [star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

/-- Exact Hermitian two-visit Gram for the true physical signed
DIRTY root, retaining every cross-visit and chronological-history
interference term (the original joint K and both OLD masks). -/
theorem source_original_ACTUAL_signed_postghost_DIRTY_coherent_gram434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hVs : ∀ g, 0 < Vs g)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hmu : ∀ g p, 0 < physicalSourceMuTilde BP bm q (2*R) Vb g p) :
    star (sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns
      q rho Vs Vb K zeta theta k R T) *
    sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns
      q rho Vs Vb K zeta theta k R T =
    (star (physicalSourceBaselineProduct BP bm q (2*R) : ℂ) *
      (physicalSourceBaselineProduct BP bm q (2*R) : ℂ)) *
      (∑ i ∈ Finset.range (2*R), ∑ j ∈ Finset.range (2*R),
        star (sourceOriginalActualSignedPostGhostVisit434
          SP sm BP bm J ell m cap patterns hcap
          q rho Vs Vb K zeta theta k R T i) *
        sourceOriginalActualSignedPostGhostVisit434
          SP sm BP bm J ell m cap patterns hcap
          q rho Vs Vb K zeta theta k R T j) := by
  let B : ℂ := (physicalSourceBaselineProduct BP bm q (2*R) : ℂ)
  let visit : ℕ → ℂ := fun j =>
    sourceOriginalActualSignedPostGhostVisit434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs Vb K zeta theta k R T j
  let root : ℂ := sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
    SP sm BP bm J ell m cap patterns
    q rho Vs Vb K zeta theta k R T
  have hRoot : root = B * ∑ j ∈ Finset.range (2*R), visit j := by
    simpa only [root, B, visit,
      sourceOriginalActualSignedPostGhostVisit434] using
      (source_original_ACTUAL_signed_physical_root_post_G_pair434
        SP sm BP bm J ell m cap patterns hi hcap
        q rho Vs Vb K zeta theta k R T hVs hmu)
  change star root * root = (star B * B) *
    (∑ i ∈ Finset.range (2*R), ∑ j ∈ Finset.range (2*R),
      star (visit i) * visit j)
  rw [hRoot, star_mul]
  calc
    (star (∑ j ∈ Finset.range (2*R), visit j) * star B) *
        (B * ∑ j ∈ Finset.range (2*R), visit j) =
      (star B * B) *
        (star (∑ j ∈ Finset.range (2*R), visit j) *
          ∑ j ∈ Finset.range (2*R), visit j) := by ring
    _ = _ := by rw [source_original_FINITE_coherent_visit_gram434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedTrueDensity -/

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
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- ORIGINAL physical Hilbert density on the actual reachable joint
Fock×cumulative-seen state. We use the exact physical orbit mass and
the genuine OLD sector-density factor, without renormalizing. -/
def sourceOriginalActualSignedTrueFockDensity434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : H) : ℝ :=
  physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu a.val.1 *
    sourceOriginalMemorySectorDensity434 SP sm BP bm J ell Vb a.val.1

/-- Strict positivity of the ACTUAL Fock/OLD mass at every reachable
Fock×seen state. The orbit-support membership is part of this state's
original finite carrier; no assumed positivity of a new density. -/
theorem source_original_ACTUAL_signed_true_fock_density_pos434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hmu : ∀ g p, 0 < mu g p) (a : H) :
    0 < sourceOriginalActualSignedTrueFockDensity434
      SP sm BP bm J ell cap Vs Vb mu a := by
  have ha := (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP bm J ell cap a.val.1 a.val.2).mp a.property
  unfold sourceOriginalActualSignedTrueFockDensity434
  exact mul_pos
    (physicalOrbitMass_pos SP sm BP bm (J+ell) cap
      Vs mu hVs hmu a.val.1 ha.1)
    (source_original_memory_sector_density_pos434
      SP sm BP bm J ell Vb hVb a.val.1)

/-- Exact weighted dual (inverse-density) energy of an original
complex CLEAN prefix on the SINGLE joint reachable Fock×seen carrier. -/
def sourceOriginalActualSignedTruePrefixEnergy434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (w : H → ℂ) : ℝ :=
  sourceOriginalSignedJointInverseEnergy434
    (sourceOriginalActualSignedTrueFockDensity434
      SP sm BP bm J ell cap Vs Vb mu) w

/-- The target energy uses the SAME actual Fock/OLD density, rather
than replacing the true cumulative seen with an independent sample. -/
def sourceOriginalActualSignedTrueTargetEnergy434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (f : H → ℂ) : ℝ :=
  sourceOriginalSignedJointForwardEnergy434
    (sourceOriginalActualSignedTrueFockDensity434
      SP sm BP bm J ell cap Vs Vb mu) f

/-- Genuine physical Fock/sector weighted complex-bilinear CS on the
reachable Fock×seen carrier. NO history-cardinality factor occurs. -/
theorem source_original_ACTUAL_signed_true_fock_pair_CS434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hmu : ∀ g p, 0 < mu g p) (w f : H → ℂ) :
    ‖∑ a : H, w a * f a‖ ≤
    Real.sqrt (sourceOriginalActualSignedTruePrefixEnergy434
      SP sm BP bm J ell cap Vs Vb mu w) *
    Real.sqrt (sourceOriginalActualSignedTrueTargetEnergy434
      SP sm BP bm J ell cap Vs Vb mu f) := by
  exact source_original_SIGNED_joint_weighted_CS434
    (sourceOriginalActualSignedTrueFockDensity434
      SP sm BP bm J ell cap Vs Vb mu)
    (source_original_ACTUAL_signed_true_fock_density_pos434
      SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu) w f
end Green64Analytic.CorrelationSquare

end

end

