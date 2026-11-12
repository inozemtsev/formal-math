module

public import Green64.Library.Weights.Part069
public import Green64.Library.Weights.Part068
public import Green64.Library.Correlation.Part053
public import Green64.Library.Correlation.Part048
public import Green64.Library.Weights.Part067
public import Green64.Library.Correlation.Part049
public import Green64.Library.Weights.ActualInitialVacuumFactor
public import Green64.Library.Weights.Part065
public import Green64.Library.Analysis.Estimates.Part013
public import Green64.Library.Correlation.Part050
public import Green64.Library.Correlation.Part052
public import Green64.Library.Correlation.Part046

@[expose] public section

/-!
# Weights / Part070

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualSignedDIRTYEnergySquare -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- No visit-count or history-cardinality factor: the SQUARED norm
of the TRUE signed insertion sum is bounded by the product of the
two exact time-aggregated weighted energies. -/
theorem source_original_SIGNED_DIRTY_pairing_energy_squared434
    {H : Type} [Fintype H]
    (C D : ℕ → H → H → ℂ) (π : H → ℝ)
    (hπ : ∀ a, 0 < π a) (n start : ℕ) (w f : H → ℂ) :
    ‖∑ j ∈ Finset.range n, ∑ b : H,
      sourceOriginalSignedForwardPrefix434 C j start w b *
      sourceOriginalSignedMatrixAction434 (D (start+j))
        (sourceOriginalSignedMatrixChain434
          (sourceOriginalSignedKernelAdd434 C D)
          (n-(j+1)) (start+j+1) f) b‖^2 ≤
    sourceOriginalSignedPrefixEnergySum434 C π n start w *
      sourceOriginalSignedDIRTYTargetEnergySum434 C D π n start f := by
  classical
  let P := sourceOriginalSignedPrefixEnergySum434 C π n start w
  let Dsum := sourceOriginalSignedDIRTYTargetEnergySum434 C D π n start f
  have hP : 0 ≤ P := by
    unfold P sourceOriginalSignedPrefixEnergySum434
    exact Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hD : 0 ≤ Dsum := by
    unfold Dsum sourceOriginalSignedDIRTYTargetEnergySum434
    exact Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hCS := source_original_SIGNED_DIRTY_pairing_energy_CS434
    C D π hπ n start w f
  calc
    _ ≤ (Real.sqrt P * Real.sqrt Dsum)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hCS 2
    _ = P * Dsum := by
      rw [mul_pow,Real.sq_sqrt hP,Real.sq_sqrt hD]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPhysicalDIRTYEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The two TRUE ORIGINAL sign-sensitive energy budgets:
time-aggregated inverse-Fock/OLD CLEAN prefix density and
time-aggregated direct-Fock/OLD DIRTY output density.
Each index retains the SAME cumulative numerical seen history. -/
def sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℝ × ℝ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N Vb
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs Vb mu K zeta theta k N T
  let Dirty := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs Vb mu K zeta theta k N T
  let w := sourceOriginalActualSignedInitialWeight434
    SP sm BP bm J ell cap hcap Vs mu
  let f := sourceOriginalActualSignedProjectedTerminalG434
    SP sm BP bm J ell cap q rho Vb mu N N
    (fun out _ => physicalVacuum SP sm BP bm J ell out)
  let π := sourceOriginalActualSignedTrueFockDensity434
    SP sm BP bm J ell cap Vs Vb mu
  (sourceOriginalSignedPrefixEnergySum434 Clean π N 0 w,
   sourceOriginalSignedDIRTYTargetEnergySum434 Clean Dirty π N 0 f)

/-- Quantitative physical first-DIRTY norm control with exactly
aggregated true signed CLEAN-prefix and DIRTY-suffix energies.
The ONLY factor besides those energies is the ORIGINAL baseline.
No power of N or |Hist| is inserted. -/
theorem source_original_ACTUAL_PHYSICAL_signed_DIRTY_root_energy434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hmu : ∀ g p, 0 < physicalSourceMuTilde BP bm q (2*R) Vb g p) :
    ‖sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns q rho Vs Vb K zeta theta k R T‖^2 ≤
    ‖(physicalSourceBaselineProduct BP bm q (2*R) : ℂ)‖^2 *
    (sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs Vb K zeta theta k R T).1 *
    (sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs Vb K zeta theta k R T).2 := by
  classical
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N Vb
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs Vb mu K zeta theta k N T
  let Dirty := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs Vb mu K zeta theta k N T
  let w := sourceOriginalActualSignedInitialWeight434
    SP sm BP bm J ell cap hcap Vs mu
  let f := sourceOriginalActualSignedProjectedTerminalG434
    SP sm BP bm J ell cap q rho Vb mu N N
    (fun out _ => physicalVacuum SP sm BP bm J ell out)
  let π := sourceOriginalActualSignedTrueFockDensity434
    SP sm BP bm J ell cap Vs Vb mu
  have hπ (a : H) : 0 < π a :=
    source_original_ACTUAL_signed_true_fock_density_pos434
      SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu a
  have hCS := source_original_SIGNED_DIRTY_pairing_energy_squared434
    Clean Dirty π hπ N 0 w f
  have hRoot := source_original_ACTUAL_PHYSICAL_signed_DIRTY_root_prefix_suffix434
    SP sm BP bm J ell m cap patterns hi hcap
    q rho Vs Vb K zeta theta k R T hVs hmu
  change sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
    SP sm BP bm J ell m cap patterns q rho Vs Vb K zeta theta k R T =
    (physicalSourceBaselineProduct BP bm q N : ℂ) *
      (∑ j ∈ Finset.range N, ∑ a : H,
        sourceOriginalSignedForwardPrefix434 Clean j 0 w a *
        sourceOriginalSignedMatrixAction434 (Dirty j)
          (sourceOriginalSignedMatrixChain434
            (sourceOriginalSignedKernelAdd434 Clean Dirty)
            (N-(j+1)) (j+1) f) a) at hRoot
  let base : ℂ := (physicalSourceBaselineProduct BP bm q N : ℂ)
  change ‖sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns
      q rho Vs Vb K zeta theta k R T‖^2 ≤
    ‖base‖^2 * sourceOriginalSignedPrefixEnergySum434 Clean π N 0 w *
      sourceOriginalSignedDIRTYTargetEnergySum434 Clean Dirty π N 0 f
  rw [hRoot,norm_mul,mul_pow]
  simp only [Nat.zero_add] at hCS
  calc
    _ ≤ ‖base‖^2 *
        (sourceOriginalSignedPrefixEnergySum434 Clean π N 0 w *
        sourceOriginalSignedDIRTYTargetEnergySum434 Clean Dirty π N 0 f) :=
      mul_le_mul_of_nonneg_left hCS (sq_nonneg ‖base‖)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPhysicalDIRTYEnergyNorm -/

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
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The genuine signed physical insertion root norm bounded by the
baseline times two ACTUAL time-aggregated Fock/OLD energies. -/
theorem source_original_ACTUAL_PHYSICAL_signed_DIRTY_root_energy_norm434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hmu : ∀ g p, 0 < physicalSourceMuTilde BP bm q (2*R) Vb g p) :
    ‖sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns q rho Vs Vb K zeta theta k R T‖ ≤
    ‖(physicalSourceBaselineProduct BP bm q (2*R) : ℂ)‖ *
    Real.sqrt ((sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs Vb K zeta theta k R T).1) *
    Real.sqrt ((sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs Vb K zeta theta k R T).2) := by
  classical
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N Vb
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs Vb mu K zeta theta k N T
  let Dirty := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs Vb mu K zeta theta k N T
  let w := sourceOriginalActualSignedInitialWeight434
    SP sm BP bm J ell cap hcap Vs mu
  let f := sourceOriginalActualSignedProjectedTerminalG434
    SP sm BP bm J ell cap q rho Vb mu N N
    (fun out _ => physicalVacuum SP sm BP bm J ell out)
  let π := sourceOriginalActualSignedTrueFockDensity434
    SP sm BP bm J ell cap Vs Vb mu
  have hπ (a : H) : 0 < π a :=
    source_original_ACTUAL_signed_true_fock_density_pos434
      SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu a
  have hCS := source_original_SIGNED_DIRTY_pairing_energy_CS434
    Clean Dirty π hπ N 0 w f
  have hRoot := source_original_ACTUAL_PHYSICAL_signed_DIRTY_root_prefix_suffix434
    SP sm BP bm J ell m cap patterns hi hcap
    q rho Vs Vb K zeta theta k R T hVs hmu
  change sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
    SP sm BP bm J ell m cap patterns q rho Vs Vb K zeta theta k R T =
    (physicalSourceBaselineProduct BP bm q N : ℂ) *
      (∑ j ∈ Finset.range N, ∑ a : H,
        sourceOriginalSignedForwardPrefix434 Clean j 0 w a *
        sourceOriginalSignedMatrixAction434 (Dirty j)
          (sourceOriginalSignedMatrixChain434
            (sourceOriginalSignedKernelAdd434 Clean Dirty)
            (N-(j+1)) (j+1) f) a) at hRoot
  let base : ℂ := (physicalSourceBaselineProduct BP bm q N : ℂ)
  change ‖sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns
      q rho Vs Vb K zeta theta k R T‖ ≤
    ‖base‖ * Real.sqrt (sourceOriginalSignedPrefixEnergySum434 Clean π N 0 w) *
      Real.sqrt (sourceOriginalSignedDIRTYTargetEnergySum434 Clean Dirty π N 0 f)
  rw [hRoot,norm_mul]
  simp only [Nat.zero_add] at hCS
  calc
    _ ≤ ‖base‖ * (Real.sqrt (sourceOriginalSignedPrefixEnergySum434 Clean π N 0 w) *
      Real.sqrt (sourceOriginalSignedDIRTYTargetEnergySum434 Clean Dirty π N 0 f)) :=
        mul_le_mul_of_nonneg_left hCS (norm_nonneg base)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedHistoryEnergyFibre -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Exact finite disintegration of a genuine product-state carrier
with a reachable filter. The mask is at the SINGLE pair (output, seen);
neither the history nor the output is resampled or maximised. -/
theorem source_original_ACTUAL_finite_history_filter_sum434
    {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (S : Finset X) (T : Finset Y) (eligible : X → Y → Prop)
    [DecidablePred (fun z : X × Y => eligible z.1 z.2)]
    (W : X → Y → ℝ) :
    (∑ z : {z : X × Y //
       z ∈ (S.product T).filter (fun z => eligible z.1 z.2)},
       W z.val.1 z.val.2) =
    ∑ x ∈ S, ∑ y ∈ T,
      if eligible x y then W x y else 0 := by
  classical
  calc
    _ = ∑ z ∈ (S.product T).filter (fun z => eligible z.1 z.2),
        W z.1 z.2 := by
      exact Finset.sum_coe_sort
        ((S.product T).filter (fun z => eligible z.1 z.2))
        (fun z : X × Y => W z.1 z.2)
    _ = ∑ z ∈ S.product T,
        (if eligible z.1 z.2 then W z.1 z.2 else 0) := by
      rw [Finset.sum_filter]
    _ = _ := by
      calc
        _ = ∑ x ∈ S, ∑ y ∈ T,
            (if eligible (x,y).1 (x,y).2
              then W (x,y).1 (x,y).2 else 0) :=
          Finset.sum_product S T
            (fun z : X × Y => if eligible z.1 z.2 then W z.1 z.2 else 0)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hxy : eligible x y <;> simp [hxy]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedHistoryEnergyDisintegration -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- True weighted physical Fock×seen sector energy, with the
REACHABLE test retained at each output and each chronological
history. No summation over impossible histories is hidden. -/
def sourceOriginalActualPhysicalHistoryFibreEnergy434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) : ℝ :=
  ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
    ∑ seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
      if sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen then
        (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y *
          sourceOriginalMemorySectorDensity434 SP sm BP bm J ell Vb y) *
          ‖F y seen‖^2
      else 0

/-- EXACT original direct-density signed Hilbert norm on the finite
joint Fock×seen carrier, disintegrated over the genuine Fock orbit
and its ACTUAL reachable chronological histories. There is no
multiplicative cardinality and no arbitrary history supremum. -/
theorem source_original_ACTUAL_PHYSICAL_history_energy_disintegration434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g)
    (hmu : ∀ g p,0 < mu g p)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434
        SP sm BP bm J ell cap Vs Vb mu)
      (fun a : H => F a.val.1 a.val.2) =
    sourceOriginalActualPhysicalHistoryFibreEnergy434
      SP sm BP bm J ell cap Vs Vb mu F := by
  classical
  let π := sourceOriginalActualSignedTrueFockDensity434
    SP sm BP bm J ell cap Vs Vb mu
  have hπ (a : H) : 0 ≤ π a :=
    (source_original_ACTUAL_signed_true_fock_density_pos434
      SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu a).le
  rw [source_original_SIGNED_forward_energy_as_sum434 π hπ]
  let S := physicalFockOrbitSupport SP sm BP bm (J+ell) cap
  let T := (sourceOriginalMemoryBirthPool434 BP bm).powerset
  let P : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → Prop :=
    fun y seen => sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen
  let W : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ :=
    fun y seen =>
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y *
        sourceOriginalMemorySectorDensity434 SP sm BP bm J ell Vb y) *
      ‖F y seen‖^2
  change (∑ a : H, W a.val.1 a.val.2) =
    ∑ y ∈ S, ∑ seen ∈ T, if P y seen then W y seen else 0
  calc
    _ = ∑ z ∈ sourceOriginalActualSignedHistoryCarrierFinset434
        SP sm BP bm J ell cap, W z.1 z.2 := by
          exact Finset.sum_coe_sort
            (sourceOriginalActualSignedHistoryCarrierFinset434 SP sm BP bm J ell cap)
            (fun z => W z.1 z.2)
    _ = _ := by
      have h := source_original_ACTUAL_finite_history_filter_sum434 S T P W
      have hh := (Finset.sum_coe_sort
        ((S.product T).filter (fun z => P z.1 z.2))
        (fun z : FullPhysicalOutput SP sm BP bm (J+ell) × Finset ℕ =>
          W z.1 z.2)).symm
      exact hh.trans h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDIRTYMatrixToMarked -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- THE actual two-OLD-masked E_DIRTY matrix on a TRUE cumulative
Fock×seen input has exactly the original full physical
marked-operator value, not a new comparison selector or averaged
history. The input seen and all subsequent choices are unchanged. -/
theorem source_original_ACTUAL_DIRTY_matrix_marked_pointwise434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (a : H) :
    (∑ b : H, sourceOriginalActualSignedOLDMaskedEMatrix434
      SP sm BP bm J ell m cap patterns
      (fun x z => ¬ sourceOriginalCleanChoice434
        SP sm BP bm J ell m cap patterns x z)
      q rho Vs Vb mu K zeta theta o k T a b *
      F b.val.1 b.val.2) =
    sourceOriginalMemoryMarkedProjectedDirty434
      SP sm BP bm J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k T F a.val.1 a.val.2 := by
  classical
  have hr := (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP bm J ell cap a.val.1 a.val.2).mp a.property
  have hE := source_original_ACTUAL_signed_OLD_masked_E_physical_exact434
    SP sm BP bm J ell m cap patterns hcap
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs Vb mu K zeta theta o k T F a
  have hD := source_original_ACTUAL_FRAME_DIRTY_projected_exact434
    SP sm BP bm J ell m cap patterns hcap
    q rho Vs Vb mu hVs hmu K zeta theta o k T F
    a.val.1 a.val.2 hr.2.2
  have hF :
      (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then
        F out st else (0:ℂ)) =
      (fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ T)
        (Classical.propDecidable _) (F out st) 0) := by
    funext out st
    by_cases ht : (∑ g : BG,(out.2 g).2.card) ≤ T <;> simp [ht]
  have hGate :
      (if sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T a then
        sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
          (fun x z => ¬ sourceOriginalCleanChoice434
            SP sm BP bm J ell m cap patterns x z)
          q rho Vs Vb mu K zeta theta o k
          (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1)
          a.val.2
          (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then
             F out st else 0)
       else 0) =
      (if (∑ g : BG,(a.val.1.2 g).2.card) ≤ T then
        sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
          q rho Vs Vb mu K zeta theta o k
          (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1)
          a.val.2
          (fun out st => @ite ℂ ((∑ g : BG,(out.2 g).2.card) ≤ T)
            (Classical.propDecidable _) (F out st) 0)
       else 0) := by
    by_cases ht : (∑ g : BG,(a.val.1.2 g).2.card) ≤ T
    · simp [sourceOriginalActualSignedOLDGate434,
        sourceOriginalSourceEFrameDirtyRow434,ht,hF]
    · simp [sourceOriginalActualSignedOLDGate434,
        sourceOriginalSourceEFrameDirtyRow434,ht]
  exact (hE.symm.trans hGate).trans hD
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDIRTYJointHilbertBridge -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Zero-extending a TRUE finite reachable joint Fock×seen test to
the actual birth pool preserves its exact physical marked energy.
There is no count of impossible histories or Fock states. -/
theorem source_original_ACTUAL_signed_DIRTY_lift_joint_energy_exact434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hmu : ∀ g p, 0 < mu g p) (f : H → ℂ) :
    sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu
      (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f) =
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434
        SP sm BP bm J ell cap Vs Vb mu) f := by
  classical
  let F := sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f
  have hz (y : FullPhysicalOutput SP sm BP bm (J+ell))
      (seen : Finset ℕ)
      (hr : ¬ sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
      F y seen = 0 := by
    have hn : (y,seen) ∉ sourceOriginalActualSignedHistoryCarrierFinset434
        SP sm BP bm J ell cap := by
      intro h
      exact hr ((source_original_ACTUAL_signed_history_mem_iff434
        SP sm BP bm J ell cap y seen).mp h).2.2
    exact dif_neg hn
  have heq :
      sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu F =
      sourceOriginalActualPhysicalHistoryFibreEnergy434
        SP sm BP bm J ell cap Vs Vb mu F := by
    unfold sourceOriginalMemoryMarkedEnergy434
      sourceOriginalActualPhysicalHistoryFibreEnergy434
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro seen hs
    by_cases hr : sourceOriginalPhysicalReachable434
      SP sm BP bm (J+ell) y seen
    · simp only [if_pos hr]
    · simp only [if_neg hr]
      rw [hz y seen hr]
      simp
  have hv (a : H) : F a.val.1 a.val.2 = f a := by
    exact source_original_ACTUAL_signed_history_lift_valid434
      SP sm BP bm J ell cap f a.val.1 a.val.2 a.property
  calc
    _ = sourceOriginalActualPhysicalHistoryFibreEnergy434
        SP sm BP bm J ell cap Vs Vb mu F := heq
    _ = sourceOriginalSignedJointForwardEnergy434
        (sourceOriginalActualSignedTrueFockDensity434
          SP sm BP bm J ell cap Vs Vb mu)
        (fun a : H => F a.val.1 a.val.2) := by
      exact (source_original_ACTUAL_PHYSICAL_history_energy_disintegration434
        SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu F).symm
    _ = _ := by
      congr 1
      funext a
      exact hv a

/-- The reachable physical H-energy is bounded by the FULL marked
Fock×seen energy without any history or orbit cardinality factor. -/
theorem source_original_ACTUAL_signed_DIRTY_reachable_le_joint_energy434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hmu : ∀ g p, 0 < mu g p)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434
        SP sm BP bm J ell cap Vs Vb mu)
      (fun a : H => F a.val.1 a.val.2) ≤
    sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu F := by
  rw [source_original_ACTUAL_PHYSICAL_history_energy_disintegration434
    SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu F]
  unfold sourceOriginalActualPhysicalHistoryFibreEnergy434
    sourceOriginalMemoryMarkedEnergy434
  apply Finset.sum_le_sum
  intro y hy
  apply Finset.sum_le_sum
  intro seen hs
  by_cases hr : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen
  · simp only [if_pos hr, le_refl]
  · simp only [if_neg hr]
    exact mul_nonneg
      (source_original_memory_FULL_density_orbit_nonneg434
        SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu y)
      (sq_nonneg _)

/-- The EXACT OLD-masked finite signed DIRTY E matrix on the TRUE
reachable H inherits a verified full marked physical joint L²
saving, with NO |H|/|seen| loss. This is the literal source E
and exact original Fock×seen density. -/
theorem source_original_ACTUAL_signed_DIRTY_finite_H_energy434
    (m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern BG J m)
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hmu : ∀ g p, 0 < mu g p)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (T : ℕ)
    (C : ℝ) (f : H → ℂ)
    (hMarked :
      sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu
        (sourceOriginalMemoryMarkedProjectedDirty434
          SP sm BP bm J ell m cap patterns
          q rho Vs Vb mu K zeta theta o k T
          (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f)) ≤
      C * sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu
        (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f)) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu)
      (fun a : H => ∑ b : H,
        sourceOriginalActualSignedOLDMaskedEMatrix434
          SP sm BP bm J ell m cap patterns
          (fun x z => ¬ sourceOriginalCleanChoice434
            SP sm BP bm J ell m cap patterns x z)
          q rho Vs Vb mu K zeta theta o k T a b * f b) ≤
    C * sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu)
      f := by
  classical
  let F := sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f
  let D := sourceOriginalMemoryMarkedProjectedDirty434
    SP sm BP bm J ell m cap patterns q rho Vs Vb mu K zeta theta o k T F
  have hp (a : H) :
      (∑ b : H, sourceOriginalActualSignedOLDMaskedEMatrix434
        SP sm BP bm J ell m cap patterns
        (fun x z => ¬ sourceOriginalCleanChoice434
          SP sm BP bm J ell m cap patterns x z)
        q rho Vs Vb mu K zeta theta o k T a b * f b) =
      D a.val.1 a.val.2 := by
    calc
      _ = ∑ b : H, sourceOriginalActualSignedOLDMaskedEMatrix434
          SP sm BP bm J ell m cap patterns
          (fun x z => ¬ sourceOriginalCleanChoice434
            SP sm BP bm J ell m cap patterns x z)
          q rho Vs Vb mu K zeta theta o k T a b * F b.val.1 b.val.2 := by
        apply Finset.sum_congr rfl
        intro b hb
        have hv : F b.val.1 b.val.2 = f b := by
          exact source_original_ACTUAL_signed_history_lift_valid434
            SP sm BP bm J ell cap f b.val.1 b.val.2 b.property
        exact congrArg (fun z : ℂ =>
          sourceOriginalActualSignedOLDMaskedEMatrix434 SP sm BP bm
            J ell m cap patterns
            (fun x z => ¬ sourceOriginalCleanChoice434
              SP sm BP bm J ell m cap patterns x z)
            q rho Vs Vb mu K zeta theta o k T a b * z) hv.symm
      _ = D a.val.1 a.val.2 := by
        exact source_original_ACTUAL_DIRTY_matrix_marked_pointwise434
          SP sm BP bm J ell m cap patterns hcap
          q rho Vs Vb mu hVs hmu K zeta theta o k T F a
  calc
    _ = sourceOriginalSignedJointForwardEnergy434
        (sourceOriginalActualSignedTrueFockDensity434
          SP sm BP bm J ell cap Vs Vb mu)
        (fun a : H => D a.val.1 a.val.2) := by
      congr 1
      funext a
      exact hp a
    _ ≤ sourceOriginalMemoryMarkedEnergy434
        SP sm BP bm J ell cap Vs Vb mu D :=
      source_original_ACTUAL_signed_DIRTY_reachable_le_joint_energy434
        SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu D
    _ ≤ C * sourceOriginalMemoryMarkedEnergy434
        SP sm BP bm J ell cap Vs Vb mu F := hMarked
    _ = _ := by
      rw [source_original_ACTUAL_signed_DIRTY_lift_joint_energy_exact434
        SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu f]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDIRTYMatrixEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 26000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Genuine E_DIRTY matrix target energy is EXACTLY the original
physically weighted marked DIRTY energy restricted to reachable
Fock×chronological-seen states. The same old-sector Fock density
and the same true global history pool appear on both sides.
No history supremum, baseline change or positive E surrogate. -/
theorem source_original_ACTUAL_DIRTY_matrix_energy_reachable_exact434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g)
    (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434
        SP sm BP bm J ell cap Vs Vb mu)
      (sourceOriginalActualSignedOLDMaskedFiniteE434
        SP sm BP bm J ell m cap patterns
        (fun x z => ¬ sourceOriginalCleanChoice434
          SP sm BP bm J ell m cap patterns x z)
        q rho Vs Vb mu K zeta theta o k T
        (sourceOriginalActualSignedHistoryRestrict434
          SP sm BP bm J ell cap F)) =
    sourceOriginalActualPhysicalHistoryFibreEnergy434
      SP sm BP bm J ell cap Vs Vb mu
      (sourceOriginalMemoryMarkedProjectedDirty434
        SP sm BP bm J ell m cap patterns
        q rho Vs Vb mu K zeta theta o k T F) := by
  classical
  let E := sourceOriginalActualSignedOLDMaskedEMatrix434
    SP sm BP bm J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP sm BP bm J ell m cap patterns x z)
    q rho Vs Vb mu K zeta theta o k T
  let D := sourceOriginalMemoryMarkedProjectedDirty434
    SP sm BP bm J ell m cap patterns q rho Vs Vb mu K zeta theta o k T F
  have hE (a : H) :
      sourceOriginalActualSignedOLDMaskedFiniteE434
        SP sm BP bm J ell m cap patterns
        (fun x z => ¬ sourceOriginalCleanChoice434
          SP sm BP bm J ell m cap patterns x z)
        q rho Vs Vb mu K zeta theta o k T
        (sourceOriginalActualSignedHistoryRestrict434
          SP sm BP bm J ell cap F) a =
      D a.val.1 a.val.2 := by
    rw [source_original_ACTUAL_signed_OLD_masked_E_matrix_exact434]
    change (∑ b : H,E a b * F b.val.1 b.val.2) = _
    exact source_original_ACTUAL_DIRTY_matrix_marked_pointwise434
      SP sm BP bm J ell m cap patterns
      hcap q rho Vs Vb mu hVs hmu K zeta theta o k T F a
  have hh :
      sourceOriginalActualSignedOLDMaskedFiniteE434
        SP sm BP bm J ell m cap patterns
        (fun x z => ¬ sourceOriginalCleanChoice434
          SP sm BP bm J ell m cap patterns x z)
        q rho Vs Vb mu K zeta theta o k T
        (sourceOriginalActualSignedHistoryRestrict434
          SP sm BP bm J ell cap F) =
        (fun a : H => D a.val.1 a.val.2) := by
    funext a
    exact hE a
  rw [hh]
  exact source_original_ACTUAL_PHYSICAL_history_energy_disintegration434
    SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu D
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDIRTYMatrixEnergyBound -/

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

/-- The FULL history-indexed actual E_DIRTY matrix L² energy is
bounded without a history-cardinality factor by the ORIGINAL
marked-energy norm integrated over ALL physical Fock outputs
and admissible seen histories, with the same physical density.
This is not yet the selector energy with ONE seen per output. -/
theorem source_original_ACTUAL_DIRTY_matrix_energy_le_marked434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g)
    (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434
        SP sm BP bm J ell cap Vs Vb mu)
      (sourceOriginalActualSignedOLDMaskedFiniteE434
        SP sm BP bm J ell m cap patterns
        (fun x z => ¬ sourceOriginalCleanChoice434
          SP sm BP bm J ell m cap patterns x z)
        q rho Vs Vb mu K zeta theta o k T
        (sourceOriginalActualSignedHistoryRestrict434
          SP sm BP bm J ell cap F)) ≤
    sourceOriginalMemoryMarkedEnergy434
      SP sm BP bm J ell cap Vs Vb mu
      (sourceOriginalMemoryMarkedProjectedDirty434
        SP sm BP bm J ell m cap patterns
        q rho Vs Vb mu K zeta theta o k T F) := by
  classical
  have hEq := source_original_ACTUAL_DIRTY_matrix_energy_reachable_exact434
    SP sm BP bm J ell m cap patterns
    hcap q rho Vs Vb mu hVs hVb hmu K zeta theta o k T F
  rw [hEq]
  unfold sourceOriginalActualPhysicalHistoryFibreEnergy434
    sourceOriginalMemoryMarkedEnergy434
  apply Finset.sum_le_sum
  intro y hy
  apply Finset.sum_le_sum
  intro seen hs
  by_cases hr : sourceOriginalPhysicalReachable434
      SP sm BP bm (J+ell) y seen
  · simp only [if_pos hr,le_refl]
  · simp only [if_neg hr]
    exact mul_nonneg
      (source_original_memory_FULL_density_orbit_nonneg434
        SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu y)
      (sq_nonneg _)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualMarkedEnergySelectorSlices -/

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
variable (J ell : ℕ) (cap : BG → ℕ)

/-- Exact disintegration of the genuine original fully marked E
energy into selector L² energies at each ACTUAL numerical history.
No fictitious distribution on histories: this is a literal finite
identity with one selector energy for each allowed seen set. -/
theorem source_original_ACTUAL_marked_energy_selector_slices434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu F =
    ∑ seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
      sourceOriginalMemorySelectorEnergy434 SP sm BP bm J ell cap Vs Vb mu
        (fun y => F y seen) := by
  classical
  unfold sourceOriginalMemoryMarkedEnergy434
    sourceOriginalMemorySelectorEnergy434
  rw [Finset.sum_comm]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDIRTYSelectorSlices -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 15000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The genuine history-indexed original E_DIRTY matrix's L²
energy is bounded by the literal SUM of the original physical
marked-DIRTY selector energies, one per possible seen history.
This is the exact local-to-global interface and it makes the
otherwise hidden history-occupation challenge explicit. -/
theorem source_original_ACTUAL_DIRTY_matrix_energy_le_selector_slices434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g)
    (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434
        SP sm BP bm J ell cap Vs Vb mu)
      (sourceOriginalActualSignedOLDMaskedFiniteE434
        SP sm BP bm J ell m cap patterns
        (fun x z => ¬ sourceOriginalCleanChoice434
          SP sm BP bm J ell m cap patterns x z)
        q rho Vs Vb mu K zeta theta o k T
        (sourceOriginalActualSignedHistoryRestrict434
          SP sm BP bm J ell cap F)) ≤
    ∑ seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
      sourceOriginalMemorySelectorEnergy434
        SP sm BP bm J ell cap Vs Vb mu
        (fun y => sourceOriginalMemoryMarkedProjectedDirty434
          SP sm BP bm J ell m cap patterns
          q rho Vs Vb mu K zeta theta o k T F y seen) := by
  have hBound := source_original_ACTUAL_DIRTY_matrix_energy_le_marked434
    SP sm BP bm J ell m cap patterns
    hcap q rho Vs Vb mu hVs hVb hmu K zeta theta o k T F
  have hSlices := source_original_ACTUAL_marked_energy_selector_slices434
    SP sm BP bm J ell cap Vs Vb mu
    (sourceOriginalMemoryMarkedProjectedDirty434
      SP sm BP bm J ell m cap patterns
      q rho Vs Vb mu K zeta theta o k T F)
  exact hBound.trans_eq hSlices
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualHistoryProbabilitySelectors -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- A finite family of genuine chronological histories with
state-dependent nonnegative occupation weights of TOTAL MASS <= 1
per physical output. This is the appropriate normalized object for
integrating LOCAL L2 selectors, rather than counting all histories.
No claim that an original signed CLEAN prefix creates such a
subprobability law is made. -/
def sourceOriginalHistorySubprobability434 {X S : Type}
    (carrier : Finset X) (histories : Finset S)
    (alpha : X → S → ℝ) : Prop :=
  (∀ x ∈ carrier, ∀ s ∈ histories, 0 ≤ alpha x s) ∧
  (∀ x ∈ carrier, (∑ s ∈ histories, alpha x s) ≤ 1)

/-- State-dependent weighted average over histories is paid by ONE
pointwise maximizing selector: no cardinality of possible histories
appears. Maximization is performed across each physical output
without resetting any history in an actual evolution. -/
theorem source_original_HISTORY_subprobability_selector_bound434
    {X S : Type} (carrier : Finset X) (histories : Finset S)
    (hs : histories.Nonempty)
    (mass : X → ℝ) (hmass : ∀ x ∈ carrier, 0 ≤ mass x)
    (alpha : X → S → ℝ)
    (hSub : sourceOriginalHistorySubprobability434 carrier histories alpha)
    (F : X → S → ℂ) (C : ℝ)
    (hSelector : ∀ sigma : X → S,
      (∀ x ∈ carrier, sigma x ∈ histories) →
      (∑ x ∈ carrier, mass x * ‖F x (sigma x)‖^2) ≤ C) :
    (∑ x ∈ carrier, mass x *
      (∑ s ∈ histories, alpha x s * ‖F x s‖^2)) ≤ C := by
  classical
  let sigma : X → S := fun x =>
    Classical.choose (Finset.exists_mem_eq_sup' hs
      (fun s : S => ‖F x s‖^2))
  have hMem (x : X) : sigma x ∈ histories :=
    (Classical.choose_spec (Finset.exists_mem_eq_sup' hs
      (fun s : S => ‖F x s‖^2))).1
  have hMax (x : X) :
      histories.sup' hs (fun s : S => ‖F x s‖^2) =
        ‖F x (sigma x)‖^2 :=
    (Classical.choose_spec (Finset.exists_mem_eq_sup' hs
      (fun s : S => ‖F x s‖^2))).2
  have hPoint (x : X) (hx : x ∈ carrier) :
      (∑ s ∈ histories, alpha x s * ‖F x s‖^2) ≤
        ‖F x (sigma x)‖^2 := by
    calc
      _ ≤ ∑ s ∈ histories,
          alpha x s * ‖F x (sigma x)‖^2 := by
        apply Finset.sum_le_sum
        intro s hs'
        apply mul_le_mul_of_nonneg_left
        exact (Finset.le_sup' (fun t : S => ‖F x t‖^2) hs').trans_eq (hMax x)
        exact hSub.1 x hx s hs'
      _ = (∑ s ∈ histories, alpha x s) *
          ‖F x (sigma x)‖^2 := by
        rw [Finset.sum_mul]
      _ ≤ 1*‖F x (sigma x)‖^2 :=
        mul_le_mul_of_nonneg_right (hSub.2 x hx) (sq_nonneg _)
      _ = _ := one_mul _
  calc
    _ ≤ ∑ x ∈ carrier, mass x * ‖F x (sigma x)‖^2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hPoint x hx) (hmass x hx)
    _ ≤ C := hSelector sigma (fun x hx => hMem x)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualHistoryTVSelectorCS -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The actual total variation of a complex signed prefix over ALL
numerical birth histories at a fixed physical output. This is an L1
variation, not the L2 energy used for Schur estimates. -/
def sourceOriginalHistorySignedTV434 {X S : Type}
    (hist : Finset S) (w : X → S → ℂ) (x : X) : ℝ :=
  ∑ s ∈ hist, ‖w x s‖

/-- Pointwise upper envelope for a genuine physical marked DIRTY
operator, obtained by selecting one real numerical seen history. -/
def sourceOriginalHistoryMaxNorm434 {X S : Type}
    (hist : Finset S) (hh : hist.Nonempty)
    (F : X → S → ℂ) (x : X) : ℝ :=
  hist.sup' hh (fun s => ‖F x s‖)

/-- The right prefix budget in a history-count-FREE Cauchy–Schwarz
argument is inverse-density L1 total variation SQUARED, not the
ordinary joint Fock×seen inverse L2 energy. -/
def sourceOriginalHistorySignedTVInverseEnergy434 {X S : Type} [Fintype X]
    (hist : Finset S) (pi : X → ℝ)
    (w : X → S → ℂ) : ℝ :=
  ∑ x : X, (sourceOriginalHistorySignedTV434 hist w x /
      Real.sqrt (pi x))^2

/-- Selector-energy norm of the pointwise maximum over allowed
chronological seen histories. An actual local marked DIRTY theorem
bounds this because it is uniform over EVERY valid selector. -/
def sourceOriginalHistorySelectorSupEnergy434 {X S : Type} [Fintype X]
    (hist : Finset S) (hh : hist.Nonempty) (pi : X → ℝ)
    (F : X → S → ℂ) : ℝ :=
  ∑ x : X, pi x * (sourceOriginalHistoryMaxNorm434 hist hh F x)^2

theorem source_original_HISTORY_TV_nonneg434
    {X S : Type} (hist : Finset S) (w : X → S → ℂ) (x : X) :
    0 ≤ sourceOriginalHistorySignedTV434 hist w x := by
  unfold sourceOriginalHistorySignedTV434
  exact Finset.sum_nonneg (fun s hs => norm_nonneg _)

theorem source_original_HISTORY_max_nonneg434
    {X S : Type} (hist : Finset S) (hh : hist.Nonempty)
    (F : X → S → ℂ) (x : X) :
    0 ≤ sourceOriginalHistoryMaxNorm434 hist hh F x := by
  rcases hh with ⟨s,hs⟩
  exact (norm_nonneg (F x s)).trans
    (Finset.le_sup' (fun t => ‖F x t‖) hs)

/-- The history supremum is achieved by one actual admissible
history for each physical output, with no independence premise. -/
theorem source_original_HISTORY_max_selector434
    {X S : Type} (hist : Finset S) (hh : hist.Nonempty)
    (F : X → S → ℂ) :
    ∃ sigma : X → S,
      (∀ x, sigma x ∈ hist) ∧
      (∀ x, sourceOriginalHistoryMaxNorm434 hist hh F x =
        ‖F x (sigma x)‖) := by
  classical
  let sigma : X → S := fun x =>
    Classical.choose (Finset.exists_mem_eq_sup' hh (fun s => ‖F x s‖))
  refine ⟨sigma,?_,?_⟩
  · intro x
    exact (Classical.choose_spec (Finset.exists_mem_eq_sup' hh
      (fun s => ‖F x s‖))).1
  · intro x
    exact (Classical.choose_spec (Finset.exists_mem_eq_sup' hh
      (fun s => ‖F x s‖))).2

/-- Uniform local selector-energy saving automatically bounds the
DIRECT physical energy of the pointwise maximum over histories,
with NO history cardinality factor, regardless of its size. -/
theorem source_original_HISTORY_uniform_selector_energy_sup434
    {X S : Type} [Fintype X]
    (hist : Finset S) (hh : hist.Nonempty) (pi : X → ℝ)
    (F : X → S → ℂ) (C : ℝ)
    (hSelector : ∀ sigma : X → S, (∀ x, sigma x ∈ hist) →
      (∑ x : X, pi x * ‖F x (sigma x)‖^2) ≤ C) :
    sourceOriginalHistorySelectorSupEnergy434 hist hh pi F ≤ C := by
  rcases source_original_HISTORY_max_selector434 hist hh F with
    ⟨sigma,hs,hmax⟩
  unfold sourceOriginalHistorySelectorSupEnergy434
  simpa only [hmax] using hSelector sigma hs

/-- Pointwise signed history pairing pays EXACT L1 prefix
variation times the largest allowed physical selector amplitude.
Unlike a naive joint L2 estimate it never counts histories. -/
theorem source_original_HISTORY_signed_pairing_TV434
    {X S : Type} (hist : Finset S) (hh : hist.Nonempty)
    (w F : X → S → ℂ) (x : X) :
    ‖∑ s ∈ hist, w x s * F x s‖ ≤
      sourceOriginalHistorySignedTV434 hist w x *
        sourceOriginalHistoryMaxNorm434 hist hh F x := by
  classical
  calc
    _ ≤ ∑ s ∈ hist, ‖w x s * F x s‖ := norm_sum_le _ _
    _ = ∑ s ∈ hist, ‖w x s‖ * ‖F x s‖ := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [norm_mul]
    _ ≤ ∑ s ∈ hist,
        ‖w x s‖ * sourceOriginalHistoryMaxNorm434 hist hh F x := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left
        (Finset.le_sup' (fun t => ‖F x t‖) hs)
        (norm_nonneg _)
    _ = _ := by
      rw [←Finset.sum_mul]
      rfl

/-- Exact history-count-free weighted Cauchy–Schwarz for the
ORIGINAL COMPLEX signed chronological history pairing. The price
for avoiding the history-count factor is an L1-history total
variation squared on the signed prefix, a DIFFERENT and
currently unproved global budget from the joint L2 prefix norm.
The DIRTY side uses the single-selector maximum energy. -/
theorem source_original_HISTORY_signed_TV_selector_CS434
    {X S : Type} [Fintype X]
    (hist : Finset S) (hh : hist.Nonempty)
    (pi : X → ℝ) (hpi : ∀ x,0 < pi x)
    (w F : X → S → ℂ) :
    ‖∑ x : X, ∑ s ∈ hist, w x s * F x s‖ ≤
      Real.sqrt (sourceOriginalHistorySignedTVInverseEnergy434 hist pi w) *
      Real.sqrt (sourceOriginalHistorySelectorSupEnergy434 hist hh pi F) := by
  classical
  let t : X → ℝ := fun x => sourceOriginalHistorySignedTV434 hist w x
  let m : X → ℝ := fun x => sourceOriginalHistoryMaxNorm434 hist hh F x
  let a : X → ℝ := fun x => t x / Real.sqrt (pi x)
  let b : X → ℝ := fun x => Real.sqrt (pi x) * m x
  calc
    _ ≤ ∑ x : X, ‖∑ s ∈ hist, w x s * F x s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x : X, t x * m x := by
      apply Finset.sum_le_sum
      intro x hx
      exact source_original_HISTORY_signed_pairing_TV434 hist hh w F x
    _ = ∑ x : X, a x * b x := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp only [a,b]
      have hs : Real.sqrt (pi x) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (hpi x))
      field_simp
    _ ≤ Real.sqrt (∑ x : X, a x^2) *
        Real.sqrt (∑ x : X, b x^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
    _ = _ := by
      have hB : (∑ x : X,b x^2) =
          ∑ x : X,pi x*(sourceOriginalHistoryMaxNorm434 hist hh F x)^2 := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp only [b,m]
        rw [mul_pow,Real.sq_sqrt (hpi x).le]
      change Real.sqrt (∑ x : X,a x^2) *
          Real.sqrt (∑ x : X,b x^2) =
        Real.sqrt (∑ x : X,a x^2) *
          Real.sqrt (∑ x : X,pi x*
            (sourceOriginalHistoryMaxNorm434 hist hh F x)^2)
      rw [hB]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualHistoryTVLocalSaving -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Uniform original local marked-DIRTY selector L2 gain and an
ARBITRARY actual signed prefix w imply a history-count-FREE
bilinear bound. Unlike a subprobability-occupation argument,
NO normalization of the complex prefix is assumed.
Its NEW cost is the genuine `l1_history^2 / physical_density`
prefix variation, which has NOT yet been shown polynomially small. -/
theorem source_original_HISTORY_signed_TV_local_selector_bound434
    {X S : Type} [Fintype X]
    (hist : Finset S) (hh : hist.Nonempty)
    (pi : X → ℝ) (hpi : ∀ x,0 < pi x)
    (w F : X → S → ℂ) (C : ℝ)
    (hSelector : ∀ sigma : X → S, (∀ x, sigma x ∈ hist) →
      (∑ x : X, pi x * ‖F x (sigma x)‖^2) ≤ C) :
    ‖∑ x : X, ∑ s ∈ hist, w x s * F x s‖ ≤
      Real.sqrt (sourceOriginalHistorySignedTVInverseEnergy434 hist pi w) *
      Real.sqrt C := by
  have hCS := source_original_HISTORY_signed_TV_selector_CS434
    hist hh pi hpi w F
  have hMax := source_original_HISTORY_uniform_selector_energy_sup434
    hist hh pi F C hSelector
  have hRoot := Real.sqrt_le_sqrt hMax
  exact hCS.trans
    (mul_le_mul_of_nonneg_left hRoot
      (Real.sqrt_nonneg _))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFiniteHistoryComplexDisintegration -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- A complex signed measure on the TRUE reachable product carrier
is extended by ZERO outside that carrier. This does not assign any
probability to the finite history pool. -/
def sourceOriginalFiniteHistoryComplexExtend434
    {X S : Type} [DecidableEq X] [DecidableEq S]
    (carrier : Finset (X × S))
    (w : {z : X × S // z ∈ carrier} → ℂ)
    (x : X) (s : S) : ℂ :=
  if h : (x,s) ∈ carrier then w ⟨(x,s),h⟩ else 0

/-- TRUE complex-signed disintegration over the support and the
cumulative numerical history. No cardinality multiplier,
no history supremum, and no replacement of a complex prefix by
a positive measure. -/
theorem source_original_SIGNED_finite_history_disintegration434
    {X S : Type} [DecidableEq X] [DecidableEq S]
    (support : Finset X) (hist : Finset S)
    (eligible : X → S → Prop)
    [DecidablePred (fun z : X × S => eligible z.1 z.2)]
    (w : {z : X × S //
      z ∈ (support.product hist).filter (fun z => eligible z.1 z.2)} → ℂ)
    (F : X → S → ℂ) :
    (∑ a : {z : X × S //
      z ∈ (support.product hist).filter (fun z => eligible z.1 z.2)},
      w a * F a.val.1 a.val.2) =
    ∑ x ∈ support,∑ s ∈ hist,
      sourceOriginalFiniteHistoryComplexExtend434
        ((support.product hist).filter (fun z => eligible z.1 z.2))
        w x s * F x s := by
  classical
  let carrier := (support.product hist).filter
    (fun z : X × S => eligible z.1 z.2)
  let W : X × S → ℂ := fun z =>
    sourceOriginalFiniteHistoryComplexExtend434 carrier w z.1 z.2 *
      F z.1 z.2
  have hz (z : X × S) (hz : z ∈ support.product hist)
      (hnot : ¬ eligible z.1 z.2) : W z = 0 := by
    have hmem : z ∉ carrier := by
      simp only [carrier,Finset.mem_filter]
      intro h
      exact hnot h.2
    simp only [W,sourceOriginalFiniteHistoryComplexExtend434,
      dif_neg hmem,zero_mul]
  calc
    _ = ∑ z ∈ carrier,W z := by
      have he := Finset.sum_coe_sort carrier W
      rw [←he]
      apply Finset.sum_congr rfl
      intro a ha
      rcases a with ⟨⟨x,s⟩,has⟩
      change w ⟨(x,s),has⟩ * F x s =
        (if h : (x,s) ∈ carrier then w ⟨(x,s),h⟩ else 0) * F x s
      have hh : (x,s) ∈ carrier := has
      simp [hh]
    _ = ∑ z ∈ support.product hist,
        if eligible z.1 z.2 then W z else 0 := by
      simp only [carrier,Finset.sum_filter]
    _ = ∑ z ∈ support.product hist,W z := by
      apply Finset.sum_congr rfl
      intro z hz'
      by_cases helig : eligible z.1 z.2
      · simp only [if_pos helig]
      · simp only [if_neg helig,hz z hz' helig]
    _ = ∑ x ∈ support,∑ s ∈ hist,W (x,s) := by
      exact Finset.sum_product support hist W
    _ = _ := by
      rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPhysicalTV -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Extend a genuine reachable Fock×cumulative-seen signed prefix
by ZERO to all pairs (physical Fock output, permitted history).
No probabilistic Markov extension is introduced. -/
def sourceOriginalActualSignedPhysicalPrefixAt434
    (w : H → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (s : Finset ℕ) : ℂ :=
  sourceOriginalFiniteHistoryComplexExtend434
    (sourceOriginalActualSignedHistoryCarrierFinset434
      SP sm BP bm J ell cap) w y s

/-- Original physical density on a Fock output, with the genuine
OLD-sector power of Vb and actual Fock mass. -/
def sourceOriginalActualSignedPhysicalFockDensity434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) : ℝ :=
  physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y *
    sourceOriginalMemorySectorDensity434 SP sm BP bm J ell Vb y

/-- The unknown true physical CLEAN-prefix variation budget,
with its L1 sum over ALL reachable numerical histories squared and
divided by the SAME actual Fock/OLD-sector input density as the
local physical marked DIRTY selector. It contains no |Hist| factor,
but its polynomial growth is NOT proved by the earlier L2 Schur
bounds; this is a distinct analytic task. -/
def sourceOriginalActualSignedPhysicalTVInverseEnergy434
    (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (w : H → ℂ) : ℝ :=
  ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
    ((∑ s ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
       ‖sourceOriginalActualSignedPhysicalPrefixAt434
           SP sm BP bm J ell cap w y s‖) /
     Real.sqrt (sourceOriginalActualSignedPhysicalFockDensity434
       SP sm BP bm J ell cap Vs Vb mu y))^2

/-- The genuine complex Fock×seen matrix pairing is EXACTLY its
physical-support plus numerical-history double sum, with the
signed prefix set to zero on unreachable histories. Neither
inaccessible states nor the number of possible histories are paid. -/
theorem source_original_ACTUAL_SIGNED_physical_prefix_double_sum434
    (w : H → ℂ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    (∑ a : H, w a * F a.val.1 a.val.2) =
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      ∑ s ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        sourceOriginalActualSignedPhysicalPrefixAt434
          SP sm BP bm J ell cap w y s * F y s := by
  classical
  exact source_original_SIGNED_finite_history_disintegration434
    (physicalFockOrbitSupport SP sm BP bm (J+ell) cap)
    ((sourceOriginalMemoryBirthPool434 BP bm).powerset)
    (fun y s => sourceOriginalPhysicalReachable434
      SP sm BP bm (J+ell) y s) w F
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPhysicalFibreTV -/

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

/-- Exactly the original finite physical Fock orbit, without the
full unbounded type of all possible physical outputs. -/
def sourceOriginalActualPhysicalFibreState434 :=
  {y : FullPhysicalOutput SP sm BP bm (J+ell) //
    y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap}

noncomputable instance :
    Fintype (sourceOriginalActualPhysicalFibreState434
      SP sm BP bm J ell cap) :=
  Finset.fintypeCoeSort
    (physicalFockOrbitSupport SP sm BP bm (J+ell) cap)

noncomputable instance :
    DecidableEq (sourceOriginalActualPhysicalFibreState434
      SP sm BP bm J ell cap) := Classical.decEq _

/-- A true reachable Fock×seen state projects to its actual
physical Fock orbit, and the accumulated history is not reset. -/
def sourceOriginalActualSignedFibreProjection434 :
    sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap →
    sourceOriginalActualPhysicalFibreState434 SP sm BP bm J ell cap :=
  fun a => ⟨a.val.1,
    (source_original_ACTUAL_signed_history_mem_iff434
      SP sm BP bm J ell cap a.val.1 a.val.2).mp a.property |>.1⟩

/-- True total variation profile over only REACHABLE chronological
histories attached to each physical output. -/
def sourceOriginalActualSignedFibreTVProfile434
    (w : sourceOriginalActualSignedHistoryState434
      SP sm BP bm J ell cap → ℂ)
    (y : sourceOriginalActualPhysicalFibreState434
      SP sm BP bm J ell cap) : ℝ :=
  sourceOriginalFiniteFibreTVProfile434
    (sourceOriginalActualSignedFibreProjection434 SP sm BP bm J ell cap)
    w y
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedTrueMatrixEnergy -/

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
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The exact original joint-state DIRTY target energy is a real
Fock/OLD-density weighted square sum, NOT a positive surrogate. -/
theorem source_original_ACTUAL_true_target_energy_expansion434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g)
    (hmu : ∀ g p, 0 < mu g p) (f : H → ℂ) :
    sourceOriginalActualSignedTrueTargetEnergy434 SP sm BP bm J ell cap Vs Vb mu f =
    ∑ a : H, sourceOriginalActualSignedTrueFockDensity434
      SP sm BP bm J ell cap Vs Vb mu a * ‖f a‖^2 := by
  classical
  unfold sourceOriginalActualSignedTrueTargetEnergy434
    sourceOriginalSignedJointForwardEnergy434
  apply Finset.sum_congr rfl
  intro a ha
  have hπ := source_original_ACTUAL_signed_true_fock_density_pos434
    SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu a
  rw [mul_pow,Real.sq_sqrt hπ.le]

/-- The inverse-density CLEAN-prefix energy is literally the dual
Fock/OLD L² energy on the SAME original joint history state. -/
theorem source_original_ACTUAL_true_prefix_energy_expansion434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g)
    (hmu : ∀ g p,0 < mu g p) (w : H → ℂ) :
    sourceOriginalActualSignedTruePrefixEnergy434 SP sm BP bm J ell cap Vs Vb mu w =
    ∑ a : H, ‖w a‖^2 /
      sourceOriginalActualSignedTrueFockDensity434
        SP sm BP bm J ell cap Vs Vb mu a := by
  classical
  unfold sourceOriginalActualSignedTruePrefixEnergy434
    sourceOriginalSignedJointInverseEnergy434
  apply Finset.sum_congr rfl
  intro a ha
  have hπ := source_original_ACTUAL_signed_true_fock_density_pos434
    SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu a
  rw [div_pow,Real.sq_sqrt hπ.le]

/-- The original projected CLEAN/DIRTY/FULL finite E matrix has
EXACT target energy against the REAL Fock/OLD sector density,
summed over all reachable histories without an artificial maximum. -/
theorem source_original_ACTUAL_signed_OLD_E_true_energy434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g)
    (hmu : ∀ g p,0 < mu g p)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (o k : ℤ) (T : ℕ) (f : H → ℂ) :
    sourceOriginalActualSignedTrueTargetEnergy434
      SP sm BP bm J ell cap Vs Vb mu
      (fun a => ∑ b : H,
        sourceOriginalActualSignedOLDMaskedEMatrix434
          SP sm BP bm J ell m cap patterns keep
          q rho Vs Vb mu K zeta theta o k T a b * f b) =
    ∑ a : H,
      sourceOriginalActualSignedTrueFockDensity434
        SP sm BP bm J ell cap Vs Vb mu a *
      ‖sourceOriginalActualSignedOLDMaskedFiniteE434
        SP sm BP bm J ell m cap patterns keep
        q rho Vs Vb mu K zeta theta o k T f a‖^2 := by
  rw [source_original_ACTUAL_true_target_energy_expansion434
    SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu]
  apply Finset.sum_congr rfl
  intro a ha
  rw [←source_original_ACTUAL_signed_OLD_masked_E_matrix_exact434
    SP sm BP bm J ell m cap patterns keep
    q rho Vs Vb mu K zeta theta o k T f a]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDeltaEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- An injective placement of finitely many complex coefficients into
a larger signed-state carrier has NO extra energy multiplicity.
This identity works even for an empty source and with arbitrary π. -/
theorem source_original_SIGNED_injective_delta_energy434
    {Y H : Type} [Fintype Y] [Fintype H]
    (i : Y → H) (hi : Function.Injective i)
    (z : Y → ℂ) (π : H → ℝ) :
    (∑ a : H,
      ‖∑ y : Y, if a = i y then z y else 0‖^2 / π a) =
    ∑ y : Y, ‖z y‖^2 / π (i y) := by
  classical
  have hSingle (a : H) :
      ‖∑ y : Y, if a = i y then z y else 0‖^2 =
      ∑ y : Y, if a = i y then ‖z y‖^2 else 0 := by
    by_cases ha : ∃ y : Y, a = i y
    · obtain ⟨y,hy⟩ := ha
      subst a
      have hh (v : Y) : i y = i v ↔ y = v := hi.eq_iff
      simp only [hh]
      simp
    · have hh (y : Y) : a ≠ i y := by
        intro h
        exact ha ⟨y,h⟩
      simp only [if_neg (hh _), Finset.sum_const_zero, norm_zero,
        zero_pow (by norm_num : 2 ≠ 0)]
  calc
    _ = ∑ a : H,
          ∑ y : Y, if a = i y then ‖z y‖^2 / π a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hSingle]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : a = i y
      · simp only [if_pos h]
      · simp only [if_neg h,zero_div]
    _ = ∑ y : Y,
          ∑ a : H, if a = i y then ‖z y‖^2 / π a else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ y : Y, ‖z y‖^2 / π (i y) := by
      apply Finset.sum_congr rfl
      intro y hy
      simp
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedInitialDualEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 17000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The genuine initial vacuum-state injection into the original
Fock×cumulative-seen carrier is INJECTIVE because its physical output
is retained, even when initial prime histories coincide. -/
theorem source_original_ACTUAL_signed_initial_state_injective434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g) :
    Function.Injective
      (sourceOriginalActualSignedInitialState434 SP sm BP bm J ell cap hcap) := by
  intro y z h
  apply Subtype.ext
  exact congrArg (fun a : H => a.val.1) h

/-- The inverse-density norm of the true initial signed Fock/vacuum
prefix is exactly ONE sum over the initial physical vacuum orbit.
No multiplicity from other seen histories is paid. -/
theorem source_original_ACTUAL_signed_initial_weight_dual_energy434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g)
    (hmu : ∀ g p,0 < mu g p) :
    sourceOriginalActualSignedTruePrefixEnergy434
      SP sm BP bm J ell cap Vs Vb mu
      (sourceOriginalActualSignedInitialWeight434
        SP sm BP bm J ell cap hcap Vs mu) =
    ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434
        SP sm BP bm J ell cap},
      ‖(physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val : ℂ) *
        star (physicalVacuum SP sm BP bm J ell y.val)‖^2 /
      sourceOriginalActualSignedTrueFockDensity434
        SP sm BP bm J ell cap Vs Vb mu
        (sourceOriginalActualSignedInitialState434
          SP sm BP bm J ell cap hcap y) := by
  classical
  rw [source_original_ACTUAL_true_prefix_energy_expansion434
    SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu]
  have h := source_original_SIGNED_injective_delta_energy434
    (sourceOriginalActualSignedInitialState434
      SP sm BP bm J ell cap hcap)
    (source_original_ACTUAL_signed_initial_state_injective434
      SP sm BP bm J ell cap hcap)
    (fun y => (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y.val))
    (sourceOriginalActualSignedTrueFockDensity434
      SP sm BP bm J ell cap Vs Vb mu)
  simpa only [sourceOriginalActualSignedInitialWeight434] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualInitialHistorySparse -/

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
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap
local notation "X" => sourceOriginalActualPhysicalFibreState434 SP sm BP bm J ell cap
local notation "Y" => {y : FullPhysicalOutput SP sm BP bm (J+ell) //
  y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap}

/-- A nonzero ORIGINAL initial complex vacuum/Fock amplitude must
be supported at the UNIQUE actual initial state for some genuine
nonzero-vacuum physical output; an arbitrary seen history has
no independent initial weight. -/
theorem source_original_ACTUAL_initial_weight_supported434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : H)
    (h : sourceOriginalActualSignedInitialWeight434
      SP sm BP bm J ell cap hcap Vs mu a ≠ 0) :
    ∃ y : Y, a = sourceOriginalActualSignedInitialState434
        SP sm BP bm J ell cap hcap y := by
  classical
  by_contra hn
  push_neg at hn
  have hz :
      sourceOriginalActualSignedInitialWeight434
        SP sm BP bm J ell cap hcap Vs mu a = 0 := by
    unfold sourceOriginalActualSignedInitialWeight434
    apply Finset.sum_eq_zero
    intro y hy
    simp only [if_neg (hn y)]
  exact h hz

/-- Only ONE genuine initial physical output can occupy a given
initial Fock fibre; no other initial seen value contributes. -/
theorem source_original_ACTUAL_initial_weight_fibre_sparse434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a b : H)
    (hp : sourceOriginalActualSignedFibreProjection434
      SP sm BP bm J ell cap a =
      sourceOriginalActualSignedFibreProjection434
      SP sm BP bm J ell cap b)
    (ha : sourceOriginalActualSignedInitialWeight434
      SP sm BP bm J ell cap hcap Vs mu a ≠ 0)
    (hb : sourceOriginalActualSignedInitialWeight434
      SP sm BP bm J ell cap hcap Vs mu b ≠ 0) : a = b := by
  obtain ⟨ya,hya⟩ := source_original_ACTUAL_initial_weight_supported434
    SP sm BP bm J ell cap hcap Vs mu a ha
  obtain ⟨yb,hyb⟩ := source_original_ACTUAL_initial_weight_supported434
    SP sm BP bm J ell cap hcap Vs mu b hb
  rw [hya,hyb] at hp ⊢
  have hyo : ya.val = yb.val := by
    exact congrArg (fun x : X => x.val) hp
  have hy : ya = yb := Subtype.ext hyo
  rw [hy]

/-- The SOURCE original initial signed Fock/vacuum prefix has exactly
one possible nonzero numerical seen history for each physical
output, despite the full finite reachability pool being enormous.
Consequently its fibrewise L1-history variation squared is
EXACTLY its L2-amplitude mass. -/
theorem source_original_ACTUAL_initial_TV_fibre_sq434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (x : X) :
    (sourceOriginalActualSignedFibreTVProfile434
      SP sm BP bm J ell cap
      (sourceOriginalActualSignedInitialWeight434
        SP sm BP bm J ell cap hcap Vs mu) x)^2 =
    ∑ a ∈ (Finset.univ : Finset H).filter
      (fun a => sourceOriginalActualSignedFibreProjection434
        SP sm BP bm J ell cap a = x),
      ‖sourceOriginalActualSignedInitialWeight434
        SP sm BP bm J ell cap hcap Vs mu a‖^2 := by
  exact source_original_finite_fibre_sparse_TV_sq434
    (sourceOriginalActualSignedFibreProjection434
      SP sm BP bm J ell cap)
    (sourceOriginalActualSignedInitialWeight434
      SP sm BP bm J ell cap hcap Vs mu)
    (source_original_ACTUAL_initial_weight_fibre_sparse434
      SP sm BP bm J ell cap hcap Vs mu) x
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedInitialVacuumNorm -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 17000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The original OLD-sector density is EXACTLY ONE at every
nonzero initial physical vacuum orbit. No normalization assumption. -/
theorem source_original_ACTUAL_initial_vacuum_sector_density_one434
    (Vb : BG → ℝ)
    (y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434
        SP sm BP bm J ell cap}) :
    sourceOriginalMemorySectorDensity434 SP sm BP bm J ell Vb y.val = 1 := by
  have hv : physicalVacuum SP sm BP bm J ell y.val ≠ 0 :=
    (Finset.mem_filter.mp y.property).2.1
  have hp : ∀ g : BG,(y.val.2 g).2 = 0 := by
    by_contra h
    exact hv (if_neg h)
  unfold sourceOriginalMemorySectorDensity434
  apply Finset.prod_eq_one
  intro g hg
  rw [hp g]
  simp

/-- The true initial signed Fock weight has EXACT inverse-density
energy equal to its vacuum weighted norm, with no independent
history count, OLD-sector reweighting, or unexplained factor N. -/
theorem source_original_ACTUAL_initial_signed_dual_energy_vacuum434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g)
    (hmu : ∀ g p,0 < mu g p) :
    sourceOriginalActualSignedTruePrefixEnergy434
      SP sm BP bm J ell cap Vs Vb mu
      (sourceOriginalActualSignedInitialWeight434
        SP sm BP bm J ell cap hcap Vs mu) =
    ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap},
      physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val *
        ‖physicalVacuum SP sm BP bm J ell y.val‖^2 := by
  classical
  rw [source_original_ACTUAL_signed_initial_weight_dual_energy434
    SP sm BP bm J ell cap hcap Vs Vb mu hVs hVb hmu]
  apply Finset.sum_congr rfl
  intro y hy
  let M : ℝ := physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val
  have hM : 0 < M :=
    physicalOrbitMass_pos SP sm BP bm (J+ell) cap
      Vs mu hVs hmu y.val (Finset.mem_filter.mp y.property).1
  have hSec := source_original_ACTUAL_initial_vacuum_sector_density_one434
    SP sm BP bm J ell cap Vb y
  have hπ :
      sourceOriginalActualSignedTrueFockDensity434
        SP sm BP bm J ell cap Vs Vb mu
        (sourceOriginalActualSignedInitialState434
          SP sm BP bm J ell cap hcap y) = M := by
    change M * sourceOriginalMemorySectorDensity434
      SP sm BP bm J ell Vb y.val = M
    rw [hSec,mul_one]
  rw [hπ]
  have hMnorm : ‖(M:ℂ)‖=M := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
  change ‖(M:ℂ) * star (physicalVacuum SP sm BP bm J ell y.val)‖^2 / M =
    M * ‖physicalVacuum SP sm BP bm J ell y.val‖^2
  rw [norm_mul,norm_star,hMnorm]
  field_simp [ne_of_gt hM]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPhysicalPrefixSchur -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 24000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Sum over all actual chronological CLEAN-prefix lengths of the
finite, explicit Fock×seen Schur transfer products for the true
orientation-dependent source joint K. No hContraction assumption. -/
def sourceOriginalActualPhysicalCLEANSchurSum434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (k : ℤ) (R T : ℕ) : ℝ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N Vb
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs Vb mu K zeta theta k N T
  let π := sourceOriginalActualSignedTrueFockDensity434
    SP sm BP bm J ell cap Vs Vb mu
  ∑ j ∈ Finset.range N,
    sourceOriginalSignedPrefixSchurGainChain434 Clean π j 0

/-- Exact true initial Fock/vacuum Hilbert cost, restricted only
by its genuine no-repeated-initial-primes gate. The small Haar
mass and OLD distributions are NOT normalized by assertion. -/
def sourceOriginalActualPhysicalInitialVacuumEnergy434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) : ℝ :=
  ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap},
    physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val *
      ‖physicalVacuum SP sm BP bm J ell y.val‖^2

/-- Unconditional SIGNED CLEAN-prefix global energy bound from actual
matrix Schur constants and the exact original initial vacuum norm.
No multiplicative numerical history count or assumed Markovness. -/
theorem source_original_ACTUAL_physical_CLEAN_prefix_Schur434
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) Vb g p) :
    (sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs Vb K zeta theta k R T).1 ≤
    sourceOriginalActualPhysicalCLEANSchurSum434
      SP sm BP bm J ell m cap patterns
      q rho Vs Vb K zeta theta k R T *
    sourceOriginalActualPhysicalInitialVacuumEnergy434
      SP sm BP bm J ell cap Vs
      (physicalSourceMuTilde BP bm q (2*R) Vb) := by
  classical
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N Vb
  let Clean := sourceOriginalActualSignedProjectedGESchedule434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs Vb mu K zeta theta k N T
  let π := sourceOriginalActualSignedTrueFockDensity434
    SP sm BP bm J ell cap Vs Vb mu
  let w := sourceOriginalActualSignedInitialWeight434
    SP sm BP bm J ell cap hcap Vs mu
  have hπ (a : sourceOriginalActualSignedHistoryState434
      SP sm BP bm J ell cap) : 0 < π a :=
    source_original_ACTUAL_signed_true_fock_density_pos434
      SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu a
  have hSchur := source_original_SIGNED_prefix_energy_sum_Schur434
    Clean π hπ N 0 w
  have hInitial := source_original_ACTUAL_initial_signed_dual_energy_vacuum434
    SP sm BP bm J ell cap hcap Vs Vb mu hVs hVb hmu
  change sourceOriginalSignedPrefixEnergySum434 Clean π N 0 w ≤
    (∑ j ∈ Finset.range N,
      sourceOriginalSignedPrefixSchurGainChain434 Clean π j 0) *
      sourceOriginalActualPhysicalInitialVacuumEnergy434
        SP sm BP bm J ell cap Vs mu
  exact hSchur.trans_eq (by
    rw [show sourceOriginalSignedJointInverseEnergy434 π w =
        sourceOriginalActualPhysicalInitialVacuumEnergy434
          SP sm BP bm J ell cap Vs mu from hInitial])
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPhysicalSchurDIRTY -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- True FIRST-DIRTY physical root controlled using exactly the
initial vacuum Fock mass, computed chronological CLEAN row/column
Schur maxima, and the original unmodified DIRTY-suffix L² energy.
NO unproved CLEAN-prefix energy bound survives as a free premise. -/
theorem source_original_ACTUAL_PHYSICAL_signed_DIRTY_Schur_energy434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hmu : ∀ g p, 0 < physicalSourceMuTilde BP bm q (2*R) Vb g p) :
    ‖sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns q rho Vs Vb K zeta theta k R T‖ ≤
    ‖(physicalSourceBaselineProduct BP bm q (2*R) : ℂ)‖ *
    Real.sqrt
      (sourceOriginalActualPhysicalCLEANSchurSum434
        SP sm BP bm J ell m cap patterns
        q rho Vs Vb K zeta theta k R T *
       sourceOriginalActualPhysicalInitialVacuumEnergy434
        SP sm BP bm J ell cap Vs
          (physicalSourceMuTilde BP bm q (2*R) Vb)) *
    Real.sqrt
      ((sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
        SP sm BP bm J ell m cap patterns hcap
        q rho Vs Vb K zeta theta k R T).2) := by
  let P := (sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
    SP sm BP bm J ell m cap patterns hcap
    q rho Vs Vb K zeta theta k R T).1
  let Targ := (sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
    SP sm BP bm J ell m cap patterns hcap
    q rho Vs Vb K zeta theta k R T).2
  let S := sourceOriginalActualPhysicalCLEANSchurSum434
    SP sm BP bm J ell m cap patterns q rho Vs Vb K zeta theta k R T
  let Vac := sourceOriginalActualPhysicalInitialVacuumEnergy434
    SP sm BP bm J ell cap Vs
    (physicalSourceMuTilde BP bm q (2*R) Vb)
  have hP : P ≤ S * Vac :=
    source_original_ACTUAL_physical_CLEAN_prefix_Schur434
      SP sm BP bm J ell m cap patterns
      hcap q rho Vs Vb hVs hVb K zeta theta k R T hmu
  have hRoot := source_original_ACTUAL_PHYSICAL_signed_DIRTY_root_energy_norm434
    SP sm BP bm J ell m cap patterns
    hi hcap q rho Vs Vb hVs hVb K zeta theta k R T hmu
  have hSqrt := Real.sqrt_le_sqrt hP
  change ‖sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
    SP sm BP bm J ell m cap patterns q rho Vs Vb K zeta theta k R T‖ ≤
    ‖(physicalSourceBaselineProduct BP bm q (2*R) : ℂ)‖ *
      Real.sqrt (S * Vac) * Real.sqrt Targ
  calc
    _ ≤ ‖(physicalSourceBaselineProduct BP bm q (2*R) : ℂ)‖ *
      Real.sqrt P * Real.sqrt Targ := hRoot
    _ ≤ ‖(physicalSourceBaselineProduct BP bm q (2*R) : ℂ)‖ *
      Real.sqrt (S * Vac) * Real.sqrt Targ := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left hSqrt (norm_nonneg _)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedInitialMassBudget -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 25000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The actual source initial vacuum is a 0/1 observable; its L2
norm-square is exactly its L1 norm. No small or BIG sector approximation. -/
theorem source_original_ACTUAL_initial_vacuum_norm_sq434
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) :
    ‖physicalVacuum SP sm BP bm J ell y‖ ^ 2 =
      ‖physicalVacuum SP sm BP bm J ell y‖ := by
  classical
  by_cases h : ∀ g : BG,(y.2 g).2 = 0
  · simp [physicalVacuum,h]
  · simp [physicalVacuum,h]

/-- The initial original 0/1-vacuum norm on every genuinely retained
nonzero sector is ONE. -/
theorem source_original_ACTUAL_initial_good_vacuum_norm_one434
    (y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap}) :
    ‖physicalVacuum SP sm BP bm J ell y.val‖=1 := by
  classical
  have hne := (Finset.mem_filter.mp y.property).2.1
  unfold physicalVacuum at hne ⊢
  by_cases h : ∀ g : BG,(y.val.2 g).2=0
  · simp [h]
  · exact False.elim (hne (by simp [h]))

/-- The genuine initial source Fock/vacuum mass of nonzero and
initially Nodup orbits, without the external BIG baseline. -/
def sourceOriginalActualSignedInitialGoodMass434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) : ℝ :=
  ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) //
      y ∈ sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap},
    physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y.val

/-- Genuine initial signed prefix DUAL Fock×seen energy equals
the unnormalized actual nonzero-vacuum orbit mass, and nothing more. -/
theorem source_original_ACTUAL_initial_signed_dual_energy_good_mass434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g)
    (hmu : ∀ g p,0 < mu g p) :
    sourceOriginalActualSignedTruePrefixEnergy434
      SP sm BP bm J ell cap Vs Vb mu
      (sourceOriginalActualSignedInitialWeight434
        SP sm BP bm J ell cap hcap Vs mu) =
    sourceOriginalActualSignedInitialGoodMass434
      SP sm BP bm J ell cap Vs mu := by
  rw [source_original_ACTUAL_initial_signed_dual_energy_vacuum434
    SP sm BP bm J ell cap hcap Vs Vb mu hVs hVb hmu]
  unfold sourceOriginalActualSignedInitialGoodMass434
  apply Finset.sum_congr rfl
  intro y hy
  rw [source_original_ACTUAL_initial_good_vacuum_norm_one434
    SP sm BP bm J ell cap y]
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedInitialMassBaseline -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 22000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- Original initial physical boundary, with its TRUE baseline and
Nodup/vacuum gates, is EXACTLY the scalar baseline times the
unique (nonzero) initial Fock-orbit mass. -/
theorem source_original_ACTUAL_initial_mass_eq_signed_good_mass434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (R : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    sourceOriginalActualInitialVacuumMass434 SP sm BP bm J ell cap q Vs V R =
    ‖(physicalSourceBaselineProduct BP bm q (2*R) : ℂ)‖ *
      sourceOriginalActualSignedInitialGoodMass434 SP sm BP bm J ell cap
        Vs (physicalSourceMuTilde BP bm q (2*R) V) := by
  classical
  let mu := physicalSourceMuTilde BP bm q (2*R) V
  let S := physicalFockOrbitSupport SP sm BP bm (J+ell) cap
  let Good := sourceOriginalActualSignedInitialGood434 SP sm BP bm J ell cap
  let mass := physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu
  let vac := physicalVacuum SP sm BP bm J ell
  unfold sourceOriginalActualInitialVacuumMass434
    sourceOriginalActualSignedInitialGoodMass434
  dsimp only
  apply congrArg (fun t : ℝ =>
    ‖(physicalSourceBaselineProduct BP bm q (2*R) : ℂ)‖ * t)
  have hTerm (y : FullPhysicalOutput SP sm BP bm (J+ell))
      (hy : y ∈ S) :
      ‖(mass y : ℂ)‖ * ‖vac y‖ *
        (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
          then (1:ℝ) else 0) =
      if vac y ≠ 0 ∧
        (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
      then mass y else 0 := by
    have hp : 0 < mass y := physicalOrbitMass_pos
      SP sm BP bm (J+ell) cap Vs mu hVs hmu y hy
    have hm : ‖(mass y:ℂ)‖=mass y := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
    rw [hm]
    by_cases hv : vac y=0
    · simp [hv]
    · have hv1 : ‖vac y‖ = 1 := by
        dsimp only [vac]
        unfold physicalVacuum at hv ⊢
        by_cases h : ∀ g : BG,(y.2 g).2=0
        · simp [h]
        · have hz : vac y = 0 := by
            simp [vac,physicalVacuum,h]
          exact False.elim (hv hz)
      rw [hv1,mul_one]
      by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
      · simp [hv,hn]
      · simp [hv,hn]
  calc
    (∑ y ∈ S,
      ‖(mass y : ℂ)‖ * ‖vac y‖ *
        (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
          then (1:ℝ) else 0)) =
      ∑ y ∈ S,
        (if vac y ≠ 0 ∧
          (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
        then mass y else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hTerm y hy
    _ = ∑ y ∈ Good, mass y := by
      change (∑ y ∈ S,
        (if vac y ≠ 0 ∧
          (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
        then mass y else 0)) =
        ∑ y ∈ S.filter (fun y => vac y ≠ 0 ∧
          (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup),
          mass y
      rw [Finset.sum_filter]
    _ = ∑ y : {y : FullPhysicalOutput SP sm BP bm (J+ell) // y ∈ Good},
        mass y.val := by
      exact (Finset.sum_attach Good mass).symm
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedInitialSchurMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 23000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- The actual signed INITIAL inverse-density Fock energy is
exactly the literal positive mass of ORIGINAL good vacua:
zero OLD sector, no repeated initial birth, and no history count. -/
theorem source_original_ACTUAL_physical_initial_vacuum_energy_eq_good434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) :
    sourceOriginalActualPhysicalInitialVacuumEnergy434
      SP sm BP bm J ell cap Vs mu =
    sourceOriginalActualSignedInitialGoodMass434
      SP sm BP bm J ell cap Vs mu := by
  classical
  unfold sourceOriginalActualPhysicalInitialVacuumEnergy434
    sourceOriginalActualSignedInitialGoodMass434
  apply Finset.sum_congr rfl
  intro y hy
  rw [source_original_ACTUAL_initial_good_vacuum_norm_one434
    SP sm BP bm J ell cap y]
  ring

/-- The true source baseline TIMES the initial signed Fock energy is
paid by the original SMALL marked-state budget and NOTHING MORE.
The numerical Nodup gate cancels BIG harmonic law and BIG baseline.
No extra assumption of unit vacuum energy is made. -/
theorem source_original_ACTUAL_physical_initial_Schur_mass_budget434
    (q : ℝ) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g, ∑ p : BP g, 1/(bm g p:ℝ)=Vb g)
    (R : ℕ)
    (hb : ∀ g p,0 < physicalSourceBaseline BP bm q (2*R) g p)
    (hb1 : ∀ g p,physicalSourceBaseline BP bm q (2*R) g p ≤ 1) :
    ‖(physicalSourceBaselineProduct BP bm q (2*R) : ℂ)‖ *
      sourceOriginalActualPhysicalInitialVacuumEnergy434
        SP sm BP bm J ell cap Vs
          (physicalSourceMuTilde BP bm q (2*R) Vb) ≤
    ∏ g : SG, ((Fintype.card (SP g):ℝ) / Vs g)^(J+ell) := by
  classical
  have hmu (g : BG) (p : BP g) :
      0 < physicalSourceMuTilde BP bm q (2*R) Vb g p := by
    have hp : (0:ℝ) < (bm g p:ℝ) :=
      Nat.cast_pos.mpr (NeZero.pos (bm g p))
    have hbp : 0 < physicalSourceBaseline BP bm q (2*R) g p := hb g p
    have hv : 0 < Vb g := hVb g
    dsimp only [physicalSourceMuTilde]
    positivity
  have hMass := source_original_ACTUAL_initial_mass_le_SMALL_mass434
    SP sm BP bm J ell cap q Vs hVs Vb hVb hHarmonic R hb hb1
  have hEq := source_original_ACTUAL_initial_mass_eq_signed_good_mass434
    SP sm BP bm J ell cap q Vs Vb R hVs hmu
  calc
    _ = sourceOriginalActualInitialVacuumMass434
          SP sm BP bm J ell cap q Vs Vb R := by
          rw [source_original_ACTUAL_physical_initial_vacuum_energy_eq_good434]
          exact hEq.symm
    _ ≤ ∑ s : GroupState SP sm (J+ell),
        groupStateMass SP sm (J+ell) Vs := hMass
    _ ≤ ∏ g : SG, ((Fintype.card (SP g):ℝ) / Vs g)^(J+ell) :=
      source_original_ACTUAL_SMALL_GROUP_initial_mass_bound434
        SP sm (J+ell) Vs hVs
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPhysicalSchurBoundary -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 23000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Original physical BIG baseline has modulus at most ONE whenever
each real input b_p is in (0,1], with no factor for the BIG alphabet. -/
theorem source_original_ACTUAL_physical_baseline_norm_le_one434
    (q : ℝ) (N : ℕ)
    (hb : ∀ g p,0 < physicalSourceBaseline BP bm q N g p)
    (hb1 : ∀ g p,physicalSourceBaseline BP bm q N g p ≤ 1) :
    ‖(physicalSourceBaselineProduct BP bm q N : ℂ)‖ ≤ 1 := by
  have hLocal0 (g : BG) :
      0 ≤ ∏ p : BP g, physicalSourceBaseline BP bm q N g p :=
    Finset.prod_nonneg (fun p _ => (hb g p).le)
  have hLocal1 (g : BG) :
      (∏ p : BP g, physicalSourceBaseline BP bm q N g p) ≤ 1 := by
    calc
      _ ≤ ∏ _p : BP g, (1:ℝ) :=
        Finset.prod_le_prod₀ (fun p _ => (hb g p).le)
          (fun p _ => hb1 g p)
      _ = 1 := by simp
  have hGlobal0 :
      0 ≤ physicalSourceBaselineProduct BP bm q N :=
    Finset.prod_nonneg (fun g _ => hLocal0 g)
  have hGlobal1 :
      physicalSourceBaselineProduct BP bm q N ≤ 1 := by
    unfold physicalSourceBaselineProduct
    calc
      _ ≤ ∏ _g : BG, (1:ℝ) :=
        Finset.prod_le_prod₀
          (fun g _ => hLocal0 g)
          (fun g _ => hLocal1 g)
      _ = 1 := by simp
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hGlobal0]
  exact hGlobal1

/-- Elementary exact-positive budget transfer. If the baseline is
contractive and the baseline-weighted vacuum mass has been paid,
the SQUARED baseline in the physical root can be absorbed without
an additional unproved source factor. -/
theorem source_original_signed_Schur_baseline_squared_budget434
    (b G Vac P S0 : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hG : 0 ≤ G) (hVac : 0 ≤ Vac)
    (hPrefix : P ≤ G * Vac) (hInit : b * Vac ≤ S0) :
    b^2 * P ≤ G * S0 := by
  calc
    b^2 * P ≤ b^2 * (G * Vac) :=
      mul_le_mul_of_nonneg_left hPrefix (sq_nonneg _)
    _ = G * (b * (b * Vac)) := by ring
    _ ≤ G * (b * Vac) := by
      apply mul_le_mul_of_nonneg_left _ hG
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hb1 (mul_nonneg hb0 hVac))
    _ ≤ G * S0 := mul_le_mul_of_nonneg_left hInit hG
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedPhysicalSchurSquared -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 23000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The EXACT chronological sum of finite CLEAN Schur products is
nonnegative. It is not asserted to be uniformly bounded. -/
theorem source_original_ACTUAL_physical_CLEAN_Schur_sum_nonneg434
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    0 ≤ sourceOriginalActualPhysicalCLEANSchurSum434
      SP sm BP bm J ell m cap patterns
      q rho Vs Vb K zeta theta k R T := by
  unfold sourceOriginalActualPhysicalCLEANSchurSum434
  dsimp only
  exact Finset.sum_nonneg (fun j hj =>
    source_original_SIGNED_prefix_Schur_gain_chain_nonneg434
      _ _ j 0)

/-- Nonnegativity of ORIGINAL initial vacuum Fock energy, with real
positive Haar and tilted BIG masses, no normalized-mass premise. -/
theorem source_original_ACTUAL_physical_initial_vacuum_energy_nonneg434
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p) :
    0 ≤ sourceOriginalActualPhysicalInitialVacuumEnergy434
      SP sm BP bm J ell cap Vs mu := by
  unfold sourceOriginalActualPhysicalInitialVacuumEnergy434
  apply Finset.sum_nonneg
  intro y hy
  have hOrb :
      y.val ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap :=
    (Finset.mem_filter.mp y.property).1
  exact mul_nonneg
    (physicalOrbitMass_pos SP sm BP bm (J+ell) cap
      Vs mu hVs hmu y.val hOrb).le (sq_nonneg _)

/-- DIRTY output energy is an explicit finite sum of nonnegative
squares against the authentic Fock/OLD joint density. -/
theorem source_original_ACTUAL_physical_DIRTY_target_energy_nonneg434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    0 ≤ (sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs Vb K zeta theta k R T).2 := by
  unfold sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
    sourceOriginalSignedDIRTYTargetEnergySum434
    sourceOriginalSignedJointForwardEnergy434
  dsimp only
  exact Finset.sum_nonneg (fun j hj =>
    Finset.sum_nonneg (fun a ha => sq_nonneg _))

/-- FULL true signed first-DIRTY physical root, with baseline paid by
literal initial BIG distinctness/harmonic law and no duplicate history
factor, bounded by: (actual CLEAN Schur growth) ×
(original SMALL marked boundary) × (actual signed DIRTY L² energy).
This is finite, not yet an asymptotic polynomial or log saving. -/
theorem source_original_ACTUAL_PHYSICAL_signed_DIRTY_Schur_SMALL_squared434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=Vb g)
    (K : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g p,0 < physicalSourceBaseline BP bm q (2*R) g p)
    (hb1 : ∀ g p,physicalSourceBaseline BP bm q (2*R) g p ≤ 1) :
    ‖sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns q rho Vs Vb K zeta theta k R T‖^2 ≤
    sourceOriginalActualPhysicalCLEANSchurSum434
      SP sm BP bm J ell m cap patterns
      q rho Vs Vb K zeta theta k R T *
    (∏ g : SG,((Fintype.card (SP g):ℝ)/Vs g)^(J+ell)) *
    (sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs Vb K zeta theta k R T).2 := by
  classical
  let b : ℝ := ‖(physicalSourceBaselineProduct BP bm q (2*R):ℂ)‖
  let G := sourceOriginalActualPhysicalCLEANSchurSum434
    SP sm BP bm J ell m cap patterns q rho Vs Vb K zeta theta k R T
  let Vac := sourceOriginalActualPhysicalInitialVacuumEnergy434
    SP sm BP bm J ell cap Vs
    (physicalSourceMuTilde BP bm q (2*R) Vb)
  let Pair := sourceOriginalActualPhysicalSignedDIRTYEnergyPair434
    SP sm BP bm J ell m cap patterns hcap q rho Vs Vb K zeta theta k R T
  let S0 : ℝ :=
    ∏ g : SG,((Fintype.card (SP g):ℝ)/Vs g)^(J+ell)
  have hmu (g : BG) (p : BP g) :
      0 < physicalSourceMuTilde BP bm q (2*R) Vb g p := by
    have hp : (0:ℝ) < (bm g p:ℝ) := Nat.cast_pos.mpr (NeZero.pos (bm g p))
    have hv : 0 < Vb g := hVb g
    have hbp := hb g p
    dsimp only [physicalSourceMuTilde]
    positivity
  have hb0 : 0 ≤ b := norm_nonneg _
  have hbLe : b ≤ 1 :=
    source_original_ACTUAL_physical_baseline_norm_le_one434
      BP bm q (2*R) hb hb1
  have hG : 0 ≤ G :=
    source_original_ACTUAL_physical_CLEAN_Schur_sum_nonneg434
      SP sm BP bm J ell m cap patterns q rho Vs Vb K zeta theta k R T
  have hVac : 0 ≤ Vac :=
    source_original_ACTUAL_physical_initial_vacuum_energy_nonneg434
      SP sm BP bm J ell cap Vs hVs
      (physicalSourceMuTilde BP bm q (2*R) Vb) hmu
  have hPre : Pair.1 ≤ G * Vac :=
    source_original_ACTUAL_physical_CLEAN_prefix_Schur434
      SP sm BP bm J ell m cap patterns
      hcap q rho Vs Vb hVs hVb K zeta theta k R T hmu
  have hInitial : b * Vac ≤ S0 :=
    source_original_ACTUAL_physical_initial_Schur_mass_budget434
      SP sm BP bm J ell cap q Vs hVs Vb hVb
      hHarmonic R hb hb1
  have hBP : b^2 * Pair.1 ≤ G * S0 :=
    source_original_signed_Schur_baseline_squared_budget434
      b G Vac Pair.1 S0 hb0 hbLe hG hVac hPre hInitial
  have hT : 0 ≤ Pair.2 :=
    source_original_ACTUAL_physical_DIRTY_target_energy_nonneg434
      SP sm BP bm J ell m cap patterns hcap
      q rho Vs Vb K zeta theta k R T
  have hRoot := source_original_ACTUAL_PHYSICAL_signed_DIRTY_root_energy434
    SP sm BP bm J ell m cap patterns
    hi hcap q rho Vs Vb hVs hVb K zeta theta k R T hmu
  change ‖sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns q rho Vs Vb K zeta theta k R T‖^2 ≤
    G * S0 * Pair.2
  calc
    _ ≤ b^2 * Pair.1 * Pair.2 := hRoot
    _ ≤ (G * S0) * Pair.2 :=
      mul_le_mul_of_nonneg_right hBP hT
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedInitialPrefixBudget -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)

/-- Under the original finite BIG harmonic law, positivity of
the source baseline and its bound by 1, the TRUE signed initial
dual CLEAN-prefix energy with its complete physical baseline is
bounded by the EXACT SMALL Haar total mass. No artificial
history factor, Fock dimension or BIG-active cost. -/
theorem source_original_ACTUAL_initial_signed_prefix_budget434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
    (R : ℕ)
    (hb : ∀ g p,0 < physicalSourceBaseline BP bm q (2*R) g p)
    (hb1 : ∀ g p,physicalSourceBaseline BP bm q (2*R) g p ≤ 1) :
    ‖(physicalSourceBaselineProduct BP bm q (2*R):ℂ)‖ *
      sourceOriginalActualSignedTruePrefixEnergy434
        SP sm BP bm J ell cap Vs V
        (physicalSourceMuTilde BP bm q (2*R) V)
        (sourceOriginalActualSignedInitialWeight434
          SP sm BP bm J ell cap hcap Vs
          (physicalSourceMuTilde BP bm q (2*R) V)) ≤
      ∑ s : GroupState SP sm (J+ell),
        groupStateMass SP sm (J+ell) Vs := by
  have hmu (g : BG) (p : BP g) :
      0 < physicalSourceMuTilde BP bm q (2*R) V g p := by
    have hp : 0 < (bm g p:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    unfold physicalSourceMuTilde
    apply one_div_pos.mpr
    exact mul_pos (mul_pos (hV g) hp) (hb g p)
  rw [source_original_ACTUAL_initial_signed_dual_energy_good_mass434
    SP sm BP bm J ell cap hcap Vs V
    (physicalSourceMuTilde BP bm q (2*R) V) hVs hV hmu]
  have hMass := source_original_ACTUAL_initial_mass_eq_signed_good_mass434
    SP sm BP bm J ell cap q Vs V R hVs hmu
  rw [←hMass]
  exact source_original_ACTUAL_initial_mass_le_SMALL_mass434
    SP sm BP bm J ell cap q Vs hVs V hV
    hHarmonic R hb hb1
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceBirthSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Literal source S/Ts/Tb specialization of the already established root.
All SMALL and BIG prime nonzero instances follow from the original primes. -/
def sourceOriginalActualSourceBirthTail434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 β m → ℝ) (xi zeta theta : ℝ)
    (k : ℤ) (R H : ℕ) : ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  letI (g : Option ι) (p : {p : ℕ // p ∈ P g}) : NeZero p.val :=
    ⟨(source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property |>.ne_zero⟩
  letI (g : β) (p : {p : ℕ // p ∈ u.Tb g}) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  exact sourceOriginalBackgroundBirthTailMemoryRoot434
    (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
    (fun g => {p : ℕ // p ∈ u.Tb g}) (fun _ p => p.val) J ell m
    (fun g => Fintype.card {p : ℕ // p ∈ u.Tb g})
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    cfg.q0 H (sourceOriginalActualSmallMass434 u) u.Vbig
    (sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig blockA blockB
      J ell m hmJ Q hA hB xi) zeta theta k R

/-- Actual source birth tail has arbitrary fixed logarithmic saving.
J and every polynomial exponent are fixed BEFORE the threshold. The
original physical hypotheses (BIG distinctness, harmonic normalization,
lower prime scale) remain explicit; no M, alphabet or operator cap is added. -/
theorem eventually_source_original_ACTUAL_SOURCE_birth_tail_saving434
    (cfg : SourceComparisonFixed434) (J ell m Cq Cxi : ℕ) (hmJ : m ≤ J)
    (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
      {x Y Hp : ℝ} (u : SourceComparisonData434 ι β cfg x L Y Hp)
      (hi : Function.Injective
        (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ u.Tb g},1/(p.val:ℝ)=u.Vbig g)
      (hmin : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
        Real.exp (L^cfg.cexp) ≤ (p.val:ℝ))
      (blockA blockB : Finset β) (Q : ℕ) (hQ : (Q:ℝ) ≤ L^Cq)
      (hA hB : SourceOriginalProbePattern434 β m → ℝ) (xi : ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi) (zeta theta : ℝ) (k : ℤ),
      ‖sourceOriginalActualSourceBirthTail434 u blockA blockB J ell m hmJ Q hA hB
        xi zeta theta k (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2/4))‖ ≤ L^(-B) := by
  let Cb : ℝ := 16*max 1 cfg.vmin⁻¹
  let Enu : ℝ := (m:ℝ)*(2*cfg.C0)*Real.log 2+((4*Cq+2*Cxi:ℕ):ℝ)+1
  let Es : ℝ := sourceOriginalB26SmallNormExponent434
    ell (Real.sqrt cfg.q0) cfg.vmin (cfg.C0+1)
  let CE : ℝ := Enu+Es
  have hCG : 0 ≤ cfg.C0 := cfg.hC0
  have hCS : 0 ≤ cfg.C0+1 := by linarith [cfg.hC0]
  have hCb : 1 ≤ Cb := by
    have hh := le_max_left (1:ℝ) cfg.vmin⁻¹
    dsimp only [Cb]
    linarith
  have hEnu : 0 ≤ Enu := by
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [Enu]
    positivity
  have hEs : 0 ≤ Es :=
    source_original_B26_small_norm_exponent_nonneg434
      ell (Real.sqrt cfg.q0) cfg.vmin (cfg.C0+1) hCS
  have hCE : 0 ≤ CE := add_nonneg hEnu hEs
  have hc : 0 < cfg.cexp := (cfg.haexp.trans cfg.hab).trans cfg.hbc
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (Real.exp 1),
    eventually_source_original_ACTUAL_SMALL_source_boundary434 cfg J ell,
    eventually_source_original_ACTUAL_RAW_COMPARISON_root_explicit_birth_cost434
      cfg.cexp cfg.vmin hc cfg.hv,
    eventually_source_original_ACTUAL_full_birth_cost_budget434
      Cb cfg.C0 CE (cfg.C0+1) cfg.vmin B hCb cfg.hC0 hCE hCS cfg.hv hB (ell+m)]
      with L hL he hSmall hRoot hBudget
  intro ι β _ _ _ _ x Y Hp u hi hHarmonic hmin blockA blockB Q hQ hA hB hhxi
    hhA hhB hxi hXi zeta theta k
  let xi := hhxi
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) he
    simpa using hh
  let P := sourceOriginalActualSmallPrimeSets434 u
  let Vs := sourceOriginalActualSmallMass434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  have hsb := source_original_ACTUAL_SMALL_source_bounds434 u
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨(hsb.1 g p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  have hVs (g : Option ι) : 0 < Vs g := cfg.hv.trans_le (hsb.2.2 g)
  have hmax (g : β) (p : BP g) : (p.val:ℝ) ≤ Real.exp (Real.sqrt L) := by
    apply u.hGroup
    rw [u.hG]
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,p.property⟩))
  have hBlock : (((blockA.card+blockB.card):ℕ):ℝ) ≤ (2*cfg.C0)*Real.log L := by
    have ha : (blockA.card:ℝ) ≤ (Fintype.card β:ℝ) := by
      exact_mod_cast Finset.card_le_univ blockA
    have hb : (blockB.card:ℝ) ≤ (Fintype.card β:ℝ) := by
      exact_mod_cast Finset.card_le_univ blockB
    push_cast
    nlinarith only [ha,hb,u.hBigGroups]
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let H := Nat.ceil (L^2/4)
  let S0 : ℝ := ∏ g : Option ι,((Fintype.card (SP g):ℝ)/Vs g)^(J+ell)
  let Cnu : ℝ := ∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
    sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu
  let Cs : ℝ := ∏ g : Option ι,memorySmallRowConstant cfg.q0 (Vs g) ell
  let E0 : ℝ := Real.exp ((cfg.C0+1)*L*Real.log L*
    (Real.sqrt L+Real.log (max 1 cfg.vmin⁻¹)))
  let G0 : ℝ := Real.exp (4*((N+1:ℕ):ℝ)*(1+Real.sqrt L))
  let F : ℝ := Cb*Real.exp (Real.sqrt L)
  have hF : 0 ≤ F := mul_nonneg (zero_le_one.trans hCb) (Real.exp_pos _).le
  have hnu : Cnu ≤ L^Enu :=
    source_original_memory_RAW_COMPARISON_cap_budget434 blockA blockB m Q
      L (2*cfg.C0) xi Cq Cxi hL (by positivity) hxi hBlock hQ hXi
  have hcs : Cs ≤ L^Es :=
    source_original_memory_SMALL_absolute_row_polynomial434 ell cfg.q0 cfg.vmin
      (cfg.C0+1) L cfg.hq0 cfg.hq1 cfg.hv hCS hL1 Vs hsb.2.2
      (source_original_ACTUAL_SMALL_group_count434 u hlog)
  have hnu0 : 0 ≤ Cnu := Finset.sum_nonneg
    (fun nu _ => source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi nu)
  have hcs0 : 0 ≤ Cs := by
    have hs : 0 < 1-Real.sqrt cfg.q0 := by
      nlinarith only [Real.sq_sqrt cfg.hq0.le,Real.sqrt_nonneg cfg.q0,cfg.hq1]
    apply Finset.prod_nonneg
    intro g hg
    have hv := hVs g
    dsimp only [memorySmallRowConstant]
    positivity
  have hpoly : Cnu*Cs ≤ L^CE := by
    calc
      _ ≤ L^Enu*L^Es := mul_le_mul hnu hcs hcs0 (Real.rpow_nonneg hLp.le _)
      _ = _ := by rw [←Real.rpow_add hLp]
  have hS0 : S0 ≤ E0 := by
    simpa only [S0,SP,Vs,P,Fintype.card_coe,E0] using hSmall u
  have hS00 : 0 ≤ S0 := Finset.prod_nonneg
    (fun g _ => pow_nonneg (div_nonneg (Nat.cast_nonneg _) (hVs g).le) _)
  have hPow : (Cnu*Cs*F^((ell+m)*Fintype.card β))^N ≤
      (L^CE*F^((ell+m)*Fintype.card β))^N :=
    pow_le_pow_left₀ (mul_nonneg (mul_nonneg hnu0 hcs0) (pow_nonneg hF _))
      (mul_le_mul_of_nonneg_right hpoly (pow_nonneg hF _)) N
  have hSource := hRoot SP (fun _ p => p.val) u.Tb hi cfg.q0 cfg.hq0 cfg.hq1 Vs hVs
    u.Vbig u.hVbig hHarmonic hmin hmax blockA blockB J ell m hmJ Q hA hB xi
    hhA hhB hxi zeta theta k 2 (by norm_num) H
  have hSource' :
      ‖sourceOriginalActualSourceBirthTail434 u blockA blockB J ell m hmJ Q hA hB
        xi zeta theta k (Nat.ceil (L^(0.52:ℝ))) H‖ ≤
      ((2:ℝ)^H)⁻¹*S0*(G0*(Cnu*Cs*F^((ell+m)*Fintype.card β))^N) := by
    convert hSource using 1 <;>
      simp only [sourceOriginalActualSourceBirthTail434,P,SP,Vs,N,H,S0,G0,Cnu,Cs,F,Cb] <;>
      congr 2 <;> push_cast <;> ring
  have hFinal := hBudget (Fintype.card β) u.hBigGroups
  apply hSource'.trans
  calc
    _ ≤ ((2:ℝ)^H)⁻¹*E0*(G0*(L^CE*F^((ell+m)*Fintype.card β))^N) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hS0 (by positivity)
      · exact mul_le_mul_of_nonneg_left hPow (Real.exp_pos _).le
      · exact mul_nonneg (Real.exp_pos _).le
          (pow_nonneg (mul_nonneg (mul_nonneg hnu0 hcs0) (pow_nonneg hF _)) _)
      · positivity
    _ = ((2:ℝ)^H)⁻¹*E0*G0*
        F^((ell+m)*Fintype.card β*N)*L^(CE*(N:ℝ)) := by
      rw [mul_pow,←pow_mul]
      have hp : (L^CE)^N=L^(CE*(N:ℝ)) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hLp.le]
      rw [hp]
      ring
    _ ≤ L^(-B) := by
      simpa only [H,E0,G0,F,N,Cb] using hFinal
end Green64Analytic.CorrelationSquare

end

end

