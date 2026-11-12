module

public import Green64.Library.Weights.Part094
public import Green64.Library.Weights.Part091
public import Green64.Library.Weights.Part093
public import Green64.Library.Analysis.Estimates.Part013

@[expose] public section

/-!
# Correlation / Part063

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredPhysicalSectors -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Out" => FullPhysicalOutput SP sm BP bm (J+ell)
local notation "Sector" => SourceOriginalMarkedSectorIndex434 BP cap
local notation "A" => SourceOriginalB26Active434 BP J ell

def sourceOriginalUnfilteredPhysicalOrderedEnergy434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (U : State → ℂ) : ℝ :=
  ∑ x : State,fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x*‖U x‖^2

/-- Exact sum of all physical OLD sectors, retaining every repeated atom and factorial. -/
theorem source_original_physical_ORDERED_ENERGY_SECTORS434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (U : State → ℂ) :
    sourceOriginalUnfilteredPhysicalOrderedEnergy434 SP sm BP bm J ell cap Vs mu U =
    ∑ d : Sector,sourceOriginalB26SectorEnergy434 SP sm BP bm J ell cap
      (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 Vs mu
      (sourceOriginalB26SourcePullback434 SP sm BP bm J ell cap
        (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 U) := by
  unfold sourceOriginalUnfilteredPhysicalOrderedEnergy434
  rw [source_original_MARKED_full_sector_sum434 SP sm BP bm J ell cap]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Fintype.sum_prod_type]
  unfold sourceOriginalB26SectorEnergy434 sourceOriginalB26SourcePullback434
  conv_lhs =>
    arg 2
    ext xs
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  rfl

/-- Exact ordered-to-orbit energy identity in the original density. -/
theorem source_original_physical_ORDERED_ORBIT_ENERGY434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (F : Out → ℂ) :
    sourceOriginalUnfilteredPhysicalOrderedEnergy434 SP sm BP bm J ell cap Vs mu
      (fun x => F (physicalFockProjection SP sm BP bm (J+ell) cap x)) =
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  let project := physicalFockProjection SP sm BP bm (J+ell) cap
  unfold sourceOriginalUnfilteredPhysicalOrderedEnergy434
    sourceOriginalUnfilteredIdealOrbitEnergy434 physicalOrbitMass
  simp only [Finset.sum_mul,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hx : project x ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap :=
    Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  rw [Finset.sum_eq_single (project x)]
  · simp only [project,ite_true]
  · intro y _ hn
    rw [if_neg (Ne.symm hn),zero_mul]
  · intro h; exact (h hx).elim

theorem source_original_physical_ordered_energy_nonneg434
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p) (U : State → ℂ) :
    0 ≤ sourceOriginalUnfilteredPhysicalOrderedEnergy434 SP sm BP bm J ell cap Vs mu U := by
  exact Finset.sum_nonneg (fun x _ =>
    mul_nonneg (fullPhysicalMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu x).le (sq_nonneg _))

theorem source_original_physical_orbit_energy_nonneg434
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p) (F : Out → ℂ) :
    0 ≤ sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  rw [← source_original_physical_ORDERED_ORBIT_ENERGY434]
  exact source_original_physical_ordered_energy_nonneg434 SP sm BP bm J ell cap Vs hVs mu hmu _

variable (m : ℕ) {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- The local seen-erased row is exactly the sum of literal target-filtered CLEAN sectors. -/
theorem source_original_physical_ORDERED_PAIR_SECTORS434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ) (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (U : State → ℂ) (F : Out → ℂ) :
    physicalOrderedInner SP sm BP bm (J+ell) cap Vs mu U
      (fun x => sourceOriginalUnfilteredIdealLocalClean434 SP sm BP bm J ell m cap patterns
        q 1 Vs V mu K zeta theta o k x F) =
    ∑ d : Sector,sourceOriginalB26LiteralSectorCleanPair434 SP sm BP bm J ell m cap
      (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 patterns
      mu V (sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m patterns
        (memoryOrientationK BP J ell m patterns K o)) q Vs zeta theta o k U F := by
  unfold physicalOrderedInner
  rw [source_original_MARKED_full_sector_sum434 SP sm BP bm J ell cap]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Fintype.sum_prod_type,source_original_unfiltered_ideal_LOCAL_CLEAN_AS_TARGET_K434]
  unfold sourceOriginalB26LiteralSectorCleanPair434
  conv_lhs =>
    arg 2
    ext xs
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  rfl

/-- Full physical ordered pairing from arbitrary-K BIG saving.
This finite transfer lemma has an explicit BIG premise; the final eventual theorem discharges it.
There is no sector-count, Fock-size, OLD multiplicity or Fourier-cardinality loss. -/
theorem source_original_physical_ORDERED_PAIR_TRANSFER434
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (V : BG → ℝ) (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (eps : ℝ) (heps : 0 ≤ eps)
    (hBig : ∀ (d : ℕ),0 < d → ∀ (t : ℝ) (u v : A → ℂ),
      ‖sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m patterns mu V
        (sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m patterns
          (memoryOrientationK BP J ell m patterns K o)) d zeta t o k u v‖^2 ≤
      eps*sourceOriginalB26ActiveEnergy434 BP J ell mu u*sourceOriginalB26ActiveEnergy434 BP J ell mu v)
    (U : State → ℂ) (F : Out → ℂ) :
    ‖physicalOrderedInner SP sm BP bm (J+ell) cap Vs mu U
      (fun x => sourceOriginalUnfilteredIdealLocalClean434 SP sm BP bm J ell m cap patterns
        q 1 Vs V mu K zeta theta o k x F)‖^2 ≤
    eps*(memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2*
      sourceOriginalUnfilteredPhysicalOrderedEnergy434 SP sm BP bm J ell cap Vs mu U*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  let ND := sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m patterns
    (memoryOrientationK BP J ell m patterns K o)
  let EU := fun d : Sector => sourceOriginalB26SectorEnergy434 SP sm BP bm J ell cap
    (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 Vs mu
    (sourceOriginalB26SourcePullback434 SP sm BP bm J ell cap
      (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 U)
  let EF := fun d : Sector => sourceOriginalB26SectorEnergy434 SP sm BP bm J ell cap
    (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 Vs mu
    (sourceOriginalB26TargetPullback434 SP sm BP bm J ell cap
      (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 F)
  let z := fun d : Sector => sourceOriginalB26LiteralSectorCleanPair434 SP sm BP bm J ell m cap
    (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 patterns
    mu V ND q Vs zeta theta o k U F
  let C := eps*(memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2
  have hC : 0 ≤ C := mul_nonneg heps (sq_nonneg _)
  have hSector (d : Sector) : ‖z d‖^2 ≤ C*EU d*EF d :=
    source_original_unfiltered_ideal_LITERAL_SECTOR_TRANSFER434 SP sm BP bm J ell m cap
      (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 patterns mu hmu V ND
      q hq hq1 Vs hVs zeta theta o k eps heps hBig U F
  have hEnergyNonneg (d : Sector)
      (f : GroupState SP sm (J+ell) → A → SourceOriginalMarkedSectorOld434 BP bm cap d → ℂ) :
      0 ≤ sourceOriginalB26SectorEnergy434 SP sm BP bm J ell cap
        (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 Vs mu f := by
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro xs _
    apply Finset.sum_nonneg
    intro t _
    apply mul_nonneg _ (sq_nonneg _)
    exact (fullPhysicalMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu
      (sourceOriginalMarkedSectorEmbed434 SP sm BP bm J ell cap d xs a t)).le
  have hb := source_original_B26_homogeneous_shared_integration434
    (fun _d : Sector => (1:ℝ)) EU EF z C (fun _ => zero_le_one)
    (fun d => hEnergyNonneg d _) (fun d => hEnergyNonneg d _) hC hSector
  simp only [Complex.ofReal_one,one_mul] at hb
  have hEU : (∑ d : Sector,EU d) =
      sourceOriginalUnfilteredPhysicalOrderedEnergy434 SP sm BP bm J ell cap Vs mu U :=
    (source_original_physical_ORDERED_ENERGY_SECTORS434 SP sm BP bm J ell cap Vs mu U).symm
  have hEF : (∑ d : Sector,EF d) =
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
    rw [← source_original_physical_ORDERED_ORBIT_ENERGY434,
      source_original_physical_ORDERED_ENERGY_SECTORS434]
    rfl
  rw [hEU,hEF] at hb
  rw [source_original_physical_ORDERED_PAIR_SECTORS434]
  exact hb
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredPhysicalOrbit -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Out" => FullPhysicalOutput SP sm BP bm (J+ell)
local notation "A" => SourceOriginalB26Active434 BP J ell

theorem source_original_physical_ORBIT_MASK_ENERGY434
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (gate : Out → Prop) (F : Out → ℂ) :
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (fun X => if gate X then F X else 0) ≤
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  unfold sourceOriginalUnfilteredIdealOrbitEnergy434
  apply Finset.sum_le_sum
  intro X hX
  by_cases h : gate X
  · simp only [if_pos h,le_refl]
  · simp only [if_neg h,norm_zero,zero_pow (by decide : 2≠0),mul_zero]
    exact mul_nonneg (physicalOrbitMass_pos SP sm BP bm (J+ell) cap Vs mu hVs hmu X hX).le
      (sq_nonneg _)

theorem source_original_physical_ORBIT_SELF_PAIR434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (F : Out → ℂ) :
    physicalSymmetricInner SP sm BP bm (J+ell) cap Vs mu F F =
    (sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F:ℂ) := by
  unfold physicalSymmetricInner sourceOriginalUnfilteredIdealOrbitEnergy434
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro X _
  rw [Complex.ofReal_mul,mul_assoc]
  congr 1
  simpa only [Complex.star_def,Complex.normSq_eq_norm_sq] using
    (Complex.normSq_eq_conj_mul_self (z := F X)).symm

variable (m : ℕ) {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Both OLD gates move exactly to the two endpoint tests in the weighted orbit pairing. -/
theorem source_original_physical_GATED_ORBIT_PAIR434
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (V : BG → ℝ) (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (T : ℕ) (zeta theta : ℝ) (o k : ℤ) (U F : Out → ℂ) :
    physicalSymmetricInner SP sm BP bm (J+ell) cap Vs mu U
      (sourceOriginalUnfilteredIdealSeenErasedClean434 SP sm BP bm J ell m cap patterns
        q 1 Vs V mu K T zeta theta o k F) =
    physicalOrderedInner SP sm BP bm (J+ell) cap Vs mu
      (fun x => if sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
        (physicalFockProjection SP sm BP bm (J+ell) cap x)
        then U (physicalFockProjection SP sm BP bm (J+ell) cap x) else 0)
      (fun x => sourceOriginalUnfilteredIdealLocalClean434 SP sm BP bm J ell m cap patterns
        q 1 Vs V mu K zeta theta o k x
          (fun Y => if sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T Y then F Y else 0)) := by
  unfold sourceOriginalUnfilteredIdealSeenErasedClean434
  rw [fullPhysicalOrbitAverage_pairing SP sm BP bm (J+ell) cap Vs mu hVs hmu]
  unfold physicalOrderedInner
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  split_ifs <;> simp only [star_zero,mul_zero,zero_mul]

/-- Exact finite physical orbit transfer. The explicit BIG bound will be discharged
by the eventual original source theorem; all quotient/sector/gate estimates here are proved. -/
theorem source_original_physical_ORBIT_TRANSFER434
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (V : BG → ℝ) (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (T : ℕ) (zeta theta : ℝ) (o k : ℤ) (eps : ℝ) (heps : 0 ≤ eps)
    (hBig : ∀ (d : ℕ),0 < d → ∀ (t : ℝ) (u v : A → ℂ),
      ‖sourceOriginalUnfilteredPhysicalPair434 BP bm J ell m patterns mu V
        (sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m patterns
          (memoryOrientationK BP J ell m patterns K o)) d zeta t o k u v‖^2 ≤
      eps*sourceOriginalB26ActiveEnergy434 BP J ell mu u*sourceOriginalB26ActiveEnergy434 BP J ell mu v)
    (rho : ℝ) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) (F : Out → ℂ) :
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
      (sourceOriginalUnfilteredIdealSeenErasedClean434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K T zeta theta o k F) ≤
    eps*(memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2*
      sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu F := by
  let Energy := sourceOriginalUnfilteredIdealOrbitEnergy434 SP sm BP bm J ell cap Vs mu
  let C := eps*(memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2
  have hC : 0 ≤ C := mul_nonneg heps (sq_nonneg _)
  let gate := sourceOriginalUnfilteredIdealOLD434 SP sm BP bm J ell T
  let mask := fun f : Out → ℂ => fun X => if gate X then f X else 0
  let E1 := sourceOriginalUnfilteredIdealSeenErasedClean434 SP sm BP bm J ell m cap patterns
    q 1 Vs V mu K T zeta theta o k
  have hEnergy (f : Out → ℂ) : 0 ≤ Energy f :=
    source_original_physical_orbit_energy_nonneg434 SP sm BP bm J ell cap Vs hVs mu hmu f
  have hMask (f : Out → ℂ) : Energy (mask f) ≤ Energy f :=
    source_original_physical_ORBIT_MASK_ENERGY434 SP sm BP bm J ell cap Vs hVs mu hmu gate f
  have hpair (u f : Out → ℂ) :
      ‖physicalSymmetricInner SP sm BP bm (J+ell) cap Vs mu u (E1 f)‖^2 ≤
      C*Energy u*Energy f := by
    rw [source_original_physical_GATED_ORBIT_PAIR434 SP sm BP bm J ell cap m patterns
      mu hmu V K q Vs hVs T zeta theta o k u f]
    have hb := source_original_physical_ORDERED_PAIR_TRANSFER434 SP sm BP bm J ell cap m
      patterns mu hmu V K q hq hq1 Vs hVs zeta theta o k eps heps hBig
      (fun x => mask u (physicalFockProjection SP sm BP bm (J+ell) cap x)) (mask f)
    rw [source_original_physical_ORDERED_ORBIT_ENERGY434] at hb
    change _ ≤ C*Energy (mask u)*Energy (mask f) at hb
    have hprod := mul_le_mul (hMask u) (hMask f) (hEnergy (mask f)) (hEnergy u)
    have hprodC := mul_le_mul_of_nonneg_left hprod hC
    calc
      _ ≤ C*Energy (mask u)*Energy (mask f) := hb
      _ ≤ C*Energy u*Energy f := by nlinarith only [hprodC]
  have hnorm (f : Out → ℂ) : Energy (E1 f) ≤ C*Energy f := by
    have hb := hpair (E1 f) f
    rw [source_original_physical_ORBIT_SELF_PAIR434 SP sm BP bm J ell cap Vs mu] at hb
    change ‖(Energy (E1 f):ℂ)‖^2 ≤ C*Energy (E1 f)*Energy f at hb
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hEnergy _)] at hb
    by_cases hzero : Energy (E1 f)=0
    · rw [hzero]; exact mul_nonneg hC (hEnergy f)
    · have hp : 0 < Energy (E1 f) := lt_of_le_of_ne (hEnergy _) (Ne.symm hzero)
      by_contra hh
      have hp2 := mul_pos hp (sub_pos.mpr (lt_of_not_ge hh))
      nlinarith only [hb,hp2]
  let damp := fun f : Out → ℂ => fun X =>
    sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho X*f X
  have hdamp (f : Out → ℂ) : Energy (damp f) ≤ Energy f :=
    source_original_unfiltered_ideal_ORBIT_DAMPING_ENERGY434 SP sm BP bm J ell cap
      rho hr0 hr1 Vs hVs mu hmu f
  have heq :
      sourceOriginalUnfilteredIdealSeenErasedClean434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K T zeta theta o k F = damp (E1 (damp F)) := by
    funext X
    exact source_original_unfiltered_ideal_SEEN_ERASED_RHO434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K T zeta theta o k F X
  change Energy _ ≤ C*Energy F
  rw [heq]
  exact (hdamp _).trans ((hnorm _).trans (mul_le_mul_of_nonneg_left (hdamp F) hC))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredPhysicalQuantitative -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Absorb the actual SMALL conditioning budget with precision chosen before J. -/
theorem source_original_physical_ABSORB_SMALL434
    (L E Cs C : ℝ) (hL : 3 ≤ L) (hC : 0 ≤ C) (hCap : C ≤ L^Cs) :
    9*L^(-(2*(E+Cs+1)))*C^2 ≤ L^(-(2*E)) := by
  have hLp : 0 < L := by linarith
  have h9 : (9:ℝ) ≤ L^2 := by nlinarith
  calc
    _ ≤ 9*L^(-(2*(E+Cs+1)))*(L^Cs)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC hCap 2)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hLp.le _))
    _ ≤ L^2*L^(-(2*(E+Cs+1)))*(L^Cs)^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h9 (Real.rpow_nonneg hLp.le _)) (sq_nonneg _)
    _ = L^(-(2*E)) := by
      rw [← Real.rpow_two,← Real.rpow_two,← Real.rpow_mul hLp.le,
        ← Real.rpow_add hLp,← Real.rpow_add hLp]
      congr 1
      ring

/-- Main physical result: arbitrary negative log-power squared norm for the
literal derived seen-erased CLEAN, on its actual FULL physical orbit energy.
The original distinguished S and all Ts are the independent SMALL carrier;
ell=1 and q=cfg.q0. RAW-none and all canonical comparison terms retain their
signs. Both OLD gates, target numerical fresh LIST Nodup after full orientation,
repeated OLD atoms, all physical weights and endpoint/orbit means are literal.
There is no analytic RMS, collision, norm or contraction premise.

Quantifier order: cfg and E -> Cs -> E0 -> m and precisions -> fixed J -> L.
Only global seen-disjointness is erased; restoring it is a separate root debt. -/
theorem eventually_source_original_physical_FULL_SEEN_ERASED_CLEAN434
    (cfg : SourceComparisonFixed434)
    (gamma dscale E Cfreq c : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale) (hE : 0 < E) (hc : 0 < c) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi : ℕ), 1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
    ∀ (J : ℕ) (hmJ : m ≤ J),
    ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}), NeZero p.val]
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g, data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g, loB g ≤ hiB g)
      (hBigUpper : ∀ g, (hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g, Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g, ∀ p ∈ data.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, data.Vbig g = ∑ p ∈ data.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (hcountA : c*Real.log L ≤ (blockA.card:ℝ))
      (hcountB : c*Real.log L ≤ (blockB.card:ℝ))
      (zeta theta : ℝ) (hZeta : |zeta| ≤ L^Cfreq)
      (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
      (cap : G → ℕ) (T : ℕ) (rho : ℝ) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1)
      (F : FullPhysicalOutput
        (fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g})
        (fun _ p => p.val) (fun g : G => {p : ℕ // p ∈ data.Tb g})
        (fun _ p => p.val) (J+1) → ℂ),
    let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
    let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
    letI : ∀ (g : Option ι) (p : SP g),NeZero p.val := fun g p =>
      ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
    let Vs := sourceOriginalActualSmallMass434 data
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) cfg.q0
      (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
    sourceOriginalUnfilteredIdealOrbitEnergy434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 cap Vs mu
      (sourceOriginalUnfilteredIdealSeenErasedClean434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m cap pats cfg.q0 rho Vs data.Vbig mu K T zeta theta o k F) ≤
    L^(-(2*E))*sourceOriginalUnfilteredIdealOrbitEnergy434
      SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 cap Vs mu F := by
  let Cs := sourceOriginalB26SmallNormExponent434 1 cfg.q0 cfg.vmin (cfg.C0+1)
  have hC0 : 0 ≤ cfg.C0+1 := by linarith [cfg.hC0]
  have hCs : 0 ≤ Cs := source_original_B26_small_norm_exponent_nonneg434
    1 cfg.q0 cfg.vmin (cfg.C0+1) hC0
  let E0 := E+Cs+1
  have hE0 : 0 < E0 := by dsimp [E0]; linarith
  obtain ⟨m,D,HH,Cq,Cxi,hm,hD,hHH,hMain⟩ :=
    eventually_source_original_physical_FULL_TILTED_NODUP_BIG434
      cfg gamma dscale E0 Cfreq c hgamma hd hE0 hc
  refine ⟨m,D,HH,Cq,Cxi,hm,hD,hHH,?_⟩
  intro J hmJ
  have hcexp : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [hMain J 1 hmJ (by omega),
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hcexp,
    eventually_ge_atTop (3:ℝ),eventually_ge_atTop (Real.exp 1)]
    with L hMain hVisit hL3 hLe
  dsimp only at hMain ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hMain⟩ := hMain
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data instNZ
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hBlocks hcountA hcountB zeta theta hZeta o k ho hk cap T rho hr0 hr1 F
  let SP := fun g : Option ι => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 data g}
  let sm : (g : Option ι) → SP g → ℕ := fun _ p => p.val
  let BP := fun g : G => {p : ℕ // p ∈ data.Tb g}
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  letI (g : Option ι) (p : SP g) : NeZero (sm g p) :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 data
  let mu := physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let Q := Nat.ceil (4*L^(D+1))
  let h := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 data).2.2 g)
  have hVb (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : 0 < (p.val:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb := (source_original_B26_physical_baseline_half434 BP bm cfg.q0
      cfg.hq0.le cfg.hq1.le (2*Nat.ceil (L^(0.52:ℝ))) g p
      (hVisit p.val (hTbLower g p.val p.property))).1
    have hb0 : 0 < physicalSourceBaseline BP bm cfg.q0
        (2*Nat.ceil (L^(0.52:ℝ))) g p := lt_of_lt_of_le (by norm_num) hb
    exact one_div_pos.mpr (mul_pos (mul_pos (hVb g) hp) hb0)
  have hLp : 0 < L := by linarith
  let eps := 9*L^(-(2*E0))
  have heps : 0 ≤ eps := mul_nonneg (by norm_num) (Real.rpow_nonneg hLp.le _)
  have hBig (d : ℕ) (hdp : 0 < d) (t : ℝ)
      (u v : SourceOriginalB26Active434 BP J 1 → ℂ) :
      ‖sourceOriginalUnfilteredPhysicalPair434 BP bm J 1 m pats mu data.Vbig
        (sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J 1 m pats
          (memoryOrientationK BP J 1 m pats K o)) d zeta t o k u v‖^2 ≤
      eps*sourceOriginalB26ActiveEnergy434 BP J 1 mu u*sourceOriginalB26ActiveEnergy434 BP J 1 mu v := by
    have hb := hMain x Y Hprime data sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge
      hTbLower hVbig blockA blockB hBlocks hcountA hcountB zeta t hZeta d hdp o k ho hk
      cfg.q0 cfg.hq0.le cfg.hq1.le u v
    simp only [sourceOriginalJointBigEnergy434,sourceOriginalJointBigMass434,
      sourceOriginalRealBigProductMass434,Complex.normSq_eq_norm_sq] at hb
    exact hb
  have hOrbit := source_original_physical_ORBIT_TRANSFER434 SP sm BP bm J 1 cap m pats
    mu hmu data.Vbig K cfg.q0 cfg.hq0 cfg.hq1 Vs hVs T zeta theta o k eps heps hBig
    rho hr0 hr1 F
  have hlog : 1 ≤ Real.log L := by
    simpa using Real.log_le_log (Real.exp_pos 1) hLe
  have hSmall := source_original_B26_small_conditioning_polynomial434 1
    cfg.q0 cfg.vmin (cfg.C0+1) L cfg.hq0 cfg.hq1 cfg.hv hC0 (by linarith)
    Vs (source_original_ACTUAL_SMALL_source_bounds434 data).2.2
    (source_original_ACTUAL_SMALL_group_count434 data hlog)
  have hSmall0 : 0 ≤ memorySmallGroupConditioningConstant (SG := Option ι) 1 cfg.q0 Vs := by
    unfold memorySmallGroupConditioningConstant
    apply Finset.prod_nonneg
    intro g _
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (pow_nonneg (sub_pos.mpr cfg.hq1).le _) (pow_nonneg (hVs g).le _))
  have hAbsorb := source_original_physical_ABSORB_SMALL434 L E Cs
    (memorySmallGroupConditioningConstant (SG := Option ι) 1 cfg.q0 Vs) hL3 hSmall0 hSmall
  have hEn := source_original_physical_orbit_energy_nonneg434 SP sm BP bm J 1 cap Vs hVs mu hmu F
  exact hOrbit.trans (mul_le_mul_of_nonneg_right hAbsorb hEn)
end Green64Analytic.CorrelationSquare

end

end

