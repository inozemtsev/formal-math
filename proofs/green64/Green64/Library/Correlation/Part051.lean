module

public import Green64.Library.Weights.ActualMixedBirthTail
public import Green64.Library.Correlation.Part050
public import Green64.Library.Correlation.Part030
public import Green64.Library.Correlation.Part049
public import Green64.Library.Correlation.Part047
public import Green64.Library.Weights.Part028
public import Green64.Library.Correlation.MemoryOldTerminalBirthCut

@[expose] public section

/-!
# Correlation / Part051

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualRootBirthTail -/

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

def sourceOriginalAbsoluteBackgroundMemoryRoot434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℝ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  ‖(physicalSourceBaselineProduct BP bm q N : ℂ)‖ *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      ‖(physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ)‖ *
      ‖physicalVacuum SP sm BP bm J ell y‖ *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        ∑ h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns N,
          sourceOriginalAbsoluteBackgroundChain434 SP sm BP bm J ell m cap patterns
            (fun g => Finset.univ \
              sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y N h g)
            q u Vs V mu K zeta theta k N N h 0
            (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y)
            (fun out _ => ‖physicalVacuum SP sm BP bm J ell out‖)
            y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

def sourceOriginalBackgroundBirthTailMemoryRoot434
    (q : ℝ) (H : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) : ℂ :=
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  (physicalSourceBaselineProduct BP bm q N : ℂ) *
    ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
      (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y : ℂ) *
      star (physicalVacuum SP sm BP bm J ell y) *
      (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
        ∑ h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns N,
          sourceOriginalSeenSeparatedBackgroundChain434 SP sm BP bm J ell m cap patterns
            (fun g => Finset.univ \
              sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y N h g)
            q Vs V mu K zeta theta k N N h 0
            (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y)
            (fun out st =>
              if H < (st ∩ sourceOriginalNumericBackground434 BP bm
                (fun g => Finset.univ \
                  sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y N h g)).card then
                physicalVacuum SP sm BP bm J ell out else 0)
            y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)


/-- The genuine full history root with a terminal numerical background
birth cut. The bound includes the entire positive active continuation,
original baseline, Fock mass and initial distinctness. -/
theorem source_original_ACTUAL_ROOT_background_birth_tail434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q u : ℝ) (hu : 1 ≤ u) (H : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    ‖sourceOriginalBackgroundBirthTailMemoryRoot434 SP sm BP bm J ell m cap patterns
      q H Vs V K zeta theta k R‖ ≤
    (u^H)⁻¹ * sourceOriginalAbsoluteBackgroundMemoryRoot434 SP sm BP bm J ell m cap patterns
      q u Vs V K zeta theta k R := by
  let N := 2*R
  let mu := physicalSourceMuTilde BP bm q N V
  let c : ℝ := (u^H)⁻¹
  let Bg := fun (y : FullPhysicalOutput SP sm BP bm (J+ell))
      (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns N) (g : BG) =>
    Finset.univ \ sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y N h g
  let T := fun (y : FullPhysicalOutput SP sm BP bm (J+ell))
      (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns N) =>
    sourceOriginalSeenSeparatedBackgroundChain434 SP sm BP bm J ell m cap patterns (Bg y h)
      q Vs V mu K zeta theta k N N h 0
      (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y)
      (fun out st => if H<(st ∩ sourceOriginalNumericBackground434 BP bm (Bg y h)).card
        then physicalVacuum SP sm BP bm J ell out else 0)
      y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
  let A := fun (y : FullPhysicalOutput SP sm BP bm (J+ell))
      (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns N) =>
    sourceOriginalAbsoluteBackgroundChain434 SP sm BP bm J ell m cap patterns (Bg y h)
      q u Vs V mu K zeta theta k N N h 0
      (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y)
      (fun out _ => ‖physicalVacuum SP sm BP bm J ell out‖)
      y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
  let W := fun y : FullPhysicalOutput SP sm BP bm (J+ell) =>
    (physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y:ℂ) *
      star (physicalVacuum SP sm BP bm J ell y)
  let WR := fun y : FullPhysicalOutput SP sm BP bm (J+ell) =>
    ‖(physicalOrbitMass SP sm BP bm (J+ell) cap Vs mu y:ℂ)‖ *
      ‖physicalVacuum SP sm BP bm J ell y‖
  have hw (y : FullPhysicalOutput SP sm BP bm (J+ell)) : ‖W y‖=WR y := by
    simp only [W,WR,norm_mul,norm_star]
  have ht (y : FullPhysicalOutput SP sm BP bm (J+ell))
      (hv : physicalVacuum SP sm BP bm J ell y≠0)
      (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns N) :
      ‖T y h‖ ≤ c*A y h := by
    have hzero := Finset.disjoint_iff_inter_eq_empty.mp
      (source_original_MEMORY_history_background_initial_empty434
        SP sm BP bm J ell m patterns hi y hv N h).2
    exact source_original_ACTUAL_MIXED_background_birth_tail434
      SP sm BP bm J ell m cap patterns (Bg y h) hi q u hu Vs V mu K zeta theta k N
      (fun out _ => physicalVacuum SP sm BP bm J ell out) N h
      (source_original_FULL_ACTIVE_HISTORY_complement_avoids434 SP sm BP bm J ell m patterns y N h)
      0 (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y)
      y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset hzero H
  have ho (y : FullPhysicalOutput SP sm BP bm (J+ell)) :
      ‖W y * (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
        then ∑ h,T y h else 0)‖ ≤
      c*(WR y*(if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
        then ∑ h,A y h else 0)) := by
    by_cases hv : physicalVacuum SP sm BP bm J ell y=0
    · simp only [W,WR,hv,star_zero,norm_zero,mul_zero,zero_mul,le_refl]
    · by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
      · rw [if_pos hn,if_pos hn,norm_mul,hw]
        have hs : ‖∑ h,T y h‖ ≤ c*(∑ h,A y h) := by
          apply le_trans (norm_sum_le _ _)
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun h hh => ht y hv h)
        calc
          _ ≤ WR y*(c*(∑ h,A y h)) :=
            mul_le_mul_of_nonneg_left hs (by rw [←hw];exact norm_nonneg _)
          _ = _ := by ring
      · simp only [if_neg hn,mul_zero,norm_zero,le_refl]
  change ‖(physicalSourceBaselineProduct BP bm q N:ℂ) *
      (∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        W y*(if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
          then ∑ h,T y h else 0))‖ ≤
    c*(‖(physicalSourceBaselineProduct BP bm q N:ℂ)‖ *
      (∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        WR y*(if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
          then ∑ h,A y h else 0)))
  rw [norm_mul]
  calc
    _ ≤ ‖(physicalSourceBaselineProduct BP bm q N:ℂ)‖ *
      (∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        ‖W y*(if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
          then ∑ h,T y h else 0)‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖(physicalSourceBaselineProduct BP bm q N:ℂ)‖ *
      (∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        c*(WR y*(if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
          then ∑ h,A y h else 0))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y hy => ho y)) (norm_nonneg _)
    _ = _ := by rw [←Finset.mul_sum];ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPositiveEBackground -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
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

variable (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
variable (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
variable (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)

local notation "X" => sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y
local notation "Y" => sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
  (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background y)
local notation "E" => sourceOriginalCanonicalBackgroundEmbedding434 SP sm BP bm
  (J+ell) cap hcap background y seen hy


include hcap hy in
theorem source_original_ABSOLUTE_E_background_frame_row434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (htarget : ∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ) :
    sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta o k X seen r F =
    sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta o k Y seen r
      (fun out s => F
        (sourceOriginalAttachPendingBackground434 SP sm BP bm J ell background y
          (sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1 X
            r.2.2.1.1 r.2.2.2.1 o k) out) s) := by
  unfold sourceOriginalAbsoluteEFrame434
  symm
  apply Fintype.sum_equiv (sourceOriginalBackgroundFrameEquiv434
    SP sm BP bm J ell m cap patterns hcap background y seen hy r o k htarget)
  intro f
  change _ =
    ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta o k X
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r
        (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
          hcap background y seen hy r f.1))‖ *
    F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns X o k
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r
        (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
          hcap background y seen hy r f.1)))
      (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns
        (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns X r
          (sourceOriginalBackgroundFrameEmbed434 SP sm BP bm J ell m cap patterns
            hcap background y seen hy r f.1))).toFinset)
  rw [source_original_SOURCE_E_background_frame_coefficient434,
    source_original_SOURCE_E_background_frame_output434,
    source_original_SOURCE_E_background_frame_births434]


variable (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
local notation "B" => sourceOriginalNumericBackground434 BP bm background
include hi in
theorem source_original_ABSOLUTE_E_background_seen_row434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (htarget : ∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ) :
    sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r F =
    sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x (seen \ B) r
      (fun out s => F out (s ∪ (seen ∩ B))) := by
  let e : {f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r //
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f} ≃
      {f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r //
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x (seen \ B) o k r f} :=
    { toFun := fun f => ⟨f.1,(source_original_SOURCE_E_frame_background_seen434
        SP sm BP bm J ell m cap patterns hi background x seen r o k htarget f.1).mp f.2⟩
      invFun := fun f => ⟨f.1,(source_original_SOURCE_E_frame_background_seen434
        SP sm BP bm J ell m cap patterns hi background x seen r o k htarget f.1).mpr f.2⟩
      left_inv := by intro f;rfl
      right_inv := by intro f;rfl }
  unfold sourceOriginalAbsoluteEFrame434
  apply Fintype.sum_equiv e
  intro f
  dsimp only [e]
  have hu (births : Finset ℕ) :
      ((seen \ B) ∪ births) ∪ (seen ∩ B) = seen ∪ births := by
    ext p
    simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [hu]
  all_goals rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPositiveGCommon -/

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
variable (M : ℕ)

/-- Positive row on the original unsplit prime-birth carrier, with
the full numerical no-rebirth gate and the full joint observation. -/
def sourceOriginalAbsoluteUnseenPrimeG434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (A : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℝ) : ℝ :=
  ∑ d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y,
    if ∀ g,∀ p ∈ (d g).2,bm g p ∉ seen then
      ‖sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M q rho N i V mu y d‖ *
      A (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y
        (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d))
        (seen ∪ sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm M y d)
    else 0

theorem source_original_ABSOLUTE_G_common_carrier434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (background : (g : BG) → Finset (BP g))
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (A : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℝ) :
    sourceOriginalAbsoluteBackgroundTiltG434 SP sm BP bm M background y
      q rho 1 N i V mu seen A =
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q rho N i V mu y seen A := by
  unfold sourceOriginalAbsoluteBackgroundTiltG434 sourceOriginalAbsoluteUnseenPrimeG434
  simp only [one_mul]
  apply Fintype.sum_equiv
    (sourceOriginalPhysicalGhostPartitionEquiv434 SP sm BP bm M background y).symm
  intro ab
  change _ = if ∀ g,∀ p ∈
    (sourceOriginalPhysicalGhostRecombine434 SP sm BP bm M background y ab.1 ab.2 g).2,
      bm g p ∉ seen then
    ‖sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M q rho N i V mu y
      (sourceOriginalPhysicalGhostRecombine434 SP sm BP bm M background y ab.1 ab.2)‖ *
    A (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y
      (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y
        (sourceOriginalPhysicalGhostRecombine434 SP sm BP bm M background y ab.1 ab.2)))
      (seen ∪ sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm M y
        (sourceOriginalPhysicalGhostRecombine434 SP sm BP bm M background y ab.1 ab.2))
    else 0
  simp only [source_original_PHYSICAL_G_partition_gate434,
    source_original_PHYSICAL_G_separate_seen_gates434 SP sm BP bm M background y hi,
    source_original_PHYSICAL_G_partition_coefficient434,
    source_original_PHYSICAL_G_partition_output434,
    source_original_PHYSICAL_G_partition_births434,norm_mul]
  split_ifs
  · congr 2
    ext n
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,
      sourceOriginalNumericBackground434]
    tauto
  · rfl

theorem source_original_ACTUAL_ACTIVE_coefficient_birth_tilt434
    (background : (g : BG) → Finset (BP g))
    (y : FullPhysicalOutput SP sm BP bm M)
    (q rho u : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y
      q rho N i V (fun g p => u*mu g p) a =
    (u:ℂ)^(∑ g,(a g).2.1.card) *
      sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y
        q rho N i V mu a := by
  unfold sourceOriginalGhostActiveCoefficient434
    sourceOriginalGroupPrimeBirthWeight434 sourceOriginalRestrictedPrimeBirthLift434
  simp only [Complex.ofReal_mul,Finset.prod_mul_distrib,Finset.prod_const]
  rw [Finset.prod_pow_eq_pow_sum Finset.univ (fun g => (a g).2.1.card) (u:ℂ)]
  ring

/-- Uniform tilt dominates partial background tilt without discarding
the actual no-rebirth gate, outputs, or any dependence of A. -/
theorem source_original_ABSOLUTE_G_background_le_all_tilt434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (background : (g : BG) → Finset (BP g))
    (q rho u : ℝ) (hu : 1 ≤ u) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (A : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℝ)
    (hA : ∀ out st,0 ≤ A out st) :
    sourceOriginalAbsoluteBackgroundTiltG434 SP sm BP bm M background y
      q rho u N i V mu seen A ≤
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q rho N i V
      (fun g p => u*mu g p) y seen A := by
  rw [←source_original_ABSOLUTE_G_common_carrier434
    SP sm BP bm M hi background]
  unfold sourceOriginalAbsoluteBackgroundTiltG434
  simp only [one_mul]
  apply Finset.sum_le_sum
  intro ab hab
  split_ifs
  · apply mul_le_mul_of_nonneg_right _ (hA _ _)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [source_original_ACTUAL_ACTIVE_coefficient_birth_tilt434,
      norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ u)]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hu)
  · rfl

theorem source_original_ABSOLUTE_UNSEEN_G_nonneg434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (A : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℝ)
    (hA : ∀ out st,0 ≤ A out st) :
    0 ≤ sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q rho N i V mu y seen A := by
  unfold sourceOriginalAbsoluteUnseenPrimeG434
  apply Finset.sum_nonneg
  intro d hd
  split_ifs
  · exact mul_nonneg (norm_nonneg _) (hA _ _)
  · rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualHistorySupGhost -/

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
variable (J ell : ℕ)

/-- Every truly selected G prime birth stays in the original finite
numerical birth pool. This is an exact membership identity, not an
assumed full-history closure estimate. -/
theorem source_original_ACTUAL_ghost_births_subset_pool434
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm (J+ell) y) :
    sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm (J+ell) y d ⊆
      sourceOriginalMemoryBirthPool434 BP bm := by
  intro p hp
  rcases Finset.mem_biUnion.mp hp with ⟨g,_,hg⟩
  rcases Finset.mem_image.mp hg with ⟨a,_,rfl⟩
  exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,
    Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩

/-- The ACTUAL numerical ghost G row propagates a uniform-in-seen
continuation envelope through its physical absolute companion. This
costs NO cardinality of the history powerset, and preserves the
numerical no-rebirth gate, full signed coefficients and all outputs. -/
theorem source_original_ACTUAL_G_history_sup_majorant434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    ‖sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen F‖ ≤
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
      q rho N i V mu y seen
      (fun out _ => sourceOriginalActualHistorySupNorm434
        SP sm BP bm J ell F out) := by
  classical
  have hs : seen ⊆ sourceOriginalMemoryBirthPool434 BP bm :=
    Finset.mem_powerset.mp hseen
  unfold sourceOriginalPhysicalGhostUnseenPrimeRow434
    sourceOriginalAbsoluteUnseenPrimeG434
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro d hd
  by_cases hg : ∀ g,∀ p ∈ (d g).2,bm g p ∉ seen
  · simp only [if_pos hg,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply source_original_ACTUAL_history_sup_dominates434
    apply Finset.mem_powerset.mpr
    exact Finset.union_subset hs (source_original_ACTUAL_ghost_births_subset_pool434
      SP sm BP bm J ell y d)
  · simp only [if_neg hg,norm_zero,le_refl]

/-- The minimal exact history-envelope of the TRUE signed G row is
bounded by the maximal ABSOLUTE G row acting on the previous minimal
continuation envelope. No factor |Hist| at either side. -/
theorem source_original_ACTUAL_G_history_sup_step434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) :
    sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell
      (fun out seen => sourceOriginalPhysicalGhostUnseenPrimeRow434
        SP sm BP bm (J+ell) q rho N i V mu out seen F) y ≤
    ((sourceOriginalMemoryBirthPool434 BP bm).powerset).sup'
      (source_original_ACTUAL_history_pool_nonempty434 BP bm)
      (fun seen => sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
        q rho N i V mu y seen
        (fun out _ => sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F out)) := by
  change ((sourceOriginalMemoryBirthPool434 BP bm).powerset).sup'
    (source_original_ACTUAL_history_pool_nonempty434 BP bm)
    (fun seen => ‖sourceOriginalPhysicalGhostUnseenPrimeRow434
      SP sm BP bm (J+ell) q rho N i V mu y seen F‖) ≤ _
  apply Finset.sup'_le
  intro seen hs
  exact (source_original_ACTUAL_G_history_sup_majorant434
    SP sm BP bm J ell q rho N i V mu F y seen hs).trans
      (Finset.le_sup' (fun s => sourceOriginalAbsoluteUnseenPrimeG434
        SP sm BP bm (J+ell) q rho N i V mu y s
        (fun out _ => sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F out)) hs)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualHistorySupEFrame -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 19000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Positive companion for the TRUE source E-frame, using the ONE
admissible injection selected by the actual frame formulation. This
keeps the identical orientations, joint K, OLD/Fock state and
numerical birth mask; no fabricated independent E-row appears. -/
def sourceOriginalAbsoluteFilteredEFrameHistory434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → ℝ) : ℝ :=
  ∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
    if h : ∃ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
        sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f then
      let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r
        (Classical.choose h)
      if keep x z then
        ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k x z‖ *
        A (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
      else 0
    else 0

/-- The TRUE filtered physical E-frame propagates the exact maximal
history envelope with no power-set cardinality factor, even with
nontrivial OLD choices and a joint signed RAW/comparison K. -/
theorem source_original_ACTUAL_E_history_sup_majorant434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    ‖sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen F‖ ≤
    sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen
      (sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F) := by
  classical
  have hs : seen ⊆ sourceOriginalMemoryBirthPool434 BP bm :=
    Finset.mem_powerset.mp hseen
  unfold sourceOriginalSourceEFrameFilteredRow434
    sourceOriginalAbsoluteFilteredEFrameHistory434
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro r hr
  by_cases h : ∃ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f
  · simp only [dif_pos h]
    let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r
      (Classical.choose h)
    let out := sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z
    let fresh := (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset
    let coeff := sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x z
    change ‖if keep x z then coeff*F out (seen ∪ fresh) else 0‖ ≤
      (if keep x z then ‖coeff‖ *
        sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F out else 0)
    by_cases hk : keep x z
    · simp only [if_pos hk,norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply source_original_ACTUAL_history_sup_dominates434
      apply Finset.mem_powerset.mpr
      exact Finset.union_subset hs (source_original_memory_E_births_subset_pool434
        SP sm BP bm J ell m cap patterns x z)
    · simp only [if_neg hk,norm_zero,le_refl]
  · simp only [dif_neg h,norm_zero,le_refl]

/-- Exact max-history dynamic step for TRUE full/CLEAN E-frame, after
preserving every chronological source prime birth; no visit count. -/
theorem source_original_ACTUAL_E_history_sup_step434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) :
    ((sourceOriginalMemoryBirthPool434 BP bm).powerset).sup'
      (source_original_ACTUAL_history_pool_nonempty434 BP bm)
      (fun seen => ‖sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k x seen F‖) ≤
    ((sourceOriginalMemoryBirthPool434 BP bm).powerset).sup'
      (source_original_ACTUAL_history_pool_nonempty434 BP bm)
      (fun seen => sourceOriginalAbsoluteFilteredEFrameHistory434
        SP sm BP bm J ell m cap patterns keep q rho Vs V mu K zeta theta o k x seen
        (sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F)) := by
  apply Finset.sup'_le
  intro seen hs
  exact (source_original_ACTUAL_E_history_sup_majorant434 SP sm BP bm J ell m cap patterns
    keep q rho Vs V mu K zeta theta o k F x seen hs).trans
    (Finset.le_sup' (fun s => sourceOriginalAbsoluteFilteredEFrameHistory434
      SP sm BP bm J ell m cap patterns keep q rho Vs V mu K zeta theta o k x s
      (sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F)) hs)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualHistorySupGEStep -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 21000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- A single true source G followed by its original frame E (or the
literal CLEAN restriction) at the canonical reachable Fock representative.
No new auxiliary coupling or independent endpoint probability is used. -/
def sourceOriginalActualGEFilteredHistory434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) : ℂ :=
  sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
    q rho N i V mu y seen (fun out st =>
      sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap out) st F)

/-- Positive operator on the same actual G/E output carrier, with the
full numerical history MAXIMUM at the intermediate E step. Neither
frame summands nor any histories are multiplied by their count. -/
def sourceOriginalActualGEFilteredPositiveHistory434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) : ℝ :=
  sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell) q rho N i V mu y seen
    (fun out _ => ((sourceOriginalMemoryBirthPool434 BP bm).powerset).sup'
      (source_original_ACTUAL_history_pool_nonempty434 BP bm)
      (fun st => sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
        keep q rho Vs V mu K zeta theta o k
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap out) st
        (sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F)))

/-- TWO genuine physical chronological steps propagate the least
uniform numerical history envelope by ONE positive G composed with
ONE positive E. Exact independent signs and comparison K are kept.
No power-set cardinality or per-visit analytic premise is introduced. -/
theorem source_original_ACTUAL_GE_history_sup_majorant434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hseen : seen ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset) :
    ‖sourceOriginalActualGEFilteredHistory434 SP sm BP bm J ell m cap patterns
      keep q rho N i Vs V mu K zeta theta o k F y seen‖ ≤
    sourceOriginalActualGEFilteredPositiveHistory434 SP sm BP bm J ell m cap patterns
      keep q rho N i Vs V mu K zeta theta o k F y seen := by
  classical
  let ETest : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun out st => sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k
      (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap out) st F
  have hE (out : FullPhysicalOutput SP sm BP bm (J+ell)) :
      sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell ETest out ≤
      ((sourceOriginalMemoryBirthPool434 BP bm).powerset).sup'
        (source_original_ACTUAL_history_pool_nonempty434 BP bm)
        (fun st => sourceOriginalAbsoluteFilteredEFrameHistory434 SP sm BP bm J ell m cap patterns
          keep q rho Vs V mu K zeta theta o k
          (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap out) st
          (sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell F)) := by
    exact source_original_ACTUAL_E_history_sup_step434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k F
      (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap out)
  have hG := source_original_ACTUAL_G_history_sup_majorant434 SP sm BP bm J ell
    q rho N i V mu ETest y seen hseen
  unfold sourceOriginalActualGEFilteredHistory434 sourceOriginalActualGEFilteredPositiveHistory434
  calc
    _ ≤ sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
        q rho N i V mu y seen
        (fun out _ => sourceOriginalActualHistorySupNorm434 SP sm BP bm J ell ETest out) := hG
    _ ≤ _ := by
      unfold sourceOriginalAbsoluteUnseenPrimeG434
      apply Finset.sum_le_sum
      intro d hd
      by_cases hh : ∀ g,∀ p ∈ (d g).2,bm g p ∉ seen
      · simp only [if_pos hh]
        exact mul_le_mul_of_nonneg_left (hE _) (norm_nonneg _)
      · simp only [if_neg hh,le_refl]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPositiveGReachable -/

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
variable (M : ℕ)

/-- The literal atom-subset G cannot create inventory other than its
selected fresh atoms. This does not use a coefficient sign or size. -/
theorem source_original_ACTUAL_G_atom_inventory434
    (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostAtomWitness434 SP sm BP bm M y) :
    sourceOriginalPhysicalInventory434 SP sm BP bm M
      (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y d) ≤
    sourceOriginalPhysicalInventory434 SP sm BP bm M y +
      (sourceOriginalPhysicalGhostAtomBirths434 SP sm BP bm M y d : Multiset ℕ) := by
  rw [sourceOriginalPhysicalGhostAtomBirths434,source_original_inventory_flatMap_bag434]
  unfold sourceOriginalPhysicalInventory434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g hg
  have hr : ((y.2 g).2.toFinset \ (d g).1.1).val ≤ (y.2 g).2 :=
    le_trans (Finset.val_le_iff.mpr Finset.sdiff_subset) (Multiset.dedup_le _)
  have hm := Multiset.map_le_map (f := fun z : Atom (BP g) (bm g) => bm g z.1) hr
  simpa only [sourceOriginalPhysicalGhostAtomOutput434,sourceOriginalBigInventory434,
    Finset.sum_multiset_singleton,Multiset.map_add,←Multiset.map_coe,Finset.coe_toList,
    add_assoc,add_comm,add_left_comm] using
    add_le_add_left (add_le_add_right hm ((d g).2.val.map (fun z => bm g z.1)))
      (∑ j : Fin M,({bm g ((y.2 g).1 j)} : Multiset ℕ))

theorem source_original_ACTUAL_UNSEEN_G_witness_reachable434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y)
    (hd : ∀ g,∀ p ∈ (d g).2,bm g p ∉ seen) :
    sourceOriginalPhysicalReachable434 SP sm BP bm M
      (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y
        (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d))
      (seen ∪ sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm M y d) := by
  have he := (source_original_PHYSICAL_G_prime_birth_gate434 SP sm BP bm M hi y seen d).mpr hd
  have hr := source_original_inventory_fresh_preserves434 _ _ seen _ hy he.1 he.2
    (source_original_ACTUAL_G_atom_inventory434 SP sm BP bm M y
      (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d))
  rw [source_original_PHYSICAL_G_prime_birth_set434] at hr
  exact hr

/-- Positive comparison needs the continuation inequality only on
actual reachable outputs. No artificial all-state norm hypothesis. -/
theorem source_original_ABSOLUTE_UNSEEN_G_reachable_mono434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen)
    (A C : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℝ)
    (hAC : ∀ out st,sourceOriginalPhysicalReachable434 SP sm BP bm M out st →
      A out st ≤ C out st) :
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q rho N i V mu y seen A ≤
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q rho N i V mu y seen C := by
  unfold sourceOriginalAbsoluteUnseenPrimeG434
  apply Finset.sum_le_sum
  intro d hd
  split_ifs with he
  · exact mul_le_mul_of_nonneg_left
      (hAC _ _ (source_original_ACTUAL_UNSEEN_G_witness_reachable434
        SP sm BP bm M hi y seen hy d he)) (norm_nonneg _)
  · rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPositiveGSourceBox -/

section

open scoped BigOperators Classical
open Filter
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 12000000


theorem source_original_ABSOLUTE_UNSEEN_G_uniform_tilt_cost434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (M : ℕ) (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q u : ℝ) (hu : 0 ≤ u) (N i : ℕ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (he : 0 ≤ sourceVisitEta q N i) (he1 : sourceVisitEta q N i ≤ 1)
    (hV : ∀ g,0 ≤ V g) (hmu : ∀ g p,0 ≤ mu g p)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ) :
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q 1 N i V
      (fun g p => u*mu g p) y seen (fun _ _ => 1) ≤
    Real.exp (u*sourceVisitEta q N i*(∑ g,∑ p,V g*mu g p)) := by
  rw [←source_original_ABSOLUTE_G_common_carrier434 SP sm BP bm M hi (fun _ => ∅)]
  have hb := source_original_ACTUAL_TILTED_G_mass_bound434
    SP sm BP bm M (fun _ => ∅) y q 1 N i V (fun g p => u*mu g p)
    he he1 zero_le_one hV (fun g p => mul_nonneg hu (hmu g p)) seen
  have hc := source_original_ACTUAL_G_birth_cost_exp434 BP (fun _ => ∅)
    q 1 N i V (fun g p => u*mu g p) he (le_refl 1)
    hV (fun g p => mul_nonneg hu (hmu g p))
  apply (hb.trans hc).trans_eq
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem eventually_source_original_ABSOLUTE_UNSEEN_G_source_box434
    (c : ℝ) (hc : 0<c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      {BG : Type} [Fintype BG] [DecidableEq BG]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
      (q : ℝ) (hq : 0≤q) (hq1 : q≤1) (V : BG → ℝ) (hV : ∀ g,0<V g)
      (hmin : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (hmax : ∀ g p,(bm g p:ℝ) ≤ Real.exp (Real.sqrt L))
      (M : ℕ)
      (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ) (i : ℕ)
      (u : ℝ) (hu : 1≤u),
      sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q 1
        (2*Nat.ceil (L^(0.52:ℝ))) i V
        (fun g p => u*physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V g p)
        y seen (fun _ _ => 1) ≤
      Real.exp (2*u*sourceVisitEta q (2*Nat.ceil (L^(0.52:ℝ))) i*(1+Real.sqrt L)) := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc] with L hL
  intro SG _ _ SP _ _ sm _ BG _ _ BP _ _ bm _ hi q hq hq1 V hV hmin hmax
    M y seen i u hu
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP bm q N V
  have hb (g : BG) (p : BP g) : (1:ℝ)/2 ≤ physicalSourceBaseline BP bm q N g p :=
    (source_original_B26_physical_baseline_half434 BP bm q hq hq1 N g p
      (hL (bm g p) (hmin g p))).1
  have hb0 (g : BG) (p : BP g) : 0<physicalSourceBaseline BP bm q N g p := by
    have hh := hb g p
    linarith
  have hmu (g : BG) (p : BP g) : 0 ≤ mu g p := by
    have hv := hV g
    have hp : (0:ℝ)<bm g p := by exact_mod_cast NeZero.pos (bm g p)
    have hb' := hb0 g p
    dsimp only [mu,physicalSourceMuTilde]
    positivity
  have he := source_original_B26_visit_eta_unit434 q hq hq1 N i
  have hsigma : (∑ g,∑ p,1/(bm g p:ℝ)) ≤ 1+Real.sqrt L := by
    have hh := source_original_GHOST_numeric_harmonic_box434
      (fun x : Sigma BP => bm x.1 x.2) Finset.univ hi
      (fun x _ => NeZero.pos _) (Real.exp (Real.sqrt L))
      (Real.one_le_exp_iff.mpr (Real.sqrt_nonneg L)) (fun x _ => hmax x.1 x.2)
    simpa only [Finset.sum_map_toList,Fintype.sum_sigma,Real.log_exp] using hh
  have hmass : (∑ g,∑ p,V g*mu g p) ≤ 2*(1+Real.sqrt L) :=
    (source_original_ACTUAL_source_mu_intensity434 BP bm q N V hV hb).trans
      (mul_le_mul_of_nonneg_left hsigma (by norm_num))
  apply (source_original_ABSOLUTE_UNSEEN_G_uniform_tilt_cost434
    SP sm BP bm M hi q u (zero_le_one.trans hu) N i V mu
    he.1 he.2 (fun g => (hV g).le) hmu y seen).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hmass (mul_nonneg (zero_le_one.trans hu) he.1)
  dsimp only [N] at hh ⊢
  nlinarith only [hh]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPositiveHistory -/

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

/-- Full positive fixed-history chain. G births use u*mu on every
prime; E keeps the original mu, joint K, both phases and outputs.
There is no history-dependent background in this operator. -/
def sourceOriginalAbsoluteFixedFrameChain434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (n : ℕ) → SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n →
    (start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
  | 0,_,start,A => fun y seen =>
      sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell) q 1 N start V
        (fun g p => u*mu g p) y seen A
  | n+1,(r,h),start,A => fun y seen =>
      sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell) q 1 N start V
        (fun g p => u*mu g p) y seen (fun yg sg =>
          sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
            q 1 Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg r
            (sourceOriginalAbsoluteFixedFrameChain434
              q u Vs V mu K zeta theta k N n h (start+1) A))

theorem source_original_ABSOLUTE_E_nonneg434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hA : ∀ out st,0 ≤ A out st) :
    0 ≤ sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r A := by
  unfold sourceOriginalAbsoluteEFrame434
  exact Finset.sum_nonneg (fun f hf => mul_nonneg (norm_nonneg _) (hA _ _))

theorem source_original_ABSOLUTE_FIXED_HISTORY_nonneg434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hA : ∀ out st,0 ≤ A out st)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    0 ≤ sourceOriginalAbsoluteFixedFrameChain434 SP sm BP bm J ell m cap patterns
      q u Vs V mu K zeta theta k N n h start A y seen := by
  induction n generalizing start y seen with
  | zero =>
      exact source_original_ABSOLUTE_UNSEEN_G_nonneg434
        SP sm BP bm (J+ell) q 1 N start V (fun g p => u*mu g p) y seen A hA
  | succ n ih =>
      rcases h with ⟨r,h⟩
      dsimp only [sourceOriginalAbsoluteFixedFrameChain434]
      apply source_original_ABSOLUTE_UNSEEN_G_nonneg434
      intro yg sg
      apply source_original_ABSOLUTE_E_nonneg434
      intro out st
      exact ih h (start+1) out st

theorem source_original_ABSOLUTE_BACKGROUND_HISTORY_nonneg434
    (background : (g : BG) → Finset (BP g))
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hA : ∀ out st,0 ≤ A out st)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (start : ℕ) (sk y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    0 ≤ sourceOriginalAbsoluteBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q u Vs V mu K zeta theta k N n h start sk A y seen := by
  induction n generalizing start sk y seen with
  | zero =>
      unfold sourceOriginalAbsoluteBackgroundChain434 sourceOriginalAbsoluteBackgroundTiltG434
      apply Finset.sum_nonneg
      intro ab hab
      split_ifs
      · exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hA _ _)
      · rfl
  | succ n ih =>
      rcases h with ⟨r,h⟩
      dsimp only [sourceOriginalAbsoluteBackgroundChain434]
      unfold sourceOriginalAbsoluteBackgroundTiltG434
      apply Finset.sum_nonneg
      intro ab hab
      split_ifs
      · apply mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        apply source_original_ABSOLUTE_E_nonneg434
        intro out st
        exact ih h (start+1) _ _ _
      · rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPositiveHistorySum -/

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

theorem source_original_ABSOLUTE_G_terminal_sum434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    {I : Type} [Fintype I]
    (F : I → FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ) :
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell) q rho N i V mu y seen
      (fun out s => ∑ t,F t out s) =
    ∑ t,sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell)
      q rho N i V mu y seen (F t) := by
  unfold sourceOriginalAbsoluteUnseenPrimeG434
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : ∀ g,∀ p ∈ (d g).2,bm g p ∉ seen
  · simp only [if_pos h,Finset.mul_sum]
  · simp only [if_neg h,Finset.sum_const_zero]

theorem source_original_ABSOLUTE_E_terminal_sum434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    {I : Type} [Fintype I]
    (F : I → FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ) :
    sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r (fun out s => ∑ t,F t out s) =
    ∑ t,sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r (F t) := by
  unfold sourceOriginalAbsoluteEFrame434
  dsimp only
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- The common positive time-ordered operator: the actual E-frame sum
is performed at each E visit on the current full state. -/
def sourceOriginalAbsoluteGEChain434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (n start : ℕ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
  | 0,start,A => fun y seen =>
      sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell) q 1 N start V
        (fun g p => u*mu g p) y seen A
  | n+1,start,A => fun y seen =>
      sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm (J+ell) q 1 N start V
        (fun g p => u*mu g p) y seen (fun yg sg =>
          ∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
            sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
              q 1 Vs V mu
              (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
              zeta theta (physicalAlternatingSign start) k
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg r
              (sourceOriginalAbsoluteGEChain434 q u Vs V mu K zeta theta k N n (start+1) A))

theorem source_original_ABSOLUTE_GE_history_sum434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalAbsoluteGEChain434 SP sm BP bm J ell m cap patterns
      q u Vs V mu K zeta theta k N n start F y seen =
    ∑ h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n,
      sourceOriginalAbsoluteFixedFrameChain434 SP sm BP bm J ell m cap patterns
        q u Vs V mu K zeta theta k N n h start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      letI : Unique (SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns 0) :=
        inferInstanceAs (Unique PUnit)
      rw [Fintype.sum_unique]
      rfl
  | succ n ih =>
      change _ = ∑ h : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns ×
        SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n,
        sourceOriginalAbsoluteFixedFrameChain434 SP sm BP bm J ell m cap patterns
          q u Vs V mu K zeta theta k N (n+1) h start F y seen
      rw [Fintype.sum_prod_type]
      rw [sourceOriginalAbsoluteGEChain434]
      simp only [sourceOriginalAbsoluteFixedFrameChain434]
      have ihf :
          sourceOriginalAbsoluteGEChain434 SP sm BP bm J ell m cap patterns
            q u Vs V mu K zeta theta k N n (start+1) F =
          fun out s => ∑ h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n,
            sourceOriginalAbsoluteFixedFrameChain434 SP sm BP bm J ell m cap patterns
              q u Vs V mu K zeta theta k N n h (start+1) F out s := by
        funext out s
        exact ih (start+1) out s
      rw [ihf]
      simp_rw [source_original_ABSOLUTE_E_terminal_sum434]
      rw [source_original_ABSOLUTE_G_terminal_sum434]
      apply Finset.sum_congr rfl
      intro r hr
      rw [source_original_ABSOLUTE_G_terminal_sum434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualOLDSeenBudget -/

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
variable (M : ℕ)

/-- Total pending OLD consists of distinct numerical BIG labels in seen. -/
theorem source_original_ACTUAL_OLD_le_seen434
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen) :
    (∑ g : BG,(y.2 g).2.card) ≤ seen.card := by
  have h := source_original_REACHABLE_background_pending_le_seen434
    SP sm BP bm M (fun g => Finset.univ) y seen hy
  simp only [Finset.mem_univ,Multiset.filter_true] at h
  exact h.trans (Finset.card_le_card Finset.inter_subset_left)

/-- Exact tilt of every G birth; no OLD or E coefficient is tilted. -/
theorem source_original_ACTUAL_G_all_birth_tilt434
    (q rho u : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y) :
    sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M
      q rho N i V (fun g p => u*mu g p) y d =
    (u:ℂ)^(∑ g,(d g).2.card) *
      sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M
        q rho N i V mu y d := by
  unfold sourceOriginalPhysicalGhostPrimeBirthCoefficient434 sourceOriginalGroupPrimeBirthWeight434
  simp only [Complex.ofReal_mul,Finset.prod_mul_distrib,Finset.prod_const]
  rw [Finset.prod_pow_eq_pow_sum Finset.univ (fun g => (d g).2.card) (u:ℂ)]
  ring

theorem source_original_ACTUAL_G_seen_growth434
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (d : SourceOriginalPhysicalGhostPrimeBirthWitness434 SP sm BP bm M y) :
    (seen ∪ sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm M y d).card ≤
      seen.card + ∑ g,(d g).2.card := by
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add_left
  unfold sourceOriginalPhysicalGhostPrimeBirthSet434
  apply (Finset.card_biUnion_le).trans
  exact Finset.sum_le_sum (fun g _ => Finset.card_image_le)

variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- All original E fresh choices together add at most one BIG active
array. This budget is global over groups and independent of the frame. -/
theorem source_original_ACTUAL_E_seen_growth434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x) :
    (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset).card ≤
      seen.card + Fintype.card BG * (J+ell) := by
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add_left
  apply (List.toFinset_card_le _).trans
  change (orientedEFreshBirths SP sm BP bm J ell m cap patterns z : Multiset ℕ).card ≤ _
  rw [orientedEFreshBirths,source_original_inventory_flatMap_bag434,Multiset.card_sum]
  simp only [Multiset.coe_card,List.length_map,Finset.length_toList]
  calc
    _ ≤ ∑ _g : BG,(J+ell) := by
      apply Finset.sum_le_sum
      intro g hg
      simpa only [Fintype.card_fin] using Finset.card_le_univ
        (orientedFresh (J+ell) (sourceBigShared J ell m (patterns z.1) g)
          (z.2.2.1.bigChoice g).2.2.1)
    _ = _ := by simp

theorem source_original_ACTUAL_initial_seen_bound434
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) :
    (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset.card ≤
      Fintype.card BG * (J+ell) := by
  apply (List.toFinset_card_le _).trans
  change (physicalOutputInitialBirths SP sm BP bm J ell y : Multiset ℕ).card ≤ _
  rw [physicalOutputInitialBirths,source_original_inventory_flatMap_bag434,Multiset.card_sum]
  simp
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualOLDWeightedRows -/

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
variable (M : ℕ)

theorem source_original_ACTUAL_G_tilted_majorant434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q rho u : ℝ) (hu : 1 ≤ u) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ)
    (A : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℝ)
    (hA : ∀ out st,0 ≤ A out st)
    (hFA : ∀ out st,sourceOriginalPhysicalReachable434 SP sm BP bm M out st →
      ‖F out st‖ ≤ A out st) :
    ‖sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm M q rho N i V mu y seen F‖ ≤
    sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q rho N i V
      (fun g p => u*mu g p) y seen A := by
  unfold sourceOriginalPhysicalGhostUnseenPrimeRow434 sourceOriginalAbsoluteUnseenPrimeG434
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  split_ifs with he
  · rw [norm_mul,source_original_ACTUAL_G_all_birth_tilt434,norm_mul,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ u)]
    have hr := source_original_ACTUAL_UNSEEN_G_witness_reachable434 SP sm BP bm M hi y seen hy d he
    apply (mul_le_mul_of_nonneg_left (hFA _ _ hr) (norm_nonneg _)).trans
    apply mul_le_mul_of_nonneg_right _ (hA _ _)
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hu)
  · simp only [norm_zero,le_refl]

/-- A single seen potential moves across the actual G row. The tilt
charges only its fresh births, with the same complete joint continuation. -/
theorem source_original_ACTUAL_G_weighted_majorant434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q rho u c : ℝ) (hu : 1 ≤ u) (hc : 0 ≤ c)
    (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ)
    (A : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℝ)
    (hA : ∀ out st,0 ≤ A out st)
    (hFA : ∀ out st,sourceOriginalPhysicalReachable434 SP sm BP bm M out st →
      ‖F out st‖ ≤ c*u^st.card*A out st) :
    ‖sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm M q rho N i V mu y seen F‖ ≤
    c*u^seen.card * sourceOriginalAbsoluteUnseenPrimeG434 SP sm BP bm M q rho N i V
      (fun g p => u*mu g p) y seen A := by
  unfold sourceOriginalPhysicalGhostUnseenPrimeRow434 sourceOriginalAbsoluteUnseenPrimeG434
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  split_ifs with he
  · rw [norm_mul,source_original_ACTUAL_G_all_birth_tilt434,norm_mul,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ u)]
    have hr := source_original_ACTUAL_UNSEEN_G_witness_reachable434 SP sm BP bm M hi y seen hy d he
    have hp := pow_le_pow_right₀ hu (source_original_ACTUAL_G_seen_growth434 SP sm BP bm M y seen d)
    rw [pow_add] at hp
    apply (mul_le_mul_of_nonneg_left (hFA _ _ hr) (norm_nonneg _)).trans
    calc
      _ ≤ ‖sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M
          q rho N i V mu y d‖ *
          (c*(u^seen.card*u^(∑ g,(d g).2.card)) *
            A (sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M y
              (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M y d))
              (seen ∪ sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm M y d)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc) (hA _ _)
      _ = _ := by ring
  · simp only [norm_zero,mul_zero,le_refl]

variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Majorization of the genuine full E-frame row on reachable outputs.
The numeric growth bound concerns the original E fresh-birth list. -/
theorem source_original_ACTUAL_E_reachable_majorant434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hFA : ∀ out st,sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) out st →
      st.card ≤ seen.card+Fintype.card BG*(J+ell) → ‖F out st‖ ≤ A out st) :
    ‖sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F‖ ≤
    ∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
      sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x seen r A := by
  rw [←source_original_SOURCE_MARKED_E_frame_row434 SP sm BP bm J ell m cap patterns
    q rho Vs V mu K zeta theta o k x seen hx,
    source_original_SOURCE_MARKED_E_fibre_frames434]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r hr
  unfold sourceOriginalSourceEFrameFibreRow434 sourceOriginalAbsoluteEFrame434
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro f hf
  dsimp only
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact hFA _ _
    (source_original_SOURCE_ORIENTED_E_reachable434 SP sm BP bm cap J ell m patterns
      x seen o k _ hx f.2.1 f.2.2)
    (source_original_ACTUAL_E_seen_growth434 SP sm BP bm J ell m cap patterns x seen _)

theorem source_original_ACTUAL_E_weighted_majorant434
    (q rho u c : ℝ) (hu : 1 ≤ u) (hc : 0 ≤ c)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hA : ∀ out st,0 ≤ A out st)
    (hFA : ∀ out st,sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) out st →
      ‖F out st‖ ≤ c*u^st.card*A out st) :
    ‖sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F‖ ≤
    c*u^(seen.card+Fintype.card BG*(J+ell)) *
      ∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
        sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta o k x seen r A := by
  have h := source_original_ACTUAL_E_reachable_majorant434 SP sm BP bm J ell m cap patterns
    q rho Vs V mu K zeta theta o k x seen hx F
    (fun out st => c*u^(seen.card+Fintype.card BG*(J+ell))*A out st)
    (fun out st hr hs => (hFA out st hr).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu hs) hc) (hA out st)))
  simpa only [source_original_ABSOLUTE_E_smul434,←Finset.mul_sum] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualOLDFirstCrossingBound -/

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

theorem source_original_ACTUAL_GE_positive434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N n start : ℕ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hA : ∀ out st,0 ≤ A out st)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    0 ≤ sourceOriginalAbsoluteGEChain434 SP sm BP bm J ell m cap patterns
      q u Vs V mu K zeta theta k N n start A y seen := by
  rw [source_original_ABSOLUTE_GE_history_sum434]
  exact Finset.sum_nonneg (fun h _ =>
    source_original_ABSOLUTE_FIXED_HISTORY_nonneg434 SP sm BP bm J ell m cap patterns
      q u Vs V mu K zeta theta k N A hA n h start y seen)

theorem source_original_ACTUAL_GE_tilted_majorant434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q u : ℝ) (hu : 1 ≤ u) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hA : ∀ out st,0 ≤ A out st)
    (hFA : ∀ out st,‖F out st‖ ≤ A out st)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    ‖sourceOriginalFrameGEChain434 SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta k N n start F y seen‖ ≤
    sourceOriginalAbsoluteGEChain434 SP sm BP bm J ell m cap patterns
      q u Vs V mu K zeta theta k N n start A y seen := by
  induction n generalizing start y seen with
  | zero =>
      exact source_original_ACTUAL_G_tilted_majorant434 SP sm BP bm (J+ell)
        hi q 1 u hu N start V mu y seen hy F A hA (fun out st _ => hFA out st)
  | succ n ih =>
      dsimp only [sourceOriginalFrameGEChain434,sourceOriginalAbsoluteGEChain434]
      apply source_original_ACTUAL_G_tilted_majorant434 SP sm BP bm (J+ell)
        hi q 1 u hu N start V mu y seen hy
      · intro out st
        apply Finset.sum_nonneg
        intro r hr
        apply source_original_ABSOLUTE_E_nonneg434
        exact source_original_ACTUAL_GE_positive434 SP sm BP bm J ell m cap patterns
          q u Vs V mu K zeta theta k N n (start+1) A hA
      · intro yg sg hg
        have hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
            (physicalFockProjection SP sm BP bm (J+ell) cap
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg)) sg := by
          rw [source_original_REACHABLE_canonical_projection434 SP sm BP bm (J+ell) cap hcap yg sg hg]
          exact hg
        apply source_original_ACTUAL_E_reachable_majorant434 SP sm BP bm J ell m cap patterns
          q 1 Vs V mu _ zeta theta _ k _ sg hx
        intro out st hr hs
        exact ih (start+1) out st hr

theorem source_original_ACTUAL_tail_factor_ge_one434
    (u : ℝ) (hu : 1 ≤ u) (T s a : ℕ) (ht : T ≤ s) :
    1 ≤ (u^T)⁻¹*u^a*u^s := by
  have hp : 0 < u^T := pow_pos (by linarith) _
  calc
    1 = (u^T)⁻¹*u^T := (inv_mul_cancel₀ hp.ne').symm
    _ ≤ (u^T)⁻¹*u^(a+s) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu (by omega)) (inv_nonneg.mpr hp.le)
    _ = _ := by rw [pow_add]; ring

/-- Actual disjoint first-crossing error is dominated by one positive
time-ordered chain. E births are charged to one common budget; there is
no multiplication by visits or histories and no independent-visit bound. -/
theorem source_original_ACTUAL_OLD_first_crossing_bound434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q u : ℝ) (hu : 1 ≤ u) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N T : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hA : ∀ out st,0 ≤ A out st)
    (hFA : ∀ out st,‖F out st‖ ≤ A out st)
    (n start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    ‖sourceOriginalOLDFirstCrossingFrameGEChain434 SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta k N T n start F y seen‖ ≤
    ((u^T)⁻¹*u^(n*(Fintype.card BG*(J+ell)))*u^seen.card) *
      sourceOriginalAbsoluteGEChain434 SP sm BP bm J ell m cap patterns
        q u Vs V mu K zeta theta k N n start A y seen := by
  have hu0 : 0 ≤ u := by linarith
  have hinv : 0 ≤ (u^T)⁻¹ := inv_nonneg.mpr (pow_nonneg hu0 _)
  induction n generalizing start y seen with
  | zero =>
      dsimp only [sourceOriginalOLDFirstCrossingFrameGEChain434]
      rw [norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hinv (pow_nonneg hu0 _)) (pow_nonneg hu0 _))
        (source_original_ACTUAL_GE_positive434 SP sm BP bm J ell m cap patterns
          q u Vs V mu K zeta theta k N 0 start A hA y seen)
  | succ n ih =>
      dsimp only [sourceOriginalOLDFirstCrossingFrameGEChain434,sourceOriginalAbsoluteGEChain434]
      apply source_original_ACTUAL_G_weighted_majorant434 SP sm BP bm (J+ell)
        hi q 1 u ((u^T)⁻¹*u^((n+1)*(Fintype.card BG*(J+ell)))) hu
        (mul_nonneg hinv (pow_nonneg hu0 _)) N start V mu y seen hy
      · intro out st
        apply Finset.sum_nonneg
        intro r hr
        apply source_original_ABSOLUTE_E_nonneg434
        exact source_original_ACTUAL_GE_positive434 SP sm BP bm J ell m cap patterns
          q u Vs V mu K zeta theta k N n (start+1) A hA
      · intro yg sg hg
        have hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
            (physicalFockProjection SP sm BP bm (J+ell) cap
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg)) sg := by
          rw [source_original_REACHABLE_canonical_projection434 SP sm BP bm (J+ell) cap hcap yg sg hg]
          exact hg
        have hpos := source_original_ACTUAL_GE_positive434 SP sm BP bm J ell m cap patterns
          q u Vs V mu K zeta theta k N n (start+1) A hA
        have hfull := source_original_ACTUAL_GE_tilted_majorant434 SP sm BP bm J ell m cap patterns
          hi hcap q u hu Vs V mu K zeta theta k N F A hA hFA n (start+1)
        by_cases hs : (∑ g : BG,(yg.2 g).2.card) ≤ T
        · rw [if_pos hs]
          have he := source_original_ACTUAL_E_weighted_majorant434 SP sm BP bm J ell m cap patterns
            q 1 u ((u^T)⁻¹*u^(n*(Fintype.card BG*(J+ell)))) hu
            (mul_nonneg hinv (pow_nonneg hu0 _)) Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k _ sg hx
            (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then
              sourceOriginalOLDFirstCrossingFrameGEChain434 SP sm BP bm J ell m cap patterns
                q 1 Vs V mu K zeta theta k N T n (start+1) F out st
              else sourceOriginalFrameGEChain434 SP sm BP bm J ell m cap patterns
                q 1 Vs V mu K zeta theta k N n (start+1) F out st)
            (sourceOriginalAbsoluteGEChain434 SP sm BP bm J ell m cap patterns
              q u Vs V mu K zeta theta k N n (start+1) A) hpos
            (by
              intro out st hr
              by_cases ht : (∑ g : BG,(out.2 g).2.card) ≤ T
              · rw [if_pos ht]
                exact ih (start+1) out st hr
              · rw [if_neg ht]
                apply (hfull out st hr).trans
                apply le_mul_of_one_le_left (hpos out st)
                apply source_original_ACTUAL_tail_factor_ge_one434 u hu
                exact (Nat.le_of_lt (Nat.lt_of_not_ge ht)).trans
                  (source_original_ACTUAL_OLD_le_seen434 SP sm BP bm (J+ell) out st hr))
          convert he using 1 <;> rw [Nat.add_mul,pow_add,pow_add] <;> ring
        · rw [if_neg hs]
          have he := source_original_ACTUAL_E_reachable_majorant434 SP sm BP bm J ell m cap patterns
            q 1 Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k _ sg hx
            (sourceOriginalFrameGEChain434 SP sm BP bm J ell m cap patterns
              q 1 Vs V mu K zeta theta k N n (start+1) F)
            (sourceOriginalAbsoluteGEChain434 SP sm BP bm J ell m cap patterns
              q u Vs V mu K zeta theta k N n (start+1) A)
            (fun out st hr _ => hfull out st hr)
          apply he.trans
          apply le_mul_of_one_le_left
          · apply Finset.sum_nonneg
            intro r hr
            exact source_original_ABSOLUTE_E_nonneg434 SP sm BP bm J ell m cap patterns
              q 1 Vs V mu _ zeta theta _ k _ sg r _ hpos
          · apply source_original_ACTUAL_tail_factor_ge_one434 u hu
            exact (Nat.le_of_lt (Nat.lt_of_not_ge hs)).trans
              (source_original_ACTUAL_OLD_le_seen434 SP sm BP bm (J+ell) yg sg hg)
end Green64Analytic.CorrelationSquare

end

end

