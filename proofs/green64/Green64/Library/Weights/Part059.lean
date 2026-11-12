module

public import Green64.Library.Weights.ActualRhoOneFullEPacket
public import Green64.Library.Correlation.Part047
public import Green64.Library.Weights.Part028
public import Green64.Library.Correlation.Part049

@[expose] public section

/-!
# Weights / Part059

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualPositiveEPacketFactor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

theorem source_original_ACTUAL_E_packet_BIG_factor434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bigSigma bigTau : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0<q) (hq1 : q<1) (hVs : ∀ g,0<Vs g)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (Kcap : ℝ)
    (hK : ∀ target : (g : BG) → Fin (J+ell) → BP g,
      ‖Knu nu aux (fun g i => (st.2 g).1 (bigSigma g i)) target‖ ≤ Kcap) :
    sourceOriginalActualFullEPacket434 SP smallMod BP bigMod
      J ell m cap patterns nu aux st bigSigma bigTau ss tt q rho Vs Vb mu Knu
      zeta theta o k ≤
    ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
      (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖ *
    Kcap * (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
    (∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
      if sourceOriginalMemoryBigFrameLegal434 BP bigMod (J+ell) cap st.2
        (sourceBigShared J ell m (patterns nu)) bigSigma bigTau
        (sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap (patterns nu) aux st bigSigma ss)
        (sourceOrientedStep SP smallMod BP bigMod J ell m cap (patterns nu) aux st bigSigma ss o k) b
      then sourceOriginalMemoryBigFrameNorm434 BP bigMod (J+ell) cap st.2 mu Vb rho
        (sourceBigShared J ell m (patterns nu)) bigSigma bigTau
        (sourceOrientedStep SP smallMod BP bigMod J ell m cap (patterns nu) aux st bigSigma ss o k) b
      else 0) := by
  classical
  let D := sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
    (patterns nu) aux st bigSigma ss
  let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap
    (patterns nu) aux st bigSigma ss o k
  let W := ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
    (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
    (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖
  let Cs := ∏ g : SG,memorySmallRowConstant q (Vs g) ell
  let scalar := fun b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 =>
    originalEdgeScalar (Knu nu aux
      (fun g i => (st.2 g).1 (bigSigma g i))
      (fun g i => (b g).1 (bigTau g i))) zeta theta D o k
  let bn := sourceOriginalMemoryBigFrameNorm434 BP bigMod (J+ell) cap st.2 mu Vb rho
    (sourceBigShared J ell m (patterns nu)) bigSigma bigTau step
  let good := fun b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 =>
    sourceOriginalMemoryBigFrameLegal434 BP bigMod (J+ell) cap st.2
      (sourceBigShared J ell m (patterns nu)) bigSigma bigTau D step b
  let smallK := fun b zs => groupPermutedKernel SP smallMod (J+ell) q Vs
    (sourceSmallShared J ell) step (fun _ _ => scalar b) ss tt st.1 zs
  have hW : 0 ≤ W := norm_nonneg _
  have hbn (b) : 0 ≤ bn b := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hCs : 0 ≤ Cs := by
    have hsqrt : Real.sqrt q < 1 := by
      nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
    have hs : 0<1-Real.sqrt q := sub_pos.mpr hsqrt
    apply Finset.prod_nonneg
    intro g hg
    have hv := hVs g
    dsimp only [memorySmallRowConstant]
    positivity
  have hscalar (b) : ‖scalar b‖ ≤ Kcap := by
    dsimp only [scalar]
    rw [source_original_edge_scalar_norm434 _ _ _ _ _ _ ho]
    exact hK _
  have hsmall (b) : (∑ zs : GroupState SP smallMod (J+ell),‖smallK b zs‖) ≤
      ‖scalar b‖*Cs :=
    source_original_memory_SOURCE_SMALL_group_kernel_row434 SP smallMod J ell
      q Vs hq hq1 hVs step (fun _ _ => scalar b) ss tt st.1
  let choice := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
    J ell m cap patterns nu aux st bigSigma bigTau ss tt
  have hnorm (b) (zs) :
      ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st (choice b zs)‖ =
      (W*bn b)*‖smallK b zs‖ := by
    dsimp only [choice,sourceOriginalMemoryFixedPhysicalChoice434,
      sourceOrientedPhysicalCoefficient,W,bn,sourceOriginalMemoryBigFrameNorm434,
      smallK,scalar,D,step]
    simp only [norm_mul,norm_prod]
  have hrow (b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2) :
      (∑ zs : GroupState SP smallMod (J+ell),
        if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns
          st o k (choice b zs)
        then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st (choice b zs)‖ else 0) ≤
      (W*Kcap*Cs)*(if good b then bn b else 0) := by
    by_cases hb : good b
    · rw [if_pos hb]
      calc
        _ ≤ ∑ zs : GroupState SP smallMod (J+ell),(W*bn b)*‖smallK b zs‖ := by
          apply Finset.sum_le_sum
          intro zs hzs
          split_ifs
          · rw [hnorm]
          · exact mul_nonneg (mul_nonneg hW (hbn b)) (norm_nonneg _)
        _ = (W*bn b)*(∑ zs : GroupState SP smallMod (J+ell),‖smallK b zs‖) :=
          (Finset.mul_sum _ _ _).symm
        _ ≤ (W*bn b)*(‖scalar b‖*Cs) :=
          mul_le_mul_of_nonneg_left (hsmall b) (mul_nonneg hW (hbn b))
        _ ≤ (W*bn b)*(Kcap*Cs) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hscalar b) hCs)
            (mul_nonneg hW (hbn b))
        _ = _ := by ring
    · rw [if_neg hb,mul_zero]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro zs hzs
      apply if_neg
      intro hz
      exact hb hz.2.2.2.1
  unfold sourceOriginalActualFullEPacket434
  calc
    _ ≤ ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
        (W*Kcap*Cs)*(if good b then bn b else 0) :=
      Finset.sum_le_sum (fun b _ => hrow b)
    _ = (W*Kcap*Cs)*∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
        if good b then bn b else 0 := (Finset.mul_sum _ _ _).symm
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedFrameLinearity -/

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

/-- Additivity of the genuine signed ghost G row, retaining numerical
no-rebirth and its full original physical coefficient. -/
theorem source_original_ACTUAL_SIGNED_G_add434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (F A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen (fun out st => F out st+A out st) =
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen F +
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen A := by
  unfold sourceOriginalPhysicalGhostUnseenPrimeRow434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> ring

/-- Additivity of the original SIGNED filtered E frame, including the
selected admissible OLD injection and fully joint K. -/
theorem source_original_ACTUAL_SIGNED_FILTERED_E_add434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (F A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen
      (fun out st => F out st+A out st) =
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen F +
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen A := by
  classical
  unfold sourceOriginalSourceEFrameFilteredRow434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : ∃ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f
  · simp only [dif_pos h]
    by_cases hk : keep x (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns
      x r (Classical.choose h))
    · simp only [if_pos hk]
      ring
    · simp only [if_neg hk,zero_add]
  · simp only [dif_neg h,zero_add]

theorem source_original_ACTUAL_SIGNED_G_zero434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen (fun _ _ => 0) = 0 := by
  classical
  unfold sourceOriginalPhysicalGhostUnseenPrimeRow434
  apply Finset.sum_eq_zero
  intro d hd
  split_ifs <;> simp

theorem source_original_ACTUAL_SIGNED_FILTERED_E_zero434
    (keep : (x : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ) :
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen (fun _ _ => 0) = 0 := by
  classical
  unfold sourceOriginalSourceEFrameFilteredRow434
  apply Finset.sum_eq_zero
  intro r hr
  split_ifs <;> simp
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDIRTYDuhamel -/

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

/-- The literal signed P CLEAN P G/E visit at chronological index i,
with original G, both OLD endpoint projectors and one joint K. -/
def sourceOriginalSignedCleanStep434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T i : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) : ℂ :=
  sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N i V mu
    y seen (fun yg sg =>
      if (∑ g : BG,(yg.2 g).2.card) ≤ T then
        sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu
          (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
          zeta theta (physicalAlternatingSign i) k
          (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
          (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then F out st else 0)
      else 0)

/-- Literal signed G followed by projected E-CLEAN, at the same
chronological index i and with the unchanged full K and seen. -/
def sourceOriginalSignedDIRTYStep434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T i : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) : ℂ :=
  sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell) q rho N i V mu
    y seen (fun yg sg =>
      if (∑ g : BG,(yg.2 g).2.card) ≤ T then
        sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu
          (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i))
          zeta theta (physicalAlternatingSign i) k
          (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
          (fun out st => if (∑ g : BG,(out.2 g).2.card) ≤ T then F out st else 0)
      else 0)

/-- Exact signed additivity of the actual G CLEAN projected-E visit,
not an abstract positive or Markov kernel. -/
theorem source_original_SIGNED_CLEAN_step_add434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T i : ℕ)
    (F A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T i (fun out st => F out st+A out st) y seen =
    sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T i F y seen +
    sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T i A y seen := by
  classical
  let KE := memoryOrientationK BP J ell m patterns K (physicalAlternatingSign i)
  let P : FullPhysicalOutput SP sm BP bm (J+ell) → Prop :=
    fun out => (∑ g : BG,(out.2 g).2.card) ≤ T
  let E (H : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
      FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun yg sg => if P yg then
      sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu KE zeta theta (physicalAlternatingSign i) k
        (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
        (fun out st => if P out then H out st else 0)
      else 0
  change sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen (E (fun out st => F out st+A out st)) =
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen (E F) +
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N i V mu y seen (E A)
  rw [←source_original_ACTUAL_SIGNED_G_add434]
  congr 1
  funext yg sg
  change E (fun out st => F out st+A out st) yg sg =
    E F yg sg + E A yg sg
  dsimp only [E]
  by_cases h : P yg
  · simp only [if_pos h]
    unfold sourceOriginalSourceEFrameCleanRow434
    have hMask :
        (fun out st => if P out then F out st+A out st else 0) =
        (fun out st => (if P out then F out st else 0) +
          (if P out then A out st else 0)) := by
      funext out st
      by_cases hh : P out
      · simp only [if_pos hh]
      · simp only [if_neg hh,zero_add]
    rw [hMask]
    exact source_original_ACTUAL_SIGNED_FILTERED_E_add434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu KE zeta theta (physicalAlternatingSign i) k
      (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
      (fun out st => if P out then F out st else 0)
      (fun out st => if P out then A out st else 0)
  · simp only [if_neg h,zero_add]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDIRTYPositions -/

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

/-- Zero is preserved by the REAL signed G PCLEANP step.
This is derived algebraically from actual additivity, not postulated. -/
theorem source_original_SIGNED_CLEAN_step_zero434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T i : ℕ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T i (fun _ _ => 0) y seen = 0 := by
  have h := source_original_SIGNED_CLEAN_step_add434
    SP sm BP bm J ell m cap patterns
    q rho Vs V mu K zeta theta k N T i
    (fun _ _ => 0) (fun _ _ => 0) y seen
  have hh : sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T i (fun _ _ => 0) y seen =
    sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T i (fun _ _ => 0) y seen +
    sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T i (fun _ _ => 0) y seen := by
    simpa only [zero_add] using h
  linear_combination -hh

/-- Signed original CLEAN step commutes with a finite sum over
candidate insertion positions. No absolute values or cardinality costs. -/
theorem source_original_SIGNED_CLEAN_step_sum434
    {I : Type} (s : Finset I)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T i : ℕ)
    (F : I → FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T i
      (fun out st => ∑ j ∈ s, F j out st) y seen =
    ∑ j ∈ s, sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T i (F j) y seen := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact source_original_SIGNED_CLEAN_step_zero434
        SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T i y seen
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have hf : (fun out st => F a out st + ∑ j ∈ s, F j out st) =
          (fun out st => F a out st) +
          (fun out st => ∑ j ∈ s,F j out st) := rfl
      rw [source_original_SIGNED_CLEAN_step_add434]
      rw [ih]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDIRTYChronology -/

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

/-- The jth genuine signed chronological insertion among n E visits.
Before position j, every G/E transition uses TRUE signed PCLEANP;
at j it uses the original signed P(E-CLEAN)P; afterwards the literal
projected full PEP suffix is retained. The same seen travels through. -/
def sourceOriginalSignedDIRTYAt434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T : ℕ) :
    (n start j : ℕ) →
      (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) →
      FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ
  | 0,_,_,_ => fun _ _ => 0
  | n+1,start,0,F =>
      sourceOriginalSignedDIRTYStep434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T start
        (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T n (start+1) F)
  | n+1,start,j+1,F =>
      sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T start
        (sourceOriginalSignedDIRTYAt434 q rho Vs V mu K zeta theta k N T n (start+1) j F)

/-- The original signed first-insertion recurrence splits EXACTLY
into DIRTY-now with FULL PEP continuation and CLEAN-now with the
remaining signed insertion. No positive or ideal comparison operator. -/
theorem source_original_SIGNED_DIRTY_chain_step434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T n start : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T (n+1) start F y seen =
    sourceOriginalSignedDIRTYStep434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T start
      (sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n (start+1) F) y seen +
    sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T start
      (sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
        SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n (start+1) F) y seen := by
  classical
  let Full := sourceOriginalOLDProjectedFrameGEChain434 SP sm BP bm J ell m cap patterns
    q rho Vs V mu K zeta theta k N T n (start+1) F
  let Insertion := sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
    SP sm BP bm J ell m cap patterns
    q rho Vs V mu K zeta theta k N T n (start+1) F
  let KE := memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start)
  let P : FullPhysicalOutput SP sm BP bm (J+ell) → Prop :=
    fun out => (∑ g : BG,(out.2 g).2.card) ≤ T
  let ED : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun yg sg => sourceOriginalSourceEFrameDirtyRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k
      (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
      (fun out st => if P out then Full out st else 0)
  let EC : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun yg sg => sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu KE zeta theta (physicalAlternatingSign start) k
      (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg) sg
      (fun out st => if P out then Insertion out st else 0)
  let D : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun yg sg => if P yg then ED yg sg else 0
  let C : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun yg sg => if P yg then EC yg sg else 0
  have hsum : (fun yg sg => if P yg then ED yg sg + EC yg sg else 0) =
      (fun yg sg => D yg sg + C yg sg) := by
    funext yg sg
    by_cases hh : P yg
    · simp only [D,C,if_pos hh]
    · simp only [D,C,if_neg hh,zero_add]
  change sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N start V mu y seen
      (fun yg sg => if P yg then ED yg sg+EC yg sg else 0) =
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N start V mu y seen D +
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm (J+ell)
      q rho N start V mu y seen C
  rw [hsum]
  exact source_original_ACTUAL_SIGNED_G_add434
    SP sm BP bm J ell q rho N start V mu y seen D C
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSignedDIRTYSum -/

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

/-- Exact signed chronological position decomposition for the entire
original first-DIRTY frame chain. The jth term consists of j genuine
PCLEANP G/E prefix visits, ONE projected (E-CLEAN) DIRTY visit, and
the full original PEP suffix with correct alternating orientations,
joint K, OLD projector gates and ONE shared numerical seen history.
There is no absolute value and no multiplicative history or visit loss. -/
theorem source_original_SIGNED_first_DIRTY_position_sum434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ)
    (N T n start : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    (∑ j ∈ Finset.range n,
      sourceOriginalSignedDIRTYAt434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n start j F y seen) =
    sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
      SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta k N T n start F y seen := by
  induction n generalizing start y seen with
  | zero =>
      simp only [Finset.range_zero,Finset.sum_empty,
        sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434]
  | succ n ih =>
      let Term := fun j =>
        sourceOriginalSignedDIRTYAt434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T n (start+1) j F
      let Full := sourceOriginalOLDProjectedFrameGEChain434
        SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta k N T n (start+1) F
      have hSum :
          (∑ j ∈ Finset.range n,
            sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
              q rho Vs V mu K zeta theta k N T start (Term j) y seen) =
          sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta k N T start
            (fun out st => ∑ j ∈ Finset.range n, Term j out st) y seen :=
        (source_original_SIGNED_CLEAN_step_sum434
          SP sm BP bm J ell m cap patterns (Finset.range n)
          q rho Vs V mu K zeta theta k N T start Term y seen).symm
      have hTerm :
          (fun out st => ∑ j ∈ Finset.range n, Term j out st) =
          sourceOriginalOLDProjectedDirtyInsertionFrameGEChain434
            SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta k N T n (start+1) F := by
        funext out st
        exact ih (start+1) out st
      rw [Finset.sum_range_succ']
      change (∑ j ∈ Finset.range n,
          sourceOriginalSignedCleanStep434 SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta k N T start (Term j) y seen) +
        sourceOriginalSignedDIRTYStep434 SP sm BP bm J ell m cap patterns
          q rho Vs V mu K zeta theta k N T start Full y seen = _
      rw [hSum,hTerm]
      rw [source_original_SIGNED_DIRTY_chain_step434]
      exact add_comm _ _
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualThetaModeCollision -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The SAME original complex return phase for any source transition
with the same signed physical displacement. This is a unit character. -/
def sourceOriginalActualThetaFrequency434
    (theta : ℝ) (k delta : ℤ) : ℂ :=
  Complex.exp ((2:ℂ) * (Real.pi:ℂ) * Complex.I *
    (theta:ℂ) * ((k*delta:ℤ):ℂ))

theorem source_original_ACTUAL_theta_frequency_add434
    (theta : ℝ) (k a b : ℤ) :
    sourceOriginalActualThetaFrequency434 theta k (a+b) =
      sourceOriginalActualThetaFrequency434 theta k a *
      sourceOriginalActualThetaFrequency434 theta k b := by
  unfold sourceOriginalActualThetaFrequency434
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem source_original_ACTUAL_return_phase_signed_frequency434
    (theta : ℝ) (o k : ℤ) (D : ℕ) :
    originalReturnPhase theta o k D =
      sourceOriginalActualThetaFrequency434 theta k (o*(D:ℤ)) := by
  unfold originalReturnPhase sourceOriginalActualThetaFrequency434
  congr 1
  push_cast
  ring

/-- Original source return phases have exact unit complex norm for ALL
theta,k and positive or negative physical orientation. -/
theorem source_original_ACTUAL_return_phase_norm_one434
    (theta : ℝ) (o k : ℤ) (D : ℕ) :
    ‖originalReturnPhase theta o k D‖ = 1 := by
  unfold originalReturnPhase
  have hp : (2:ℂ) * (Real.pi:ℂ) * Complex.I *
      (theta:ℂ) * ((o*k*(D:ℤ):ℤ):ℂ) =
      ((2*Real.pi*theta*((o*k*(D:ℤ):ℤ):ℝ):ℝ):ℂ) * Complex.I := by
    push_cast
    ring
  push_cast at hp ⊢
  rw [hp]
  have hcast : (2:ℂ) * (Real.pi:ℂ) * (theta:ℂ) *
      ((o:ℂ) * (k:ℂ) * (D:ℂ)) =
      (((2*Real.pi*theta*((o*k*(D:ℤ):ℤ):ℝ)):ℝ):ℂ) := by
    push_cast
    ring
  rw [hcast]
  exact Complex.norm_exp_ofReal_mul_I _

/-- ALL complex same-D cross terms survive theta unchanged.
Fourier orthogonality can discard only genuinely different TOTAL
signed frequencies; it NEVER kills collisions within one D-mode. -/
theorem source_original_ACTUAL_same_D_cross_mode_exact434
    (a b : ℂ) (theta : ℝ) (o k : ℤ) (D : ℕ) :
    star (a * originalReturnPhase theta o k D) *
        (b * originalReturnPhase theta o k D) = star a * b := by
  let phase := originalReturnPhase theta o k D
  have hnorm : ‖phase‖ = 1 :=
    source_original_ACTUAL_return_phase_norm_one434 theta o k D
  have hunit : star phase * phase = 1 := by
    calc
      star phase * phase = phase * star phase := mul_comm _ _
      _ = ((‖phase‖^2 : ℝ) : ℂ) := by
        simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using
          (Complex.mul_conj phase)
      _ = 1 := by rw [hnorm]; norm_num
  calc
    star (a*phase) * (b*phase) =
        (star a * b) * (star phase * phase) := by
          rw [star_mul]
          ring
    _ = star a * b := by rw [hunit, mul_one]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualThetaLaurent -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Genuine source return phase as an additive-in-displacement unit
character. One theta is shared by all chronological visits. -/
def sourceOriginalActualThetaCharacter434
    (theta : ℝ) : Multiplicative ℤ →* ℂ where
  toFun n := sourceOriginalActualThetaFrequency434 theta 1 n.toAdd
  map_one' := by
    change sourceOriginalActualThetaFrequency434 theta 1 0 = 1
    simp [sourceOriginalActualThetaFrequency434]
  map_mul' a b := by
    change sourceOriginalActualThetaFrequency434 theta 1 (a.toAdd+b.toAdd) =
      sourceOriginalActualThetaFrequency434 theta 1 a.toAdd *
      sourceOriginalActualThetaFrequency434 theta 1 b.toAdd
    exact source_original_ACTUAL_theta_frequency_add434 theta 1 a.toAdd b.toAdd

/-- Laurent-polynomial evaluation in the original common theta phase.
Multiplication of polynomials corresponds to adding chronological
signed integer displacements, not independent theta resampling. -/
def sourceOriginalActualThetaEval434
    (theta : ℝ) : AddMonoidAlgebra ℂ ℤ →ₐ[ℂ] ℂ :=
  (AddMonoidAlgebra.lift ℂ ℂ ℤ) (sourceOriginalActualThetaCharacter434 theta)

theorem source_original_ACTUAL_theta_eval_single434
    (theta : ℝ) (d : ℤ) (z : ℂ) :
    sourceOriginalActualThetaEval434 theta
      (AddMonoidAlgebra.single d z) =
      z * sourceOriginalActualThetaFrequency434 theta 1 d := by
  simpa [sourceOriginalActualThetaEval434,
    sourceOriginalActualThetaCharacter434, smul_eq_mul] using
    (AddMonoidAlgebra.lift_single
      (sourceOriginalActualThetaCharacter434 theta) d z)

theorem source_original_ACTUAL_return_phase_eval_single434
    (theta : ℝ) (o k : ℤ) (D : ℕ) (z : ℂ) :
    sourceOriginalActualThetaEval434 theta
      (AddMonoidAlgebra.single (o*k*(D:ℤ)) z) =
        z * originalReturnPhase theta o k D := by
  rw [source_original_ACTUAL_theta_eval_single434]
  congr 1
  unfold originalReturnPhase sourceOriginalActualThetaFrequency434
  congr 1
  push_cast
  ring
end Green64Analytic.CorrelationSquare

end

end

