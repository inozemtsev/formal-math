module

public import Green64.Library.Correlation.Part045
public import Green64.Library.Correlation.Part049

@[expose] public section

/-!
# Weights / ActualRhoOneFullEPacket

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualRhoOneFullEPacket -/

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

/-- A literal original coefficient packet. It retains all legality
tests, auxiliary bans, the signed Fourier/Mellin scalar, stores,
ordered promotions, all target states and both permutation masses. -/
def sourceOriginalActualFullEPacket434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bigSigma bigTau : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) : ℝ :=
  ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
  ∑ zs : GroupState SP smallMod (J+ell),
    let z := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
      J ell m cap patterns nu aux st bigSigma bigTau ss tt b zs
    if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z
    then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st z‖ else 0

/-- Exact transfer from the full BIG row to the literal
SMALL x BIG source packet. The global joint K is bounded once, after
fixing the full BIG endpoints; it is never separated into functions of
individual groups or endpoints. -/
private theorem full_packet_bound434
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


/-- Complete literal RAW/comparison E packet at rho=1. The cap of the
actual two-block joint K is proved; both phases, endpoints, auxiliary
data, permutations and all OLD choices are retained. This is a growing
absolute bound intended for a birth tail, not a comparison saving. -/
theorem source_original_ACTUAL_RAW_COMPARISON_full_E_packet434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (Vb : G → ℝ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (cap : G → ℕ)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi : ℝ)
    (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
    (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
    (hxi : 0 < xi)
    (nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ nu))
    (st : FullPhysicalState SP smallMod (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) cap)
    (bs bt : BigGroupPerm (BG:=G) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q : ℝ) (Vs : SG → ℝ) (hq : 0 < q) (hq1 : q < 1) (hVs : ∀ g,0 < Vs g)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hmu : ∀ g p,0 ≤ mu g p) (R : ℝ) (hR : 1 ≤ R)
    (hMass : ∀ g,(∑ p,mu g p) ≤ R) (hVb : ∀ g,0 < Vb g)
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) :
    let patterns := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 P Vb blockA blockB J ell m hmJ Q hA hB xi
    sourceOriginalActualFullEPacket434 SP smallMod (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) J ell m cap patterns nu aux st bs bt ss tt
      q 1 Vs Vb mu K zeta theta o k ≤
    ‖(sourceAuxMass (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
        J m Vb (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=G) (J+ell):ℂ) *
      (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖ *
    sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu *
    (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
    (∏ g : G,(4:ℝ)^(ell+m)*
      ((max 1 ((st.2 g).2.1.val:ℝ))^(ell+m)*
        ((max 1 (Vb g)⁻¹)^(ell+m)*R^(ell+m)))) := by
  dsimp only
  let patterns := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let K := sourceOriginalMemoryRawComparisonK434 P Vb blockA blockB J ell m hmJ Q hA hB xi
  have hCs : 0 ≤ (∏ g : SG,memorySmallRowConstant q (Vs g) ell) := by
    have hsqrt : Real.sqrt q < 1 := by
      nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
    have hs : 0 < 1-Real.sqrt q := sub_pos.mpr hsqrt
    apply Finset.prod_nonneg
    intro g hg
    have hv := hVs g
    dsimp only [memorySmallRowConstant]
    positivity
  have hK := source_original_memory_RAW_COMPARISON_K_cap434 P Vb blockA blockB J ell m hmJ
    Q hA hB xi hhA hhB hxi nu aux
    (fun g i => (st.2 g).1 (bs g i))
  apply (full_packet_bound434 SP smallMod (fun g => {p : ℕ // p ∈ P g})
    (fun _ p => p.val) J ell m cap patterns nu aux st bs bt ss tt
    q 1 Vs Vb hq hq1 hVs mu K zeta theta o k ho
    (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu) hK).trans
  apply mul_le_mul_of_nonneg_left
    (source_original_ACTUAL_BIG_rho_one_frame434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) cap st.2 mu hmu Vb R hVb hR hMass
      (sourceBigShared J ell m (patterns nu)) bs bt
      (sourceOrientedPhysicalD SP smallMod (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) J ell m cap (patterns nu) aux st bs ss)
      (sourceOrientedStep SP smallMod (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) J ell m cap (patterns nu) aux st bs ss o k)
      (ell+m) (memory_source_unshared_count J ell m (patterns nu)))
  exact mul_nonneg (mul_nonneg (norm_nonneg _)
    (source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi nu)) hCs
end Green64Analytic.CorrelationSquare

end

end

