module

public import Green64.Library.Weights.Part059
public import Green64.Library.Weights.ActualPositiveEAssembly
public import Green64.Library.Correlation.Part051
public import Green64.Library.Correlation.Part049

@[expose] public section

/-!
# Weights / Part064

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualPositiveESourceBox -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Full source E row at rho=1, with every auxiliary and permutation
average assembled exactly. The threshold precedes all moving finite
families, slots, states and joint kernels. hK is only a pointwise
joint cap, discharged for the actual RAW/comparison kernel below. -/
theorem eventually_source_original_ACTUAL_full_E_source_box434
    (c vmin : ℝ) (hc : 0 < c) (hv : 0 < vmin) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      {BG : Type} [Fintype BG] [DecidableEq BG]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (hi : ∀ g,Function.Injective (bm g))
      (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
      (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
      (V : BG → ℝ) (hV : ∀ g,vmin ≤ V g)
      (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
      (hmin : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (hmax : ∀ g p,(bm g p:ℝ) ≤ Real.exp (Real.sqrt L))
      (J ell m : ℕ) {Nu : Type} [Fintype Nu]
      (patterns : Nu → SourcePattern BG J m)
      (Kcap : Nu → ℝ) (hK0 : ∀ nu,0 ≤ Kcap nu)
      (K : SourcePatternK BP J ell m patterns)
      (hK : ∀ nu aux s t,‖K nu aux s t‖ ≤ Kcap nu)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
      (x : FullPhysicalState SP sm BP bm (J+ell) (fun g => Fintype.card (BP g))),
      sourceOriginalActualFullERow434 SP sm BP bm J ell m
        (fun g => Fintype.card (BP g)) patterns q 1 Vs V
        (physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V)
        K zeta theta o k x ≤
      (∑ nu,Kcap nu) * (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
        (16*max 1 vmin⁻¹*Real.exp (Real.sqrt L))^((ell+m)*Fintype.card BG) := by
  filter_upwards [eventually_source_original_ACTUAL_BIG_rho_one_source_box434 c vmin hc hv] with L hL
  intro SG _ _ SP _ _ sm _ BG _ _ BP _ _ bm _ hi q hq hq1 Vs hVs V hV hHarmonic
    hmin hmax J ell m Nu _ patterns Kcap hK0 K hK zeta theta o k ho x
  let cap := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V
  let Cs := ∏ g : SG,memorySmallRowConstant q (Vs g) ell
  let Cb := (16*max 1 vmin⁻¹*Real.exp (Real.sqrt L))^((ell+m)*Fintype.card BG)
  have hVp (g : BG) : 0 < V g := hv.trans_le (hV g)
  have hCs : 0 ≤ Cs := by
    have hsqrt : Real.sqrt q < 1 := by
      nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
    have hs : 0 < 1-Real.sqrt q := sub_pos.mpr hsqrt
    apply Finset.prod_nonneg
    intro g hg
    have hv' := hVs g
    dsimp only [memorySmallRowConstant]
    positivity
  rw [source_original_ACTUAL_full_E_row_packets434]
  change _ ≤ (∑ nu,Kcap nu)*Cs*Cb
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro nu hnu
  let W := fun aux : SourceBigAux BP J m (patterns nu) =>
    ‖(sourceAuxMass BP bm J m V (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
      (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖
  calc
    _ ≤ ∑ aux : SourceBigAux BP J m (patterns nu),
        ∑ bs : BigGroupPerm (BG:=BG) (J+ell),∑ bt : BigGroupPerm (BG:=BG) (J+ell),
        ∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
          W aux*(Kcap nu*Cs*Cb) := by
      apply Finset.sum_le_sum
      intro aux haux
      apply Finset.sum_le_sum
      intro bs hbs
      apply Finset.sum_le_sum
      intro bt hbt
      apply Finset.sum_le_sum
      intro ss hss
      apply Finset.sum_le_sum
      intro tt htt
      have hp := source_original_ACTUAL_E_packet_BIG_factor434
        SP sm BP bm J ell m cap patterns nu aux x bs bt ss tt
        q 1 Vs V hq hq1 hVs mu K zeta theta o k ho (Kcap nu) (hK nu aux _)
      have hb := hL BP bm hi q hq.le hq1.le V hV hHarmonic hmin hmax
        J ell m (patterns nu) x.2 bs bt
        (sourceOrientedPhysicalD SP sm BP bm J ell m cap (patterns nu) aux x bs ss)
        (sourceOrientedStep SP sm BP bm J ell m cap (patterns nu) aux x bs ss o k)
      exact (hp.trans (mul_le_mul_of_nonneg_left hb
        (mul_nonneg (mul_nonneg (norm_nonneg _) (hK0 nu)) hCs))).trans_eq (by
          dsimp only [W,Cs,Cb];ring)
    _ = _ := by
      simp_rw [←Finset.sum_mul]
      rw [source_original_memory_ALL_OUTER_total_mass434 (SG:=SG) BP bm
        J ell m V hVp hHarmonic (patterns nu),one_mul]

/-- The actual RAW plus all original comparison terms, including the
orientation-dependent endpoint transpose. No assumed analytic norm
or smallness hypothesis remains. This is an absolute growth bound. -/
theorem eventually_source_original_ACTUAL_RAW_COMPARISON_full_E_source_box434
    (c vmin : ℝ) (hc : 0 < c) (hv : 0 < vmin) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
      (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
      (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
      (V : G → ℝ) (hV : ∀ g,vmin ≤ V g)
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ P g},1/(p.val:ℝ)=V g)
      (hmin : ∀ g (p : {p : ℕ // p ∈ P g}),Real.exp (L^c) ≤ (p.val:ℝ))
      (hmax : ∀ g (p : {p : ℕ // p ∈ P g}),(p.val:ℝ) ≤ Real.exp (Real.sqrt L))
      (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
      (Q : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi : ℝ)
      (hhA : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA nu)
      (hhB : ∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB nu)
      (hxi : 0 < xi) (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
      (x : FullPhysicalState SP sm (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
        (J+ell) (fun g => Fintype.card {p : ℕ // p ∈ P g})) (seen : Finset ℕ),
      let patterns := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
      let K := sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q hA hB xi
      (∑ r : SourceOriginalSourceEFrame434 SP sm (fun g => {p : ℕ // p ∈ P g})
          J ell m patterns,
        sourceOriginalAbsoluteEFrame434 SP sm (fun g => {p : ℕ // p ∈ P g})
          (fun _ p => p.val) J ell m (fun g => Fintype.card {p : ℕ // p ∈ P g}) patterns
          q 1 Vs V
          (physicalSourceMuTilde (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
            q (2*Nat.ceil (L^(0.52:ℝ))) V)
          (memoryOrientationK (fun g => {p : ℕ // p ∈ P g}) J ell m patterns K o)
          zeta theta o k x seen r (fun _ _ => 1)) ≤
      (∑ nu : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
        sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi nu) *
      (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
      (16*max 1 vmin⁻¹*Real.exp (Real.sqrt L))^((ell+m)*Fintype.card G) := by
  filter_upwards [eventually_source_original_ACTUAL_full_E_source_box434 c vmin hc hv] with L hL
  intro SG _ _ SP _ _ sm _ G _ _ P _ q hq hq1 Vs hVs V hV hHarmonic hmin hmax
    blockA blockB J ell m hmJ Q hA hB xi hhA hhB hxi zeta theta o k ho x seen
  dsimp only
  apply (source_original_ABSOLUTE_E_frames_le_full_row434
    SP sm (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) J ell m
    (fun g => Fintype.card {p : ℕ // p ∈ P g})
    (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
    q 1 Vs V _ _ zeta theta o k x seen).trans
  refine hL SP sm (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
    (fun _ => Subtype.val_injective) q hq hq1 Vs hVs V hV hHarmonic hmin hmax
    J ell m _ _ (source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi)
    _ ?_ zeta theta o k ho x
  intro nu aux s t
  unfold memoryOrientationK
  split_ifs
  · exact source_original_memory_RAW_COMPARISON_K_cap434 P V blockA blockB J ell m hmJ
      Q hA hB xi hhA hhB hxi nu aux s t
  · exact source_original_memory_RAW_COMPARISON_K_cap434 P V blockA blockB J ell m hmJ
      Q hA hB xi hhA hhB hxi nu aux t s
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPositiveHistoryTransfer -/

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

/-- Actual background history is dominated by a common positive
history operator. The only increase is extending the G birth tilt to
all primes. E coefficients and the arbitrary joint observation are
kept literally, with background reattached before every continuation. -/
theorem source_original_ACTUAL_BACKGROUND_history_le_common434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (background : (g : BG) → Finset (BP g))
    (q u : ℝ) (hu : 1 ≤ u)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hA : ∀ out st,0 ≤ A out st)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (havoid : sourceOriginalFrameHistoryAvoids434 SP sm BP J ell m patterns background n h)
    (start : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen) :
    sourceOriginalAbsoluteBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q u Vs V mu K zeta theta k N n h start
      (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y) A y seen ≤
    sourceOriginalAbsoluteFixedFrameChain434 SP sm BP bm J ell m cap patterns
      q u Vs V mu K zeta theta k N n h start A y seen := by
  induction n generalizing start y seen with
  | zero =>
      exact source_original_ABSOLUTE_G_background_le_all_tilt434
        SP sm BP bm (J+ell) hi background q 1 u hu N start V mu y seen A hA
  | succ n ih =>
      rcases h with ⟨r,h⟩
      dsimp only [sourceOriginalAbsoluteBackgroundChain434,sourceOriginalAbsoluteFixedFrameChain434]
      refine le_trans (source_original_ABSOLUTE_G_background_le_all_tilt434
        SP sm BP bm (J+ell) hi background q 1 u hu N start V mu y seen _ ?_) ?_
      · intro yg sg
        apply source_original_ABSOLUTE_E_nonneg434
        intro out st
        exact source_original_ABSOLUTE_BACKGROUND_HISTORY_nonneg434
          SP sm BP bm J ell m cap patterns background q u Vs V mu K zeta theta k N
          A hA n h (start+1) _ _ _
      · unfold sourceOriginalAbsoluteUnseenPrimeG434
        apply Finset.sum_le_sum
        intro d hd
        split_ifs with he
        · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          dsimp only
          let yg := sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm (J+ell) y
            (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm (J+ell) y d)
          let sg := seen ∪ sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm (J+ell) y d
          have hg : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) yg sg :=
            source_original_ACTUAL_UNSEEN_G_witness_reachable434
              SP sm BP bm (J+ell) hi y seen hy d he
          have hs : sourceOriginalActiveFrameStep434 SP sm BP bm J ell m cap patterns
              (sourceOriginalPhysicalActiveSkeleton434 SP sm BP bm J ell y) r
              (physicalAlternatingSign start) k =
            sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1
              (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap yg)
              r.2.2.1.1 r.2.2.2.1 (physicalAlternatingSign start) k := rfl
          rw [source_original_ABSOLUTE_E_background_frame_row434
            SP sm BP bm J ell m cap patterns hcap background yg sg hg q Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta r (physicalAlternatingSign start) k havoid.1]
          rw [source_original_ABSOLUTE_E_background_seen_row434
            SP sm BP bm J ell m cap patterns (hi := hi) (background := background)
            q 1 Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
              (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background yg))
            sg r (physicalAlternatingSign start) k havoid.1]
          rw [hs]
          unfold sourceOriginalAbsoluteEFrame434
          apply Finset.sum_le_sum
          intro f hf
          dsimp only
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          have hf' := (source_original_SOURCE_E_frame_background_seen434
            SP sm BP bm J ell m cap patterns hi background
            (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
              (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background yg))
            sg r (physicalAlternatingSign start) k havoid.1 f.1).mpr f.2
          have hr := source_original_SOURCE_E_background_frame_reachable434
            SP sm BP bm J ell m cap patterns hcap background yg sg hg r
            (physicalAlternatingSign start) k f.1 hf'
          have hu' (births : Finset ℕ) :
              ((sg \ sourceOriginalNumericBackground434 BP bm background) ∪ births) ∪
                (sg ∩ sourceOriginalNumericBackground434 BP bm background) = sg ∪ births := by
            ext p
            simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
            tauto
          rw [hu']
          exact ih h havoid.2 (start+1) _ _ hr
        · rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualPositiveCommonRoot -/

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

/-- Common positive root: original vacuum/orbit measure, initial
distinctness and all original frames; all G births are tilted.
No background depending on the future history occurs on the RHS. -/
def sourceOriginalAbsoluteCommonMemoryRoot434
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
          sourceOriginalAbsoluteFixedFrameChain434 SP sm BP bm J ell m cap patterns
            q u Vs V mu K zeta theta k N N h 0
            (fun out _ => ‖physicalVacuum SP sm BP bm J ell out‖)
            y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      else 0)

/-- Full-root domination, with the actual history-dependent background
eliminated inside each summand before any history sum is bounded. -/
theorem source_original_ACTUAL_BACKGROUND_root_le_common434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q u : ℝ) (hu : 1 ≤ u) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    sourceOriginalAbsoluteBackgroundMemoryRoot434 SP sm BP bm J ell m cap patterns
      q u Vs V K zeta theta k R ≤
    sourceOriginalAbsoluteCommonMemoryRoot434 SP sm BP bm J ell m cap patterns
      q u Vs V K zeta theta k R := by
  unfold sourceOriginalAbsoluteBackgroundMemoryRoot434 sourceOriginalAbsoluteCommonMemoryRoot434
  dsimp only
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro y hy
  by_cases hv : physicalVacuum SP sm BP bm J ell y = 0
  · simp only [hv,norm_zero,mul_zero,zero_mul,le_refl]
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
  · rw [if_pos hn,if_pos hn]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    apply Finset.sum_le_sum
    intro h hh
    exact source_original_ACTUAL_BACKGROUND_history_le_common434
      SP sm BP bm J ell m cap patterns hi hcap
      (fun g => Finset.univ \
        sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns y (2*R) h g)
      q u hu Vs V (physicalSourceMuTilde BP bm q (2*R) V) K zeta theta k (2*R)
      (fun out _ => ‖physicalVacuum SP sm BP bm J ell out‖) (fun _ _ => norm_nonneg _)
      (2*R) h
      (source_original_FULL_ACTIVE_HISTORY_complement_avoids434
        SP sm BP bm J ell m patterns y (2*R) h)
      0 y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
      (source_original_MEMORY_initial_reachable434 SP sm BP bm J ell y hv hn)
  · simp only [if_neg hn,mul_zero,le_refl]

/-- The genuine signed terminal background-birth tail is controlled by
a single common positive root, not by a history-count multiple. -/
theorem source_original_ACTUAL_ROOT_birth_tail_common434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q u : ℝ) (hu : 1 ≤ u) (H : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R : ℕ) :
    ‖sourceOriginalBackgroundBirthTailMemoryRoot434 SP sm BP bm J ell m cap patterns
      q H Vs V K zeta theta k R‖ ≤
    (u^H)⁻¹ * sourceOriginalAbsoluteCommonMemoryRoot434 SP sm BP bm J ell m cap patterns
      q u Vs V K zeta theta k R := by
  apply (source_original_ACTUAL_ROOT_background_birth_tail434
    SP sm BP bm J ell m cap patterns hi q u hu H Vs V K zeta theta k R).trans
  exact mul_le_mul_of_nonneg_left
    (source_original_ACTUAL_BACKGROUND_root_le_common434
      SP sm BP bm J ell m cap patterns hi hcap q u hu Vs V K zeta theta k R)
    (inv_nonneg.mpr (pow_nonneg (by linarith : 0 ≤ u) H))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualOLDRemoval -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

theorem source_original_ACTUAL_tail_factor_budget434
    (u : ℝ) (hu : 1 ≤ u) (T H a s : ℕ) (hm : H+a+s ≤ T) :
    (u^T)⁻¹*u^a*u^s ≤ (u^H)⁻¹ := by
  have hpos : 0 < u := by linarith
  apply (mul_le_mul_iff_right₀ (pow_pos hpos H)).mp
  calc
    _ = (u^T)⁻¹*u^(H+a+s) := by simp only [pow_add]; ring
    _ ≤ (u^T)⁻¹*u^T :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hu hm)
        (inv_nonneg.mpr (pow_nonneg hpos.le _))
    _ = _ := by rw [inv_mul_cancel₀ (pow_pos hpos T).ne',mul_inv_cancel₀ (pow_pos hpos H).ne']

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Finite removal of BOTH original total-OLD endpoint projectors at
EVERY E visit. The discrepancy is that of the original signed root.
All vacuum/Fock/baseline factors and the complete joint K are retained.
The all-birth tilt pays a single global E budget. rho cancels exactly. -/
theorem source_original_ACTUAL_OLD_projector_discrepancy_common434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho u : ℝ) (hrho : rho ≠ 0) (hu : 1 ≤ u)
    (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T H : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p)
    (hm : H+(2*R+1)*(Fintype.card BG*(J+ell)) ≤ T) :
    ‖memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R -
      sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T‖ ≤
    (u^H)⁻¹ * sourceOriginalAbsoluteCommonMemoryRoot434 SP sm BP bm J ell m cap patterns
      q u Vs V K zeta theta k R := by
  rw [source_original_MEMORY_OLD_discrepancy_rho_invariant434
    SP sm BP bm J ell m cap patterns q rho hrho Vs V K zeta theta k R T]
  unfold memorySourceRoot sourceOriginalOLDProjectedMemoryRoot434
    sourceOriginalAbsoluteCommonMemoryRoot434
  dsimp only
  rw [←mul_sub,←Finset.sum_sub_distrib,norm_mul]
  calc
    _ ≤ ‖(physicalSourceBaselineProduct BP bm q (2*R) : ℂ)‖ *
      ∑ y ∈ physicalFockOrbitSupport SP sm BP bm (J+ell) cap,
        ‖(physicalOrbitMass SP sm BP bm (J+ell) cap Vs
            (physicalSourceMuTilde BP bm q (2*R) V) y : ℂ) *
            star (physicalVacuum SP sm BP bm J ell y) *
            (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
              memorySourceGEChain SP sm BP bm J ell m patterns cap q 1 Vs V
                (physicalSourceMuTilde BP bm q (2*R) V) K zeta theta k (2*R) (2*R) 0
                (fun out _ => physicalVacuum SP sm BP bm J ell out)
                y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset else 0)
          -
          (physicalOrbitMass SP sm BP bm (J+ell) cap Vs
            (physicalSourceMuTilde BP bm q (2*R) V) y : ℂ) *
            star (physicalVacuum SP sm BP bm J ell y) *
            (if (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup then
              sourceOriginalOLDProjectedMemoryGEChain434 SP sm BP bm J ell m cap patterns
                q 1 Vs V (physicalSourceMuTilde BP bm q (2*R) V) K zeta theta k (2*R) T (2*R) 0
                (fun out _ => physicalVacuum SP sm BP bm J ell out)
                y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset else 0)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ _ := by
      rw [mul_left_comm (u^H)⁻¹]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y hy
      by_cases hv : physicalVacuum SP sm BP bm J ell y=0
      · simp only [hv,star_zero,norm_zero,mul_zero,zero_mul,sub_zero,le_refl]
      by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
      · simp only [if_pos hn]
        have hr := source_original_MEMORY_initial_reachable434 SP sm BP bm J ell y hv hn
        rw [source_original_MEMORY_frame_chain_exact434 SP sm BP bm J ell m cap patterns
          hi hcap q 1 Vs V _ hVs hmu K zeta theta k (2*R) _ (2*R) 0 y _ hr]
        rw [source_original_MEMORY_OLD_projected_frame_exact434 SP sm BP bm J ell m cap patterns
          hi hcap q 1 Vs V _ hVs hmu K zeta theta k (2*R) T _ (2*R) 0 y _ hr]
        rw [←mul_sub,source_original_MEMORY_OLD_first_crossing_partition434,
          norm_mul,norm_mul,norm_star]
        rw [←source_original_ABSOLUTE_GE_history_sum434]
        have hb := source_original_ACTUAL_OLD_first_crossing_bound434
          SP sm BP bm J ell m cap patterns hi hcap q u hu Vs V
          (physicalSourceMuTilde BP bm q (2*R) V) K zeta theta k (2*R) T
          (fun out _ => physicalVacuum SP sm BP bm J ell out)
          (fun out _ => ‖physicalVacuum SP sm BP bm J ell out‖)
          (fun _ _ => norm_nonneg _) (fun _ _ => le_rfl) (2*R) 0 y _ hr
        have hiSeen := source_original_ACTUAL_initial_seen_bound434 SP sm BP bm J ell y
        have hbudget := source_original_ACTUAL_tail_factor_budget434 u hu T H
          ((2*R)*(Fintype.card BG*(J+ell)))
          (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset.card
          (by nlinarith)
        have hpos := source_original_ACTUAL_GE_positive434 SP sm BP bm J ell m cap patterns
          q u Vs V (physicalSourceMuTilde BP bm q (2*R) V) K zeta theta k
          (2*R) (2*R) 0 (fun out _ => ‖physicalVacuum SP sm BP bm J ell out‖)
          (fun _ _ => norm_nonneg _) y
          (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset
        have hh := hb.trans (mul_le_mul_of_nonneg_right hbudget hpos)
        calc
          _ ≤ (‖(physicalOrbitMass SP sm BP bm (J+ell) cap Vs
                  (physicalSourceMuTilde BP bm q (2*R) V) y : ℂ)‖ *
                ‖physicalVacuum SP sm BP bm J ell y‖) *
              ((u^H)⁻¹ * sourceOriginalAbsoluteGEChain434 SP sm BP bm J ell m cap patterns
                q u Vs V (physicalSourceMuTilde BP bm q (2*R) V) K zeta theta k
                (2*R) (2*R) 0 (fun out _ => ‖physicalVacuum SP sm BP bm J ell out‖)
                y (physicalOutputInitialBirths SP sm BP bm J ell y).toFinset) :=
            mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = _ := by ring
      · simp only [if_neg hn,mul_zero,sub_zero,norm_zero,zero_mul,le_refl]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFullMemoryErrorSplit -/

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


/-- True finite PEP-PCLEANP identity using only source-relevant
BIG injectivity/cap and positivity. No auxiliary MemorySourceDomain
field (e.g., exact SMALL harmonic normalization) is needed. -/
theorem source_original_MEMORY_PEP_PCLEAN_physical_DIRTY_general434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T -
    sourceOriginalOLDProjectedCleanMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
      SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T := by
  rw [source_original_MEMORY_OLD_projected_root_frame_exact434
    SP sm BP bm J ell m cap patterns hi hcap q rho Vs V K zeta theta k R T hVs hmu]
  unfold sourceOriginalOLDProjectedFrameMemoryRoot434
    sourceOriginalOLDProjectedCleanMemoryRoot434
    sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
  dsimp only
  rw [←mul_sub,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hv : physicalVacuum SP sm BP bm J ell y=0
  · simp only [hv,star_zero,mul_zero,zero_mul,sub_self]
  · by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
    · simp only [if_pos hn]
      rw [←mul_sub,source_original_MEMORY_PEP_PCLEAN_frame_telescoping434]
      rw [source_original_ACTUAL_DIRTY_insertion_physical_exact434
        SP sm BP bm J ell m cap patterns hi hcap q rho Vs V
        (physicalSourceMuTilde BP bm q (2*R) V) hVs hmu K zeta theta k
        (2*R) T (fun out _ => physicalVacuum SP sm BP bm J ell out)
        (2*R) 0 y _
        (source_original_MEMORY_initial_reachable434 SP sm BP bm J ell y hv hn)]
    · simp only [if_neg hn,mul_zero,sub_self]

/-- All original full-vs-projector error is split into ONE already-paid
OLD tail plus the exact chronological marked DIRTY insertion root.
A norm inequality, not a claim of DIRTY saving. -/
theorem source_original_MEMORY_full_to_CLEAN_error_split434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    ‖memorySourceRoot SP sm BP bm J ell m patterns cap
        q rho Vs V K zeta theta k R -
      sourceOriginalOLDProjectedCleanMemoryRoot434 SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T‖ ≤
    ‖memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R -
      sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T‖ +
    ‖sourceOriginalOLDProjectedDirtyPhysicalInsertionMemoryRoot434
        SP sm BP bm J ell m cap patterns q rho Vs V K zeta theta k R T‖ := by
  have hsplit := source_original_MEMORY_PEP_PCLEAN_physical_DIRTY_general434
    SP sm BP bm J ell m cap patterns hi hcap q rho Vs V K zeta theta k R T hVs hmu
  calc
    _ = ‖(memorySourceRoot SP sm BP bm J ell m patterns cap
          q rho Vs V K zeta theta k R -
          sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
            q rho Vs V K zeta theta k R T) +
          (sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
            q rho Vs V K zeta theta k R T -
          sourceOriginalOLDProjectedCleanMemoryRoot434 SP sm BP bm J ell m cap patterns
            q rho Vs V K zeta theta k R T)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans_eq (by rw [hsplit])
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualProjectedDirtyReduction -/

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

/-- No full MemorySourceDomain is needed for this exact identity: the
positivity and reachability data used by the physical Fock frame suffice.
In particular q/rho need not be artificially changed. -/
theorem source_original_MEMORY_PEP_PCLEAN_root_telescoping_of_mass434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T -
    sourceOriginalOLDProjectedCleanMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T =
    sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434 SP sm BP bm J ell m cap patterns
      q rho Vs V K zeta theta k R T := by
  rw [source_original_MEMORY_OLD_projected_root_frame_exact434
    SP sm BP bm J ell m cap patterns hi hcap q rho Vs V K zeta theta k R T hVs hmu]
  unfold sourceOriginalOLDProjectedFrameMemoryRoot434
    sourceOriginalOLDProjectedCleanMemoryRoot434
    sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434
  dsimp only
  rw [←mul_sub,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup
  · simp only [if_pos hn]
    rw [←mul_sub,source_original_MEMORY_PEP_PCLEAN_frame_telescoping434]
  · simp only [if_neg hn,mul_zero,sub_self]

/-- Exact full-root reduction: all residual error after replacing the
PEP E chain by PCLEANP plus one DIRTY insertion is JUST the previously
proved global OLD-tail discrepancy, with no extra assumption on the E
continuations. This algebraic identity is not an insertion saving. -/
theorem source_original_MEMORY_FULL_to_clean_plus_DIRTY_exact434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p) :
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R -
      sourceOriginalOLDProjectedCleanMemoryRoot434 SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T -
      sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434 SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T =
    memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R -
      sourceOriginalOLDProjectedMemoryRoot434 SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T := by
  have h := source_original_MEMORY_PEP_PCLEAN_root_telescoping_of_mass434
    SP sm BP bm J ell m cap patterns hi hcap q rho Vs V K zeta theta k R T hVs hmu
  rw [←h]
  ring

/-- The full signed root has a quantified positive-envelope error
AFTER the exact CLEAN/one-DIRTY insertion decomposition. The real
mathematical missing estimate is now on the insertion root itself. -/
theorem source_original_MEMORY_FULL_to_clean_plus_DIRTY_cost434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q rho u : ℝ) (hrho : rho ≠ 0) (hu : 1 ≤ u)
    (Vs : SG → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (R T H : ℕ)
    (hVs : ∀ g,0 < Vs g)
    (hmu : ∀ g p,0 < physicalSourceMuTilde BP bm q (2*R) V g p)
    (hm : H+(2*R+1)*(Fintype.card BG*(J+ell)) ≤ T) :
    ‖memorySourceRoot SP sm BP bm J ell m patterns cap q rho Vs V K zeta theta k R -
      sourceOriginalOLDProjectedCleanMemoryRoot434 SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T -
      sourceOriginalOLDProjectedDirtyInsertionMemoryRoot434 SP sm BP bm J ell m cap patterns
        q rho Vs V K zeta theta k R T‖ ≤
    (u^H)⁻¹ * sourceOriginalAbsoluteCommonMemoryRoot434 SP sm BP bm J ell m cap patterns
      q u Vs V K zeta theta k R := by
  rw [source_original_MEMORY_FULL_to_clean_plus_DIRTY_exact434
    SP sm BP bm J ell m cap patterns hi hcap q rho Vs V K zeta theta k R T hVs hmu]
  exact source_original_ACTUAL_OLD_projector_discrepancy_common434
    SP sm BP bm J ell m cap patterns hi hcap q rho u hrho hu Vs V
    K zeta theta k R T H hVs hmu hm
end Green64Analytic.CorrelationSquare

end

end

