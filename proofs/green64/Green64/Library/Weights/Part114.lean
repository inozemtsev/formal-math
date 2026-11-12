module

public import Green64.Library.Weights.RawCapEnvelope
public import Green64.Library.Correlation.Part074
public import Green64.Library.Weights.Part111
public import Green64.Library.Correlation.Part072
public import Green64.Library.Correlation.PhysicalSharedFreeCarrier
public import Green64.Library.Weights.Part112

@[expose] public section

/-!
# Weights / Part114

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## RawCapGeometry -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- A nonzero literal K=1 physical RAW slice has two genuine complete
physical mark carriers. No comparison kernel or clean event is introduced. -/
theorem parity_raw_physical_completion_support434
    {G : Type} [Fintype G] [DecidableEq G]
    (J : ℕ) (P : G→Finset ℕ) (V : G→ℝ) (q : ℝ) (w wp : ℕ)
    (s : ∀ g : G,parityRawSharedSlots434 J → ℕ)
    (hnz : parityRawPhysicalSlice434 J P V q w wp s≠0) :
    (sourceB574LabelledCompletions434 P (J+1)
      (fun _ : G=>parityRawSharedSlots434 J) s w).Nonempty ∧
    (sourceB574LabelledCompletions434 P (J+1)
      (fun _ : G=>parityRawSharedSlots434 J) s wp).Nonempty := by
  constructor
  · by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hnz
    unfold parityRawPhysicalSlice434
    dsimp only
    rw [he]
    simp only [Finset.sum_empty,mul_zero]
  · by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hnz
    unfold parityRawPhysicalSlice434
    dsimp only
    simp only [he,Finset.sum_empty,Finset.sum_const_zero,mul_zero]

/-- A genuine RAW completion reconstructs the literal none-index native
frame with exactly the SAME shared product. Its full divisor is DR since
DC=1, so the accepted actual frame window applies without an assumed DR
bound, a comparison probe or a clean-array restriction. -/
theorem parity_raw_completion_divisor_window434
    (L : ℝ) (hL : Real.exp 1≤L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ)
    (w : ℕ)
    (ha : (sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1)
      (fun _ : B645ActualGroup434 L hS=>parityRawSharedSlots434 J) s w).Nonempty) :
    (sourceB574SharedDilation434 (J+1)
      (fun _ : B645ActualGroup434 L hS=>parityRawSharedSlots434 J) s : ℝ) ≤
      (b651ParityWindowSize434 J 0 L : ℝ) := by
  let E := fun _ : B645ActualGroup434 L hS=>parityRawSharedSlots434 J
  let d := sourceB574SharedDilation434 (J+1) E s
  obtain ⟨a,ha⟩ := ha
  change a∈parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E
    (fun i=>s i.1 i.2) (d*w) at ha
  rw [parity_physical_completions_restriction_fibre434] at ha
  obtain ⟨ha,hs⟩ := Finset.mem_filter.mp ha
  let e := parityActualFixedPositionMarksEquiv434 L hS J (d*w)
  let x := e.symm ⟨a,ha⟩
  have hx : parityActualPositionMarks434 L hS J (d*w) x=a := by
    change (e (e.symm ⟨a,ha⟩)).val=a
    rw [Equiv.apply_symm_apply]
  have hshared : (fun g i=>parityActualPositionMarks434 L hS J (d*w) x g i.val)=s := by
    funext g i
    rw [hx]
    exact congrFun hs ⟨g,i⟩
  have hD := parity_raw_frame_divisor434 L hS J 0 (Nat.zero_le J) (d*w) x
  rw [hshared] at hD
  have hwindow := b660_actual_parity_frame_D_window434 L hL hS J 0 0 (by norm_num)
    (sourceOriginalMemoryRawComparisonPattern434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
      J 0 (Nat.zero_le J)) x.val (parityRawIdentityFrame434 L hS J 0 (Nat.zero_le J))
  rw [hD] at hwindow
  exact hwindow

/-- Every nonzero true RAW cap-loss slice supplies the physical completion
needed for its actual shared-product window. The zero case will be handled
separately by nonnegativity in the eventual estimate. -/
theorem parity_raw_cap_nonzero_window434
    (L : ℝ) (hL : Real.exp 1≤L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (rho xi3 Z : ℝ) (positions : Finset ℤ) (k : ℤ) (lo hi : ℕ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ)
    (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ)
    (hnz : parityRawCapSlice434 L hS J rho xi3 Z positions k lo hi F G tw psi s≠0) :
    (sourceB574SharedDilation434 (J+1)
      (fun _ : B645ActualGroup434 L hS=>parityRawSharedSlots434 J) s : ℝ) ≤
      (b651ParityWindowSize434 J 0 L : ℝ) := by
  classical
  let d := sourceB574SharedDilation434 (J+1)
    (fun _ : B645ActualGroup434 L hS=>parityRawSharedSlots434 J) s
  let N := paritySharedQuotientPositions434 positions d
  change (∑ w∈N,∑ wp∈N,
    if (2*k)≠0 ∧ (wp:ℤ)=(w:ℤ)+2*k then
      parityRawCapTerm434 L hS J rho xi3 Z lo hi F G tw psi s w wp else 0)≠0 at hnz
  obtain ⟨w,hw,hrow⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  obtain ⟨wp,hwp,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrow
  have ht : parityRawCapTerm434 L hS J rho xi3 Z lo hi F G tw psi s w wp≠0 := by
    intro he
    apply hterm
    split_ifs <;> simp only [he]
  have hPhysical : parityRawPhysicalSlice434 J (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (1/2:ℝ) w wp s≠0 := by
    intro he
    apply ht
    unfold parityRawCapTerm434
    dsimp only
    rw [he,mul_zero]
  have hComp := parity_raw_physical_completion_support434 J (b645ActualBand434 L hS)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (1/2:ℝ) w wp s hPhysical
  exact parity_raw_completion_divisor_window434 L hL hS J s w hComp.1
end Green64Analytic.Parity

end

end

/-! ## RawCapSaving -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Genuine physical cap saving for each literal RAW shared slice.
Precision is fixed before L and the actual operator tuple. A nonzero slice
supplies its own actual none-frame, so no DR support/size or surrogate
physical-envelope premise remains. DC=1 gives X=Z and shift2k. -/
theorem parity_eventually_actual_raw_cap_slice_saving434
    (J : ℕ) (S beta gamma CZ Ck Cpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ), 1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (xi3 Z : ℝ) (k : ℤ),
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
        ∀ (Kpsi : ℝ),0≤Kpsi → ∀ (lo hi : ℕ) (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) →
          (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ),
          (∀ g i,s g i∈b645ActualBand434 L hS g) →
        ∀ positions : Finset ℤ,
          ‖parityRawCapSlice434 L hS J rho xi3 Z positions k lo hi E G tw psi s‖ ≤
            ((128*66:ℝ)*(3:ℝ)^128)*parityRawCapCoefficient434 L hS J s*Kpsi*L^(-A) := by
  filter_upwards [parity_eventually_actual_B633_raw_cap_envelope434 S beta gamma hSfine hbeta hgamma,
    parity_eventually_actual_marked_physical_Pcap_harmonic434 J Cpsi A,
    b651_eventually_parity_window_sqrt434 J 0 (by norm_num),
    b638_eventually_const_power434 88 (1/2) 1 (by norm_num),
    parity_eventually_harmonic_scale_budget434 CZ Ck hCZ]
    with L hFinite hTail hWindow hRate hBudget
  refine ⟨hTail.1,hTail.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk Kpsi hKpsi lo hi tw psi hSupp hPsi s hs positions
  let F := sourceNativePrimeCore r e L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let d := sourceB574SharedDilation434 (J+1)
    (fun _ : B645ActualGroup434 L hS=>parityRawSharedSlots434 J) s
  let C := parityRawCapCoefficient434 L hS J s
  let N := paritySharedQuotientPositions434 positions d
  let Slic := parityRawCapSlice434 L hS J rho xi3 Z positions k lo hi E G tw psi s
  have hC : 0≤C := parity_raw_cap_coefficient_nonneg434 L hS J s
  have hLp : 0<L := by linarith [hFinite.1]
  change ‖Slic‖≤((128*66:ℝ)*(3:ℝ)^128)*C*Kpsi*L^(-A)
  by_cases hz : Slic=0
  · rw [hz,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC) hKpsi) (Real.rpow_nonneg hLp.le _)
  have hdwindow := parity_raw_cap_nonzero_window434 L hWindow.1 hS J rho xi3 Z
    positions k lo hi E G tw psi s hz
  have hSupport := parity_actual_labelled_shared_support434 L hFinite.1 hS (J+1)
    (fun _ : B645ActualGroup434 L hS=>parityRawSharedSlots434 J) s hs
  have hd : 0<d := hSupport.1
  have hdcap : (d:ℝ)≤Real.exp (Real.sqrt L) := hdwindow.trans hWindow.2
  have hsqrt : Real.sqrt L≤(1/88:ℝ)*L := by
    rw [Real.rpow_one] at hRate
    rw [Real.sqrt_eq_rpow]
    linarith
  have hdsmall : (d:ℝ)≤Real.exp ((1/88:ℝ)*L) :=
    hdcap.trans (Real.exp_le_exp.mpr hsqrt)
  have hOne : (1:ℝ)≤Real.exp (Real.sqrt L) := by
    calc
      (1:ℝ)=Real.exp 0 := by simp
      _ ≤ Real.exp (Real.sqrt L) := Real.exp_le_exp.mpr (Real.sqrt_nonneg L)
  have hb := hBudget.2 Z hZlo hZhi 1 (by norm_num)
    (by simpa only [Nat.cast_one] using hOne) k hk
  simp only [Nat.cast_one,mul_one] at hb
  have hErr := hTail.2.2 hS 0 (Nat.zero_le J) (∅,∅) d Z Kpsi (2*k) psi (N.sup id)
    hd hSupport.2 hdsmall hb.1 hKpsi hb.2.1 hb.2.2 hSupp hPsi
  rw [←parity_raw_cap_marked_weight_actual434 L hS J] at hErr
  have hFin := hFinite.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma
    hS J xi3 Z lo hi tw psi s hs positions k
  dsimp only at hFin
  have hdR : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  calc
    _ ≤ C*(d:ℝ)*parityMarkedPhysicalPcapHarmonicEnvelope434 (sourceNativeOriginalG434 20 L) L d
        (parityRawCapMarkedWeight434 L hS) Z (2*k) psi (N.sup id) := hFin
    _ ≤ C*(d:ℝ)*(((128*66:ℝ)*(3:ℝ)^128)*(d:ℝ)⁻¹*Kpsi*L^(-A)) :=
      mul_le_mul_of_nonneg_left hErr (mul_nonneg hC (Nat.cast_nonneg d))
    _ = (((128*66:ℝ)*(3:ℝ)^128)*C*Kpsi*L^(-A))*((d:ℝ)*(d:ℝ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hdR,mul_one]
end Green64Analytic.Parity

end

end

/-! ## RawCapAggregate -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- The complete unrestricted RAW shared law has total one, including
repeated numerical labels and its single inverse DR. Only the full
physical damping remains after integrating the quantitative coefficient. -/
theorem parity_eventually_raw_cap_coefficient_total434 :
    ∀ᶠ L : ℝ in atTop,1<L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ),
        (∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × parityRawSharedSlots434 J =>
          b645ActualBand434 L hS i.1),parityRawCapCoefficient434 L hS J (fun g i=>s ⟨g,i⟩))=
          (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ)) := by
  filter_upwards [parity_eventually_actual_full_mass_floor434] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro hS J
  let E := fun _ : B645ActualGroup434 L hS=>parityRawSharedSlots434 J
  let P := b645ActualBand434 L hS
  let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
  let ss := Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g=>P i.1)
  let D := (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ))
  have hVnz (g : B645ActualGroup434 L hS) : V g≠0 :=
    (source_actual_P_uniform_mass_floor_positive.trans_le (h.2.2 hS g).1).ne'
  have hm := parity_B574_shared_mass_total434 (J+1) E P V
    (parity_actual_full_mass_exact434 L hS) hVnz
  change (∑ s∈ss,D*sourceB574SharedMass434 (J+1) E V (fun g i=>s ⟨g,i⟩))=D
  rw [←Finset.mul_sum,hm,mul_one]

/-- The genuine literal RAW cap loss after all complete shared labels.
The actual shared probability is integrated only after its quantitative
bound; no DR-dependent physical gate or arithmetic is extracted from an
exact identity. RAW has no auxiliary-family or cell-mass cardinality cost. -/
theorem parity_eventually_actual_raw_cap_aggregate434
    (J : ℕ) (S beta gamma CZ Ck Cpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (xi3 Z : ℝ) (k : ℤ),
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
        ∀ (Kpsi : ℝ),0≤Kpsi → ∀ (lo hi : ℕ) (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) → (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ positions : Finset ℤ,
          ‖parityRawHarmonicPhysicalAggregate434 L hS J (-xi3) Z k positions lo hi E G
            (-(rho+xi3)) (-rho) tw 0 psi (fun n np=>1-parityOriginalPhysicalPairPcap434 L n np)‖ ≤
          ((128*66:ℝ)*(3:ℝ)^128)*
          (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ))*Kpsi*L^(-A) := by
  filter_upwards [parity_eventually_actual_raw_cap_slice_saving434 J S beta gamma CZ Ck Cpsi A
      hSfine hbeta hgamma hCZ,parity_eventually_raw_cap_coefficient_total434] with L hSave hMass
  refine ⟨hSave.1,hSave.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk Kpsi hKpsi lo hi tw psi hSupp hPsi positions
  let F := sourceNativePrimeCore r e L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let EF := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let GG := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let ss := Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × parityRawSharedSlots434 J =>
    b645ActualBand434 L hS i.1)
  let C := fun s : ((g : B645ActualGroup434 L hS) × parityRawSharedSlots434 J)→ℕ =>
    parityRawCapCoefficient434 L hS J (fun g i=>s ⟨g,i⟩)
  let f := fun s : ((g : B645ActualGroup434 L hS) × parityRawSharedSlots434 J)→ℕ =>
    parityRawCapSlice434 L hS J rho xi3 Z positions k lo hi EF GG tw psi (fun g i=>s ⟨g,i⟩)
  have hPoint (s) (hs : s∈ss) : ‖f s‖≤((128*66:ℝ)*(3:ℝ)^128)*C s*Kpsi*L^(-A) := by
    exact hSave.2.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma
      hS xi3 Z k hZlo hZhi hk Kpsi hKpsi lo hi tw psi hSupp hPsi
      (fun g i=>s ⟨g,i⟩) (fun g i=>(Fintype.mem_piFinset.mp hs) ⟨g,i⟩) positions
  have hTotal := hMass.2.2 hS J
  rw [parity_raw_cap_slices_exact434 L hS J rho xi3 Z positions k lo hi EF GG tw psi]
  change ‖∑ s∈ss,f s‖≤_
  calc
    _ ≤ ∑ s∈ss,‖f s‖ := norm_sum_le _ _
    _ ≤ ∑ s∈ss,((128*66:ℝ)*(3:ℝ)^128)*C s*Kpsi*L^(-A) := Finset.sum_le_sum hPoint
    _ = ((128*66:ℝ)*(3:ℝ)^128)*(∑ s∈ss,C s)*Kpsi*L^(-A) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
    _ = _ := by rw [hTotal]
end Green64Analytic.Parity

end

end

/-! ## RawCapAggregateSaving -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Complete literal RAW physical cap loss has every logarithmic saving.
The local precision A+16*(J+1)*log2+1 pays both full physical dampings and
absorbs the fixed cutoff constant before L and all operator choices. The
true RAW K1/DC1 law has no comparison-cell or auxiliary-pattern loss. -/
theorem parity_eventually_actual_raw_cap_aggregate_saving434
    (J : ℕ) (S beta gamma CZ Ck Cpsi Kpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) (hK : 0≤Kpsi) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (xi3 Z : ℝ) (k : ℤ),
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
        ∀ (lo hi : ℕ) (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) → (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ positions : Finset ℤ,
          ‖parityRawHarmonicPhysicalAggregate434 L hS J (-xi3) Z k positions lo hi E G
            (-(rho+xi3)) (-rho) tw 0 psi (fun n np=>1-parityOriginalPhysicalPairPcap434 L n np)‖≤L^(-A) := by
  let ed := 16*(J+1:ℝ)*Real.log 2
  let B := A+ed+1
  let C := ((128*66:ℝ)*(3:ℝ)^128)*Kpsi
  filter_upwards [parity_eventually_actual_raw_cap_aggregate434 J S beta gamma CZ Ck Cpsi B
      hSfine hbeta hgamma hCZ,eventually_ge_atTop C] with L hFamily hConst
  refine ⟨hFamily.1,hFamily.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk lo hi tw psi hSupp hPsi positions
  have hLp : 0<L := (Real.exp_pos 2).trans_le hFamily.1
  have hC : 0≤C := mul_nonneg (by positivity) hK
  have hBound := hFamily.2.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1
    xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk Kpsi hK lo hi tw psi hSupp hPsi positions
  have hD := parity_actual_full_damping_log_budget434 L hFamily.1 hS J
  have hPowers : L^ed*L^(-B)=L^(-A-1) := by
    rw [←Real.rpow_add hLp]
    congr 1
    dsimp only [B]
    ring
  calc
    _ ≤ C*(1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ))*L^(-B) :=
      hBound.trans_eq (by dsimp only [C];ring)
    _ ≤ C*L^ed*L^(-B) := by gcongr
    _ = C*(L^ed*L^(-B)) := by ring
    _ = C*L^(-A-1) := by rw [hPowers]
    _ ≤ L*L^(-A-1) := mul_le_mul_of_nonneg_right hConst (Real.rpow_nonneg hLp.le _)
    _ = L^(1+(-A-1)) := by
      simpa only [Real.rpow_one] using (Real.rpow_add hLp (1:ℝ) (-A-1)).symm
    _ = L^(-A) := by congr 1;ring

/-- The original Option.none RAW cap loss, rather than a surrogate empty
comparison kernel, has the same full saving with exactly one external Z.
Original m,Q,h,xi are arbitrary irrelevant RAW constructor parameters;
no positivity or cell-size hypothesis is added for them. -/
theorem parity_eventually_actual_literal_raw_cap_outer_Z_saving434
    (J : ℕ) (S beta gamma CZ Ck Cpsi Kpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) (hK : 0≤Kpsi) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
        ∀ (lo hi : ℕ) (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) → (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ positions : Finset ℤ,
          ‖(Z:ℂ)*parityActualEndpointWeightedRawPositiveFibreSum434 L hS J m hmJ Q h xi (-xi3) Z k
            positions lo hi E G (-(rho+xi3)) (-rho) tw 0 psi
            (fun n np=>1-parityOriginalPhysicalPairPcap434 L n np)‖≤Z*L^(-A) := by
  filter_upwards [parity_eventually_actual_raw_cap_aggregate_saving434 J S beta gamma CZ Ck Cpsi Kpsi A
    hSfine hbeta hgamma hCZ hK] with L hSave
  refine ⟨hSave.1,hSave.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hZlo hZhi hk lo hi tw psi hSupp hPsi positions
  let F := sourceNativePrimeCore r e L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  have hLp : 0<L := (Real.exp_pos 2).trans_le hSave.1
  have hL : 1<L := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<2)).trans_le hSave.1
  have hZ : 0<Z := (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hBound := hSave.2.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1
    xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk lo hi tw psi hSupp hPsi positions
  rw [parity_raw_endpoint_weight_physical_aggregate434 L hL hS J m hmJ Q h xi (-xi3) Z k
    positions lo hi E G (-(rho+xi3)) (-rho) tw 0 psi
    (fun n np=>1-parityOriginalPhysicalPairPcap434 L n np)]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hZ.le]
  exact mul_le_mul_of_nonneg_left hBound hZ.le
end Green64Analytic.Parity

end

end

/-! ## RawCapLinear -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- The literal full shared/free RAW physical aggregate is linear in the
independently supplied endpoint-pair weight, without replacing either
physical support or the arithmetic core. In particular the physical
Ppart cap can be inserted by subtracting its exact complement. -/
theorem parity_raw_physical_aggregate_sub_weight434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (zeta Z : ℝ) (k : ℤ) (positions : Finset ℤ)
    (lo hi : ℕ) (F G : PrimeSlotCore) (t1 t2 : ℝ)
    (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (W₁ W₂ : ℕ → ℕ → ℂ) :
    parityRawHarmonicPhysicalAggregate434 L hS J zeta Z k positions lo hi
      F G t1 t2 tw v psi (fun n np => W₁ n np - W₂ n np) =
    parityRawHarmonicPhysicalAggregate434 L hS J zeta Z k positions lo hi
      F G t1 t2 tw v psi W₁ -
    parityRawHarmonicPhysicalAggregate434 L hS J zeta Z k positions lo hi
      F G t1 t2 tw v psi W₂ := by
  unfold parityRawHarmonicPhysicalAggregate434
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  dsimp only
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro wp hwp
  split_ifs with h
  · ring
  · simp

/-- Exact original physical Ppart cap insertion in the literal RAW aggregate.
The complement retains both original gates at D_R*w and D_R*w'. -/
theorem parity_raw_physical_pcap_difference434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (zeta Z : ℝ) (k : ℤ) (positions : Finset ℤ)
    (lo hi : ℕ) (F G : PrimeSlotCore) (t1 t2 : ℝ)
    (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityRawHarmonicPhysicalAggregate434 L hS J zeta Z k positions lo hi F G t1 t2
      tw v psi (parityOriginalPhysicalPairPcap434 L) =
    parityRawHarmonicPhysicalAggregate434 L hS J zeta Z k positions lo hi F G t1 t2
      tw v psi (fun _ _ => 1) -
    parityRawHarmonicPhysicalAggregate434 L hS J zeta Z k positions lo hi F G t1 t2
      tw v psi (fun n np => 1 - parityOriginalPhysicalPairPcap434 L n np) := by
  rw [← parity_raw_physical_aggregate_sub_weight434]
  congr 1
  funext n np
  ring
end Green64Analytic.Parity

end

end

/-! ## RawSharedSeed -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

/-- The actual none-index RAW frame reconstructed from one complete
physical marking has its original signed displacement bounded framewise.
No comparison probe or summed-matrix cancellation supplies this bound. -/
theorem parity_raw_completion_frame_radius434
    (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ)
    (w : ℕ)
    (ha : (sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1)
      (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s w).Nonempty)
    (Ck : ℝ) (k : ℤ) (hk : (k.natAbs : ℝ) ≤ L^Ck) :
    |(2*k)*(sourceB574SharedDilation434 (J+1)
      (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s : ℤ)| ≤
      (b651ParityPathRadius434 J Ck L : ℤ) := by
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let d := sourceB574SharedDilation434 (J+1) E s
  obtain ⟨a,ha⟩ := ha
  change a ∈ parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E
    (fun i => s i.1 i.2) (d*w) at ha
  rw [parity_physical_completions_restriction_fibre434] at ha
  obtain ⟨ha,hs⟩ := Finset.mem_filter.mp ha
  let e := parityActualFixedPositionMarksEquiv434 L hS J (d*w)
  let x := e.symm ⟨a,ha⟩
  have hx : parityActualPositionMarks434 L hS J (d*w) x=a := by
    change (e (e.symm ⟨a,ha⟩)).val=a
    rw [Equiv.apply_symm_apply]
  have hshared : (fun g i => parityActualPositionMarks434 L hS J (d*w) x g i.val)=s := by
    funext g i
    rw [hx]
    exact congrFun hs ⟨g,i⟩
  have hD := parity_raw_frame_divisor434 L hS J 0 (Nat.zero_le J) (d*w) x
  rw [hshared] at hD
  have hR := parity_actual_frame_radius434 J 0 Ck L hL hS
    (sourceOriginalMemoryRawComparisonPattern434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
      J 0 (Nat.zero_le J)) x.val (parityRawIdentityFrame434 L hS J 0 (Nat.zero_le J)) k hk
  rw [hD] at hR
  exact hR

/-- The original finite physical source seed holds on every genuine RAW
completion and nonzero cutoff. The full shared divisor is controlled by
its proved none-frame window; no arbitrary shared law is substituted. -/
theorem parity_eventually_raw_completion_seed434 (J : ℕ) (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop,Real.exp 1 ≤ L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ),
      (∀ g i,s g i ∈ b645ActualBand434 L hS g) →
    ∀ Z : ℝ,0 < Z → Z ≤ Real.exp L*L^CZ →
    ∀ psi : ℝ → ℂ,(∀ u,psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64) →
    ∀ w : ℕ,0 < w →
      (sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1)
        (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s w).Nonempty →
      psi ((w : ℝ)/Z) ≠ 0 →
      ((sourceB574SharedDilation434 (J+1)
        (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s*w : ℕ) : ℤ) ∈
        b654ParitySeedPositions434 1 (parityDyadicLimit434 L) := by
  filter_upwards [parity_eventually_dyadic_outer_envelope434 J 0 CZ (by norm_num)] with L hEnv
  refine ⟨hEnv.1,?_⟩
  intro hS s hs Z hZ hZhi psi hSupp w hw hcomp hpsi
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let d := sourceB574SharedDilation434 (J+1) E s
  have hL1 : 1 < L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ)<1)).trans_le hEnv.1
  have hd := (parity_actual_labelled_shared_support434 L hL1 hS (J+1) E s hs).1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hwBound : (w : ℝ) ≤ 64*Z := (div_le_iff₀ hZ).mp (hSupp _ hpsi).2
  have hnhi : ((d*w : ℕ) : ℝ) ≤ 64*(Z*(d : ℝ)) := by
    calc
      _ = (d : ℝ)*(w : ℝ) := Nat.cast_mul _ _
      _ ≤ (d : ℝ)*(64*Z) := mul_le_mul_of_nonneg_left hwBound hdR.le
      _ = _ := by ring
  have hwindow : (d : ℝ) ≤ (b651ParityWindowSize434 J 0 L : ℝ) :=
    parity_raw_completion_divisor_window434 L hEnv.1 hS J s w hcomp
  have hLp : 0 < L := by linarith
  have hnend : ((d*w : ℕ) : ℝ) < (parityDyadicLimit434 L : ℝ) := by
    calc
      _ ≤ 64*(Z*(d : ℝ)) := hnhi
      _ ≤ 64*((Real.exp L*L^CZ)*(b651ParityWindowSize434 J 0 L : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hZhi hwindow hdR.le
            (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hLp.le _))) (by norm_num)
      _ = 64*Real.exp L*L^CZ*(b651ParityWindowSize434 J 0 L : ℝ) := by ring
      _ < Real.exp (2*L) := hEnv.2
      _ < (parityDyadicLimit434 L : ℝ) := parity_dyadic_limit_exp434 L hLp
  apply Finset.mem_image.mpr
  refine ⟨d*w,Finset.mem_Ico.mpr ⟨Nat.mul_pos hd hw,?_⟩,rfl⟩
  exact_mod_cast hnend

/-- Exact removal of the source seed from the arithmetic multiplying a
literal RAW physical slice. The original ordinary-part/core and balanced
phase/parity identities are used, while every shared mark remains inside
the physical slice. No clean-array or error hypothesis is assumed. -/
theorem parity_eventually_raw_shared_scalar_slice434 (J : ℕ) (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop,Real.exp 1 ≤ L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ),
      (∀ g i,s g i ∈ b645ActualBand434 L hS g) →
    ∀ (rho xi3 Z : ℝ),0 < Z → Z ≤ Real.exp L*L^CZ →
    ∀ psi : ℝ → ℂ,(∀ u,psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64) →
    ∀ (F G : PrimeSlotCore) (tw : Bool) (w wp : ℕ),0 < w → 0 < wp →
      let d := sourceB574SharedDilation434 (J+1)
        (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
      let B := parityRawPhysicalSlice434 J (b645ActualBand434 L hS)
        (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
        (1/2) w wp s
      parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
          (-(rho+xi3)) (-rho) tw 0 psi d 1 w wp*B =
        parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
          (-(rho+xi3)) (-rho) tw psi 1 w wp*B := by
  filter_upwards [parity_eventually_raw_completion_seed434 J CZ] with L hSeed
  refine ⟨hSeed.1,?_⟩
  intro hS s hs rho xi3 Z hZ hZhi psi hSupp F G tw w wp hw hwp
  dsimp only
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let d := sourceB574SharedDilation434 (J+1) E s
  let B := parityRawPhysicalSlice434 J (b645ActualBand434 L hS)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (1/2) w wp s
  change parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
      (-(rho+xi3)) (-rho) tw 0 psi d 1 w wp*B =
    parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi 1 w wp*B
  by_cases hB : B=0
  · rw [hB,mul_zero,mul_zero]
  by_cases hpsi : psi ((w : ℝ)/Z)=0
  · have hleft : parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
        (-(rho+xi3)) (-rho) tw 0 psi d 1 w wp=0 := by
      unfold parityHarmonicSharedArithmetic434
      split_ifs <;> simp only [Nat.cast_one,mul_one,hpsi,mul_zero,zero_mul]
    have hright : parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
        (-(rho+xi3)) (-rho) tw psi 1 w wp=0 := by
      unfold parityHarmonicStrippedArithmetic434
      simp only [Nat.cast_one,mul_one,hpsi,mul_zero,zero_mul]
    rw [hleft,hright]
  have hcomp := (parity_raw_physical_completion_support434 J (b645ActualBand434 L hS)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (1/2) w wp s hB).1
  have hseed := hSeed.2 hS s hs Z hZ hZhi psi hSupp w hw hcomp hpsi
  have hL1 : 1 < L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ)<1)).trans_le hSeed.1
  have hstrip := parity_actual_labelled_shared_arithmetic434 L hL1 hS (J+1) E s hs
    rho xi3 Z 1 (parityDyadicLimit434 L) F G tw psi 1 w wp (by norm_num) hw hwp
  dsimp only at hstrip
  rw [hstrip,if_pos hseed]

/-- Both positive quotient endpoints lie in the original shared quotient
carrier on the exact RAW shift and nonzero original cutoff. This is proved
framewise at DR before finite reindexing of the full shared sum. -/
theorem parity_eventually_raw_completion_pair_carrier434 (J : ℕ) (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop,Real.exp 1 ≤ L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ),
      (∀ g i,s g i ∈ b645ActualBand434 L hS g) →
    ∀ (Ck Z : ℝ) (k : ℤ),(k.natAbs : ℝ) ≤ L^Ck → 0 < Z → Z ≤ Real.exp L*L^CZ →
    ∀ psi : ℝ → ℂ,(∀ u,psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64) →
    ∀ w wp : ℕ,0 < w → 0 < wp →
      (sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1)
        (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s w).Nonempty →
      psi ((w : ℝ)/Z) ≠ 0 → (wp : ℤ)=(w : ℤ)+2*k →
      let d := sourceB574SharedDilation434 (J+1)
        (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
      let W := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
      w ∈ paritySharedQuotientPositions434 W d ∧ wp ∈ paritySharedQuotientPositions434 W d := by
  filter_upwards [parity_eventually_raw_completion_seed434 J CZ] with L hSeed
  refine ⟨hSeed.1,?_⟩
  intro hS s hs Ck Z k hk hZ hZhi psi hSupp w wp hw hwp hcomp hpsi hstep
  dsimp only
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let d := sourceB574SharedDilation434 (J+1) E s
  have hL1 : 1 < L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ)<1)).trans_le hSeed.1
  have hd := (parity_actual_labelled_shared_support434 L hL1 hS (J+1) E s hs).1
  have hseed := hSeed.2 hS s hs Z hZ hZhi psi hSupp w hw hcomp hpsi
  have hRadius := parity_raw_completion_frame_radius434 L hSeed.1 hS J s w hcomp Ck k hk
  change ((d*w : ℕ) : ℤ) ∈ b654ParitySeedPositions434 1 (parityDyadicLimit434 L) at hseed
  change |(2*k)*(d : ℤ)| ≤ (b651ParityPathRadius434 J Ck L : ℤ) at hRadius
  have hstep' : (wp : ℤ)=(w : ℤ)+(2*k)*(1 : ℕ) := by simpa using hstep
  have hphysical := (parity_harmonic_shared_step_iff434 d 1 w wp hd k).mpr hstep'
  simp only [Nat.mul_one] at hphysical
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hseed
  have haI := Finset.mem_Ico.mp ha
  have hnlo : (1 : ℤ) ≤ ((d*w : ℕ) : ℤ) := by omega
  have hnhi : ((d*w : ℕ) : ℤ) < (parityDyadicLimit434 L : ℤ) := by omega
  have hr0 : (0 : ℤ) ≤ (b651ParityPathRadius434 J Ck L : ℤ) := by positivity
  obtain ⟨hrlo,hrhi⟩ := abs_le.mp hRadius
  constructor
  · apply (parity_shared_quotient_mem_iff434 _ d w hd).mpr
    refine ⟨hw,Finset.mem_Icc.mpr ⟨?_,?_⟩⟩ <;> omega
  · apply (parity_shared_quotient_mem_iff434 _ d wp hd).mpr
    refine ⟨hwp,Finset.mem_Icc.mpr ⟨?_,?_⟩⟩ <;> omega
end Green64Analytic.Parity

end

end

/-! ## RawSourceMarked -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 26000

/-- The COMPLETE one-slot marked sum, with its true harmonic mass, is
exactly the original source one-mark weight. Vanishing distinct counts
are retained; no positivity, prime, cleanliness or approximation premise
is needed for this finite identity. -/
theorem parity_raw_one_mark_source_weight434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (q : ℝ) (n : ℕ) :
    actualBigMarkDecoration P (fun _=>1) q (fun g=>groupHarmonic (P g))
      (fun _=>1) n = (Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight q 1 P n : ℂ) := by
  unfold actualBigMarkDecoration
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,bigMarkLists_card,
    Nat.descFactorial_one,Nat.cast_prod]
  unfold bigMarkPrefactor Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight
  simp only [Nat.cast_one,pow_one,Nat.descFactorial_one,Complex.ofReal_prod]
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  change (((q^((smallPrimeCount (P g) n : ℤ)-1)/groupHarmonic (P g) : ℝ) : ℂ)*
    (smallPrimeCount (P g) n : ℂ)) =
    ((q^(smallPrimeCount (P g) n-1)*(smallPrimeCount (P g) n : ℝ)/groupHarmonic (P g) : ℝ) : ℂ)
  by_cases hn : smallPrimeCount (P g) n=0
  · simp [hn]
  · have hN : 1 ≤ smallPrimeCount (P g) n := Nat.one_le_iff_ne_zero.mpr hn
    have he : (smallPrimeCount (P g) n : ℤ)-1=
        ((smallPrimeCount (P g) n-1 : ℕ) : ℤ) := by
      simpa using (Nat.cast_sub hN : ((smallPrimeCount (P g) n-1 : ℕ) : ℤ)=
        (smallPrimeCount (P g) n : ℤ)-(1 : ℤ)).symm
    rw [he,zpow_natCast]
    push_cast
    ring

/-- Independent literal stripped RAW slice: K=1 on BOTH complete
one-slot free-list carriers, with both original full-group prefactors.
It contains no comparison probe, auxiliary normalization or desired
source-channel definition. -/
def parityRawStrippedSlice434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ) (q : ℝ) (w wp : ℕ) : ℂ :=
  bigMarkPrefactor P (fun _=>1) q V w *
    bigMarkPrefactor P (fun _=>1) q V wp *
    (∑ a∈bigMarkLists P (fun _=>1) w,∑ b∈bigMarkLists P (fun _=>1) wp,(1 : ℂ))

/-- Exact two-list extraction with both full prefactors and conjugation
on the first endpoint. This is not an estimate or a replacement kernel. -/
theorem parity_raw_stripped_slice_marked434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ) (q : ℝ) (w wp : ℕ) :
    parityRawStrippedSlice434 P V q w wp =
      star (actualBigMarkDecoration P (fun _=>1) q V (fun _=>1) w)*
        actualBigMarkDecoration P (fun _=>1) q V (fun _=>1) wp := by
  simpa only [parityRawStrippedSlice434,star_one,mul_one] using
    source_two_marked_tests434 P (fun _=>1) q V (fun _=>1) (fun _=>1) w wp

/-- The independently defined literal K=1 stripped slice equals the
original source endpoint one-mark product, with exact harmonic masses. -/
theorem parity_raw_stripped_slice_source_weight434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (q : ℝ) (w wp : ℕ) :
    parityRawStrippedSlice434 P (fun g=>groupHarmonic (P g)) q w wp =
      (Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight q 1 P w*Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight q 1 P wp : ℝ) := by
  rw [parity_raw_stripped_slice_marked434,parity_raw_one_mark_source_weight434,
    parity_raw_one_mark_source_weight434]
  simp

/-- Reindexing the entire physical SMALL+BIG family preserves the
original source one-mark product, including the distinguished SMALL
group and all original reciprocal masses. -/
theorem parity_actual_raw_marked_source_weight434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (q : ℝ) (n : ℕ) :
    Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight q 1 (b645ActualBand434 L hS) n =
      Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight q 1 (sourceOriginalPAllActualBands 20 L) n := by
  unfold Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight
  let e := sourceNativeOriginalFullEquiv434 20 L hS hL
  calc
    _ = ∏ g : B645ActualGroup434 L hS,
        q^(shiftTwoGroupOmega (sourceOriginalPAllActualBands 20 L (e g)) n-1)*
          ((shiftTwoGroupOmega (sourceOriginalPAllActualBands 20 L (e g)) n).descFactorial 1 : ℝ)/
            (groupHarmonic (sourceOriginalPAllActualBands 20 L (e g)))^1 := by
      apply Finset.prod_congr rfl
      intro g hg
      rw [parity_actual_full_band_source434 L hL hS g]
    _ = _ := e.prod_comp (fun g =>
      q^(shiftTwoGroupOmega (sourceOriginalPAllActualBands 20 L g) n-1)*
        ((shiftTwoGroupOmega (sourceOriginalPAllActualBands 20 L g) n).descFactorial 1 : ℝ)/
          (groupHarmonic (sourceOriginalPAllActualBands 20 L g))^1)

/-- Actual r20 stripped RAW-to-source marked identity. Both free endpoint
products are complete, every original group is retained, and the true V
fields are used without an external mass-normalization assumption. -/
theorem parity_actual_raw_stripped_source_weight434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (w wp : ℕ) :
    parityRawStrippedSlice434 (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (1/2 : ℝ) w wp =
      (Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight (1/2 : ℝ) 1 (sourceOriginalPAllActualBands 20 L) w*
        Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight (1/2 : ℝ) 1 (sourceOriginalPAllActualBands 20 L) wp : ℝ) := by
  have hV : Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L) =
      (fun g=>groupHarmonic (b645ActualBand434 L hS g)) := by
    funext g
    rw [parity_actual_full_mass_exact434]
    simp only [groupHarmonic,one_div]
  rw [hV,parity_raw_stripped_slice_source_weight434,
    parity_actual_raw_marked_source_weight434 L hL hS,
    parity_actual_raw_marked_source_weight434 L hL hS]
end Green64Analytic.Parity

end

end

