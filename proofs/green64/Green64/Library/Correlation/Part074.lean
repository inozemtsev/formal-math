module

public import Green64.Library.Correlation.PhysicalSharedFreeCapEnvelope
public import Green64.Library.Correlation.Part072
public import Green64.Library.Correlation.Part073

@[expose] public section

/-!
# Correlation / Part074

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalSharedFreeCapSaving -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- A nonzero literal cap-loss slice supplies an ACTUAL physical completion.
The native frame window bound then controls the true DR*DC. Neither a
shared-size nor an auxiliary-size premise is postulated. -/
theorem parity_actual_cap_loss_nonzero_window434
    (L : ℝ) (hL : Real.exp 1≤L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Z : ℝ) (positions : Finset ℤ) (k : ℤ) (lo hi : ℕ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : ∀ g : B645ActualGroup434 L hS,
      sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (hnz : parityActualPhysicalComparisonCapLossSlice434 L hS J m hmJ nu Q h xi rho xi3 Z
      positions k lo hi F G tw psi aux s≠0) :
    ((sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s *
      parityActualProbeAuxD434 L J m hmJ nu aux : ℕ) : ℝ)≤(b651ParityWindowSize434 J 0 L:ℝ) := by
  classical
  let d := sourceB574SharedDilation434 (J+1)
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let N := paritySharedQuotientPositions434 positions d
  change (∑ w∈N,∑ wp∈N,
    if (2*k)≠0 ∧ (wp:ℤ)=(w:ℤ)+(2*k)*(c:ℤ) then
      parityActualPhysicalComparisonCapLossTerm434 L hS J m hmJ nu Q h xi rho xi3 Z lo hi F G tw psi aux s w wp
    else 0)≠0 at hnz
  obtain ⟨w,hw,hrow⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  obtain ⟨wp,hwp,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrow
  have ht : parityActualPhysicalComparisonCapLossTerm434 L hS J m hmJ nu Q h xi rho xi3 Z
      lo hi F G tw psi aux s w wp≠0 := by
    intro he
    apply hterm
    split_ifs <;> simp only [he]
  have hPhysical : parityActualB574Physical434 L hS J m hmJ nu Q h xi aux s w wp≠0 := by
    intro he
    apply ht
    unfold parityActualPhysicalComparisonCapLossTerm434
    dsimp only
    rw [he,mul_zero]
  have hComp := parity_B574_physical_slice_completion_support434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
    Q h h xi (b645ActualBand434 L hS)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
      (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
    (1/2) w wp s hPhysical
  exact parity_actual_completion_full_divisor_window434 L hL hS J m hmJ nu aux s w hComp.1

/-- Every requested logarithmic precision is fixed BEFORE L and all actual
endpoint/operator data. A nonzero slice supplies its own genuine physical
completion, so DR<=exp(L/88), DC<=exp(sqrt L) and all harmonic geometry are
derived. The original full marked physical Pcap saving then applies.
Both inverse cell masses, native auxiliary atom and SharedMass remain in
C; no shared or auxiliary sum has been suppressed. -/
theorem parity_eventually_actual_comparison_cap_slice_saving434
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
          (m : ℕ) (hmJ : m≤J)
          (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
          (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ), 0<h → 0<xi →
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
        ∀ (Kpsi : ℝ),0≤Kpsi → ∀ (lo hi : ℕ) (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) →
          (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ (aux : ParityActualProbeAux434 L J m hmJ nu)
          (s : ∀ g : B645ActualGroup434 L hS,
            sourceOriginalProbeSharedSlots434 J 1 m hmJ
              (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ),
          (∀ g i,s g i∈b645ActualBand434 L hS g) →
        ∀ positions : Finset ℤ,
          ‖parityActualPhysicalComparisonCapLossSlice434 L hS J m hmJ nu Q h xi rho xi3 Z
            positions k lo hi E G tw psi aux s‖ ≤
            ((128*66:ℝ)*(3:ℝ)^128)*
              parityActualComparisonCapEnvelopeCoefficient434 L hS J m hmJ nu Q xi aux s*Kpsi*L^(-A) := by
  filter_upwards [parity_eventually_actual_B633_cap_loss_envelope434 S beta gamma hSfine hbeta hgamma,
    parity_eventually_actual_marked_physical_Pcap_harmonic434 J Cpsi A,
    b651_eventually_parity_window_sqrt434 J 0 (by norm_num),
    b638_eventually_const_power434 88 (1/2) 1 (by norm_num),
    parity_eventually_harmonic_scale_budget434 CZ Ck hCZ]
    with L hFinite hTail hWindow hRate hBudget
  refine ⟨hTail.1,hTail.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ nu Q h xi xi3 Z k hh hxi hZlo hZhi hk Kpsi hKpsi
    lo hi tw psi hSupp hPsi aux s hs positions
  let F := sourceNativePrimeCore r e L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let d := sourceB574SharedDilation434 (J+1)
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let C := parityActualComparisonCapEnvelopeCoefficient434 L hS J m hmJ nu Q xi aux s
  let N := paritySharedQuotientPositions434 positions d
  let Slic := parityActualPhysicalComparisonCapLossSlice434 L hS J m hmJ nu Q h xi rho xi3 Z
    positions k lo hi E G tw psi aux s
  have hC : 0≤C := parity_actual_comparison_cap_coefficient_nonneg434 L hS J m hmJ nu Q xi aux s
  have hLp : 0<L := by linarith [hFinite.1]
  change ‖Slic‖≤((128*66:ℝ)*(3:ℝ)^128)*C*Kpsi*L^(-A)
  by_cases hz : Slic=0
  · rw [hz,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC) hKpsi) (Real.rpow_nonneg hLp.le _)
  have hdc := parity_actual_cap_loss_nonzero_window434 L hWindow.1 hS J m hmJ nu Q h xi rho xi3 Z
    positions k lo hi E G tw psi aux s hz
  have hSupport := parity_actual_labelled_shared_support434 L hFinite.1 hS (J+1)
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s hs
  have hd : 0<d := hSupport.1
  have hc : 0<c := parity_actual_probe_aux_positive434 L hS J m hmJ nu aux
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hc1 : (1:ℝ)≤ c := by exact_mod_cast hc
  have hdcR : (d:ℝ)*(c:ℝ)≤(b651ParityWindowSize434 J 0 L:ℝ) := by exact_mod_cast hdc
  have hdprod : (d:ℝ)≤(d:ℝ)*(c:ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc1 (Nat.cast_nonneg d)
  have hcprod : (c:ℝ)≤(d:ℝ)*(c:ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hd1 (Nat.cast_nonneg c)
  have hdcap : (d:ℝ)≤Real.exp (Real.sqrt L) := hdprod.trans (hdcR.trans hWindow.2)
  have hccap : (c:ℝ)≤Real.exp (Real.sqrt L) := hcprod.trans (hdcR.trans hWindow.2)
  have hsqrt : Real.sqrt L≤(1/88:ℝ)*L := by
    rw [Real.rpow_one] at hRate
    rw [Real.sqrt_eq_rpow]
    linarith
  have hdsmall : (d:ℝ)≤Real.exp ((1/88:ℝ)*L) :=
    hdcap.trans (Real.exp_le_exp.mpr hsqrt)
  have hb := hBudget.2 Z hZlo hZhi c hc hccap k hk
  have hErr := hTail.2.2 hS m hmJ nu d (Z*(c:ℝ)) Kpsi ((2*k)*(c:ℤ)) psi (N.sup id)
    hd hSupport.2 hdsmall hb.1 hKpsi hb.2.1 hb.2.2 hSupp hPsi
  have hFin := hFinite.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma
    hS J m hmJ nu Q h xi xi3 Z hh hxi lo hi tw psi aux s hs positions k
  dsimp only at hFin
  have hdR : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  calc
    _ ≤ C*(d:ℝ)*parityMarkedPhysicalPcapHarmonicEnvelope434 (sourceNativeOriginalG434 20 L) L d
        (parityActualFullMarkedWeight434 L hS J m hmJ nu)
        (Z*(c:ℝ)) ((2*k)*(c:ℤ)) psi (N.sup id) := hFin
    _ ≤ C*(d:ℝ)*(((128*66:ℝ)*(3:ℝ)^128)*(d:ℝ)⁻¹*Kpsi*L^(-A)) :=
      mul_le_mul_of_nonneg_left hErr (mul_nonneg hC (Nat.cast_nonneg d))
    _ = (((128*66:ℝ)*(3:ℝ)^128)*C*Kpsi*L^(-A))*((d:ℝ)*(d:ℝ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hdR,mul_one]
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeCapSharedSaving -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- The complete labelled shared law has total one. The carrier includes
ALL repeated prime draws; no clean or injective conditioning occurs. -/
theorem parity_B574_shared_mass_total434
    {G : Type} [Fintype G] [DecidableEq G]
    (M : ℕ) (E : G→Finset (Fin M)) (P : G→Finset ℕ) (V : G→ℝ)
    (hV : ∀ g,V g=∑ p∈P g,1/(p:ℝ)) (hVnz : ∀ g,V g≠0) :
    (∑ s∈Fintype.piFinset (fun i : (g : G) × E g=>P i.1),
      sourceB574SharedMass434 M E V (fun g i=>s ⟨g,i⟩))=1 := by
  classical
  have hMass (i : (g : G) × E g) :
      (∑ p∈P i.1,sourcePrimeSharedAtom434 (V i.1) p)=1 :=
    source_prime_shared_atom_total434 (P i.1) (V i.1) (hV i.1) (hVnz i.1)
  simpa only [sourceSharedLaw434,sourceB574SharedMass434,Fintype.prod_sigma] using
    (source_shared_law_total434 (fun i : (g : G) × E g=>P i.1)
      (fun i=>sourcePrimeSharedAtom434 (V i.1)) hMass)

/-- Actual shared normalization sums the exact cap-envelope coefficient.
The remaining factors are squared damping loss, the typed auxiliary
probability atom and BOTH original inverse cell masses. -/
theorem parity_eventually_actual_cap_coefficient_total434 :
    ∀ᶠ L : ℝ in atTop,1<L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (J m : ℕ) (hmJ : m≤J)
        (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
        (Q : ℕ) (xi : ℝ) (aux : ParityActualProbeAux434 L J m hmJ nu),
        let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
        (∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g=>b645ActualBand434 L hS i.1),
          parityActualComparisonCapEnvelopeCoefficient434 L hS J m hmJ nu Q xi aux (fun g i=>s ⟨g,i⟩))=
          (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ)) *
          ‖(sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
            (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ)‖ *
          ((Q:ℝ)^4*(xi⁻¹)^2) := by
  filter_upwards [parity_eventually_actual_full_mass_floor434] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro hS J m hmJ nu Q xi aux
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
  let P := b645ActualBand434 L hS
  let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
  let ss := Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g=>P i.1)
  let D := (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ))
  let A := ‖(sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
    (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ)‖
  let B := (Q:ℝ)^4*(xi⁻¹)^2
  have hVnz (g : B645ActualGroup434 L hS) : V g≠0 :=
    (source_actual_P_uniform_mass_floor_positive.trans_le (h.2.2 hS g).1).ne'
  have hm := parity_B574_shared_mass_total434 (J+1) E P V
    (parity_actual_full_mass_exact434 L hS) hVnz
  change (∑ s∈ss,D*sourceB574SharedMass434 (J+1) E V (fun g i=>s ⟨g,i⟩)*A*B)=D*A*B
  calc
    _ = (D*(∑ s∈ss,sourceB574SharedMass434 (J+1) E V (fun g i=>s ⟨g,i⟩)))*A*B := by
      simp only [Finset.sum_mul,Finset.mul_sum]
    _ = _ := by rw [hm,mul_one]

/-- Genuine comparison cap loss after summing EVERY shared label. Actual
B633 endpoints and the physical Pcap tail give the bound; no envelope
premise and no surrogate clean law is used. The full auxiliary atom is
still explicit, to be integrated by its original probability law. -/
theorem parity_eventually_actual_comparison_cap_shared_saving434
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
          (m : ℕ) (hmJ : m≤J)
          (nu : ↥(sourceOriginalTwoBlockProbePatterns434
            (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
          (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),0<h → 0<xi →
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
        ∀ (Kpsi : ℝ),0≤Kpsi → ∀ (lo hi : ℕ) (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) → (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ (aux : ParityActualProbeAux434 L J m hmJ nu.val) (positions : Finset ℤ),
          ‖parityActualEndpointWeightedComparisonB574434 L hS J m hmJ nu Q h xi (-xi3) Z k
            positions lo hi E G (-(rho+xi3)) (-rho) tw 0 psi aux
            (fun n np=>1-parityOriginalPhysicalPairPcap434 L n np)‖ ≤
          ((128*66:ℝ)*(3:ℝ)^128)*
          (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ)) *
          ‖(sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
            (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu.val) aux : ℂ)‖ *
          ((Q:ℝ)^4*(xi⁻¹)^2)*Kpsi*L^(-A) := by
  filter_upwards [parity_eventually_actual_comparison_cap_slice_saving434 J S beta gamma CZ Ck Cpsi A
      hSfine hbeta hgamma hCZ,parity_eventually_actual_cap_coefficient_total434] with L hSave hMass
  refine ⟨hSave.1,hSave.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ nu Q h xi xi3 Z k hh hxi hZlo hZhi hk Kpsi hKpsi
    lo hi tw psi hSupp hPsi aux positions
  let F := sourceNativePrimeCore r e L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let EF := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let GG := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
  let ss := Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g=>b645ActualBand434 L hS i.1)
  let C := fun s : ((g : B645ActualGroup434 L hS) × E g)→ℕ =>
    parityActualComparisonCapEnvelopeCoefficient434 L hS J m hmJ nu.val Q xi aux (fun g i=>s ⟨g,i⟩)
  let f := fun s : ((g : B645ActualGroup434 L hS) × E g)→ℕ =>
    parityActualPhysicalComparisonCapLossSlice434 L hS J m hmJ nu.val Q h xi rho xi3 Z positions k lo hi EF GG tw psi aux (fun g i=>s ⟨g,i⟩)
  have hPoint (s) (hs : s∈ss) : ‖f s‖≤((128*66:ℝ)*(3:ℝ)^128)*C s*Kpsi*L^(-A) := by
    exact hSave.2.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma
      hS m hmJ nu.val Q h xi xi3 Z k hh hxi hZlo hZhi hk Kpsi hKpsi lo hi tw psi hSupp hPsi aux
      (fun g i=>s ⟨g,i⟩) (fun g i=>(Fintype.mem_piFinset.mp hs) ⟨g,i⟩) positions
  have hTotal := hMass.2.2 hS J m hmJ nu.val Q xi aux
  rw [parity_actual_comparison_cap_loss_slices_exact434 L hS J m hmJ nu Q h xi rho xi3 Z positions k lo hi EF GG tw psi aux]
  change ‖∑ s∈ss,f s‖≤_
  calc
    _ ≤ ∑ s∈ss,‖f s‖ := norm_sum_le _ _
    _ ≤ ∑ s∈ss,((128*66:ℝ)*(3:ℝ)^128)*C s*Kpsi*L^(-A) := Finset.sum_le_sum hPoint
    _ = ((128*66:ℝ)*(3:ℝ)^128)*(∑ s∈ss,C s)*Kpsi*L^(-A) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
    _ = _ := by rw [hTotal]; ring
end Green64Analytic.Parity

end

end

/-! ## RawCapMarked -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 22000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- The genuine RAW endpoint marked weight has exactly one free slot in
EVERY full SMALL and BIG group. This definition contains no comparison
kernel or comparison probe. -/
def parityRawCapMarkedWeight434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (n : ℕ) : ℝ :=
  ‖actualBigMarkDecoration (b645ActualBand434 L hS) (fun _ => 1) (1/2:ℝ)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (fun _ => 1) n‖

/-- Only the marked WEIGHT is specialized to the all-empty first-J index
at m=0. Its endpoint-free count is one, not zero. No RAW/comparison kernel
identity is asserted. -/
theorem parity_raw_cap_marked_weight_actual434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ) :
    parityRawCapMarkedWeight434 L hS =
      parityActualFullMarkedWeight434 L hS J 0 (Nat.zero_le J) (∅,∅) := by
  have ht : sourceOriginalProbeFreeMarkCount434 J 1 0 (Nat.zero_le J)
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) 0
        ((∅,∅) : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) 0)) =
      (fun _ => 1) := by
    funext g
    simp [sourceOriginalProbeFreeMarkCount434,sourceOriginalProbeFreedSlots434]
  funext n
  unfold parityRawCapMarkedWeight434 parityActualFullMarkedWeight434
  rw [ht]

/-- Literal RAW coefficient: full two-endpoint damping and the complete
shared harmonic mass, including its single inverse DR. RAW has K=1 and
DC=1, so no comparison-cell or auxiliary-family factor occurs. -/
def parityRawCapCoefficient434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ) : ℝ :=
  (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ)) *
    sourceB574SharedMass434 (J+1) (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)) s

theorem parity_raw_cap_coefficient_nonneg434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ) :
    0≤parityRawCapCoefficient434 L hS J s := by
  have hV (g : B645ActualGroup434 L hS) :
      0≤Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L) g := by
    rw [parity_actual_full_mass_exact434]
    exact Finset.sum_nonneg (fun p hp => by positivity)
  have hm := source_B574_shared_mass_nonneg434 (J+1)
    (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)) s hV
  unfold parityRawCapCoefficient434
  positivity

/-- The true kernel-one physical RAW slice satisfies the original dirty
B574 marked envelope with J shared and one endpoint-free slot per group.
Actual prime/disjointness/mass hypotheses are derived internally. -/
theorem parity_raw_actual_physical_marked_bound434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ)
    (hs : ∀ g i,s g i∈b645ActualBand434 L hS g) (w wp : ℕ) :
    ‖parityRawPhysicalSlice434 J (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (1/2:ℝ) w wp s‖ ≤
      parityRawCapCoefficient434 L hS J s * parityRawCapMarkedWeight434 L hS w *
        parityRawCapMarkedWeight434 L hS wp := by
  have hV (g : B645ActualGroup434 L hS) :
      0≤Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L) g := by
    rw [parity_actual_full_mass_exact434]
    exact Finset.sum_nonneg (fun p hp => by positivity)
  exact parity_raw_physical_slice_bound434 J (b645ActualBand434 L hS)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (1/2) w wp s (by norm_num) (by norm_num) hV
    (fun g p hp => (parity_actual_full_band_prime_floor434 L hL.le hS g p hp).1)
    hs (parity_actual_full_band_disjoint434 L hL hS)

/-- One literal RAW cap-loss term retains both original physical cap
gates at DR*w and DR*wp, actual shared arithmetic and the complete K=1
physical slice. The signed shift is imposed by the surrounding carrier. -/
def parityRawCapTerm434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (rho xi3 Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (tw : Bool) (psi : ℝ→ℂ)
    (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ) (w wp : ℕ) : ℂ :=
  let d := sourceB574SharedDilation434 (J+1)
    (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
  (1-parityOriginalPhysicalPairPcap434 L (d*w) (d*wp)) *
    parityHarmonicSharedArithmetic434 L (-xi3) Z lo hi F G (-(rho+xi3)) (-rho) tw 0 psi d 1 w wp *
    parityRawPhysicalSlice434 J (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (1/2:ℝ) w wp s

/-- Both full physical flags and marked endpoint factors survive the
pointwise norm bound. Arithmetic stripping uses the true balanced phases
and retains the finite source seed before taking its indicator bound. -/
theorem parity_raw_cap_term_marked434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (rho xi3 Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (tw : Bool) (psi : ℝ→ℂ)
    (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ)
    (hs : ∀ g i,s g i∈b645ActualBand434 L hS g)
    (w wp : ℕ) (hw : 0<w) (hwp : 0<wp) :
    let d := sourceB574SharedDilation434 (J+1)
      (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
    ‖parityRawCapTerm434 L hS J rho xi3 Z lo hi F G tw psi s w wp‖ ≤
      parityOriginalPhysicalPcapFlags434 L d w wp *
      ‖parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi 1 w wp‖ *
      (parityRawCapCoefficient434 L hS J s * parityRawCapMarkedWeight434 L hS w *
        parityRawCapMarkedWeight434 L hS wp) := by
  dsimp only
  let d := sourceB574SharedDilation434 (J+1)
    (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
  have hA := parity_actual_shared_arithmetic_norm_le434 L hL hS (J+1)
    (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s hs
    rho xi3 Z lo hi F G tw psi 1 w wp (by norm_num) hw hwp
  have hB := parity_raw_actual_physical_marked_bound434 L hL hS J s hs w wp
  have hC := parity_original_physical_Pcap_loss_norm434 L d w wp
  have hC0 := parity_original_physical_Pcap_flags_nonneg434 L d w wp
  unfold parityRawCapTerm434
  dsimp only
  simp only [norm_mul]
  exact mul_le_mul (mul_le_mul hC hA (norm_nonneg _) hC0) hB (norm_nonneg _)
    (mul_nonneg hC0 (norm_nonneg _))

/-- Genuine native/B633 RAW cap domination, with both tau-square endpoint
bounds supplied by the original cores and K=1. The operator tuple is
chosen after the eventual threshold; no endpoint norm bound is assumed. -/
theorem parity_eventually_actual_B633_raw_cap_term434
    (S beta gamma : ℝ) (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1<L ∧
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
          (J : ℕ) (xi3 Z : ℝ) (lo hi : ℕ) (tw : Bool) (psi : ℝ→ℂ)
          (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ),
          (∀ g i,s g i∈b645ActualBand434 L hS g) →
        ∀ (w wp : ℕ), 0<w → 0<wp →
          let d := sourceB574SharedDilation434 (J+1)
            (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
          ‖parityRawCapTerm434 L hS J rho xi3 Z lo hi E G tw psi s w wp‖ ≤
            parityOriginalPhysicalPcapFlags434 L d w wp *
            ((w:ℝ)⁻¹*(w.divisors.card:ℝ)^2*(wp.divisors.card:ℝ)^2*‖psi ((w:ℝ)/Z)‖) *
            (parityRawCapCoefficient434 L hS J s * parityRawCapMarkedWeight434 L hS w *
              parityRawCapMarkedWeight434 L hS wp) := by
  filter_upwards [parity_eventually_actual_B633_stripped_tau434 S beta gamma hSfine hbeta hgamma,
    eventually_gt_atTop (1:ℝ)] with L hCore hL
  refine ⟨hL,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS J xi3 Z lo hi tw psi s hs w wp hw hwp
  let F := sourceNativePrimeCore r e L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let d := sourceB574SharedDilation434 (J+1)
    (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
  have hMain := parity_raw_cap_term_marked434 L hL hS J rho xi3 Z lo hi E G tw psi s hs w wp hw hwp
  dsimp only at hMain
  have hTau := hCore.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma
    xi3 Z tw psi 1 w wp hw hwp
  simp only [Nat.cast_one,mul_one] at hTau
  have hB := parity_raw_actual_physical_marked_bound434 L hL hS J s hs w wp
  have hB0 := (norm_nonneg _).trans hB
  have hC0 := parity_original_physical_Pcap_flags_nonneg434 L d w wp
  exact hMain.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTau hC0) hB0)
end Green64Analytic.Parity

end

end

