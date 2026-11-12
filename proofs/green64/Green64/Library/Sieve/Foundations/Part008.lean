module

public import Green64.Library.Weights.Part116
public import Green64.Library.Sieve.Foundations.Part007
public import Green64.Library.Weights.Part005
public import Green64.Library.Weights.Part003

@[expose] public section

/-!
# Sieve / Foundations / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## UniformPhysicalSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option maxRecDepth 32000

/-- Actual original source estimate with precision fixed before both fine parameters. -/
theorem parity_eventually_B633_actual_literal_raw_harmonic_saving_common_precision434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        ‖(Z : ℂ)*parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
          (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
          1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
          (fun t => (t : ℂ)*psi t) (fun _ _ => 1)‖ ≤ Z*L^(-target) := by
  let KH : ℕ → ℝ := sourceNormalizedLogDerivativeConstants 64 Kpsi
  have hKH : ∀ j, 0 ≤ KH j :=
    source_normalized_log_derivative_constants_nonneg 64 Kpsi (by norm_num) hKpsi
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hH⟩ :=
    parity_eventually_actual_harmonic_physical_saving434
      (target+2) Cfreq Ck Cpsi Kpsi (by linarith) hCk hCpsi hKpsi
  obtain ⟨B,S,hSB,hMain⟩ :=
    parity_eventually_B633_actual_rank_main_saving_common_precision434 jQ m
      (target+2) Cpsi (Cpsi+1) Cfreq CZ Ck (Cq : ℝ) (Cxi : ℝ) KH
      hCpsi hKH (by linarith) hCZ hCk
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hMain := hMain beta gamma hbeta hgamma
  have hSpos : 0 < S := by
    nlinarith [show (0 : ℝ) ≤ (B : ℝ) from Nat.cast_nonneg B]
  have hRest := parity_eventually_actual_harmonic_outer_Z_rank_error434
    J S beta gamma CZ Ck (Cq : ℝ) (Cxi : ℝ) Cpsi (KH 0) (target+2)
    hSpos hbeta hgamma hCZ (hKH 0)
  filter_upwards [hH S beta gamma CZ hSpos hbeta hgamma hCZ,hMain,hRest,
    eventually_ge_atTop (3 : ℝ)] with L hHL hML hRL hL3
  dsimp only at hHL
  obtain ⟨hL1,hQp,hQc,hh,hh2,hxi,hxic,hFamily0,hHsave⟩ := hHL
  refine ⟨hFamily0,hML.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let Q : ℕ := Nat.ceil (4*L^(D+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH) : ℕ) : ℝ)
  let xi : ℝ := L^(-(Cxi : ℝ))
  let psiH : ℝ → ℂ := fun t => (t : ℂ)*psi t
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let H := parityHarmonicPhysical434 L hFamily J m hmJ Q h xi (-xi3) Z Ck k
    (parityDyadicDepth434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0 psiH
  let R := parityActualHarmonicRawPositiveFibreSum434 L hFamily J m hmJ Q h xi (-xi3) Z k
    positions 1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0 psiH
  let Main := parityActualWeightedRankMainFamily434 L hFamily J m hmJ Q h xi
    rho xi3 Ck Z k Ecore Gcore tw psiH
  have hLp : 0 < L := by linarith
  have hZ : 0 < Z :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hh1 : h ≤ 1 := by change h+h ≤ 1 at hh2;change 0 < h at hh;nlinarith
  have hQbound : (Q : ℝ) ≤ L^(Cq : ℝ) := by
    simpa only [Real.rpow_natCast] using hQc
  have hXibound : xi⁻¹ ≤ L^(Cxi : ℝ) := by
    simpa only [Real.rpow_natCast] using hxic
  have hkReal : |(k : ℝ)| ≤ L^Ck := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hkBound
  have hSmoothH : ContDiff ℝ ∞ psiH := Complex.ofRealCLM.contDiff.mul hSmooth
  have hSupportH : ∀ t : ℝ, psiH t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64 := by
    intro t ht
    apply hSupport t
    intro hz
    exact ht (by simp only [psiH,hz,mul_zero])
  have hRegH : sourceLogDerivativeBudget Cpsi KH L (fun u => psiH (Real.exp u)) :=
    source_actual_normalized_log_derivative_budget 64 Cpsi L Kpsi psi
      (by norm_num) hCpsi hKpsi hL1.le hSmooth hSupport hReg
  have hPsiH : ∀ t : ℝ, ‖psiH t‖ ≤ KH 0*L^Cpsi := by
    intro t
    by_cases ht : psiH t = 0
    · rw [ht,norm_zero]
      exact mul_nonneg (hKH 0) (Real.rpow_nonneg hLp.le _)
    · have htp : 0 < t := by linarith [(hSupportH t ht).1]
      simpa only [iteratedDeriv_zero,Nat.cast_zero,zero_add,mul_one,Real.exp_log htp]
        using hRegH 0 (Real.log t)
  have hHsmall : ‖(Z : ℂ)*H‖ ≤ Z*L^(-(target+2)) :=
    hHsave hFamily psi hSmooth hSupport hReg xi3 hxi3 k hk hkBound
      prime lFine uFine hFineLow 20 (sourceOriginalLiteralDepth 20 L) (by norm_num)
      band slot delta freq (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma tw Z hZlo hZhi
  have hMsmall : ‖(Z : ℂ)*Main‖ ≤ Z*L^(-(target+2)) :=
    (hML.2.2 hFamily Z hZlo hZhi J m hmJ (le_refl m) h xi hh hh1 hxi
      band hband slot delta freq k hk hkBound chi rho xi1 xi2 xi3 sigma
      prime lFine uFine a b hFineLow hl hu hub Q hQbound hXibound tw
      hrho hxi1 hxi2 hxi3 hsigma psiH hSmoothH hSupportH hRegH).2
  have hError : ‖(Z : ℂ)*(H-R-Main)‖ ≤ Z*L^(-(target+2)) :=
    hRL.2.2 prime lFine uFine hFineLow 20 (sourceOriginalLiteralDepth 20 L)
      (by norm_num) band slot delta freq (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma hFamily m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi
      hkReal hQbound hXibound tw psiH hSupportH hPsiH
  have hRawSmall : ‖(Z : ℂ)*R‖ ≤ Z*L^(-target) := by
    have hPower : L^2*L^(-(target+2)) = L^(-target) := by
      calc
        _ = L^((2 : ℕ) : ℝ)*L^(-(target+2)) := by rw [Real.rpow_natCast]
        _ = L^(((2 : ℕ) : ℝ)+(-(target+2))) := (Real.rpow_add hLp _ _).symm
        _ = L^(-target) := by congr 1 <;> norm_num <;> ring
    calc
      _ = ‖(Z : ℂ)*H-(Z : ℂ)*Main-(Z : ℂ)*(H-R-Main)‖ := by congr 1;ring
      _ ≤ ‖(Z : ℂ)*H-(Z : ℂ)*Main‖+‖(Z : ℂ)*(H-R-Main)‖ := norm_sub_le _ _
      _ ≤ (‖(Z : ℂ)*H‖+‖(Z : ℂ)*Main‖)+‖(Z : ℂ)*(H-R-Main)‖ :=
        add_le_add (norm_sub_le _ _) (le_refl _)
      _ ≤ (Z*L^(-(target+2))+Z*L^(-(target+2)))+Z*L^(-(target+2)) :=
        add_le_add (add_le_add hHsmall hMsmall) hError
      _ = Z*(3*L^(-(target+2))) := by ring
      _ ≤ Z*(L^2*L^(-(target+2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by nlinarith : (3 : ℝ) ≤ L^2)
            (Real.rpow_nonneg hLp.le _)) hZ.le
      _ = Z*L^(-target) := by rw [hPower]
  have hRawEq : R =
      parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
        positions 1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
        psiH (fun _ _ => 1) := by
    simpa only [R,parityActualEndpointWeightedRawPositiveFibreSum434,
      parityActualHarmonicRawPositiveFibreSum434,one_mul] using
      parity_raw_endpoint_weight_physical_aggregate434 L hL1 hFamily J m hmJ Q h xi (-xi3) Z k
        positions 1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
        psiH (fun _ _ => 1)
  rw [hRawEq] at hRawSmall
  exact hRawSmall

/-- Actual original source estimate with precision fixed before both fine parameters. -/
theorem parity_eventually_B633_actual_capped_literal_raw_saving_common_precision434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        ‖(Z : ℂ)*parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
          (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
          1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
          (fun t => (t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L)‖
          ≤ Z*L^(-target) := by
  let KH : ℕ → ℝ := sourceNormalizedLogDerivativeConstants 64 Kpsi
  have hKH : ∀ j, 0 ≤ KH j :=
    source_normalized_log_derivative_constants_nonneg 64 Kpsi (by norm_num) hKpsi
  obtain ⟨J,B,S,hSB,hRaw⟩ :=
    parity_eventually_B633_actual_literal_raw_harmonic_saving_common_precision434 jQ (target+1)
      Cfreq CZ Ck Cpsi Kpsi (by linarith) hCZ hCk
      hCpsi hKpsi
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hRaw := hRaw beta gamma hbeta hgamma
  have hSpos : 0 < S := by
    nlinarith [show (0 : ℝ) ≤ (B : ℝ) from Nat.cast_nonneg B]
  have hCap := parity_eventually_actual_literal_raw_cap_outer_Z_saving434
    J S beta gamma CZ Ck Cpsi (KH 0) (target+1)
    hSpos hbeta hgamma hCZ (hKH 0)
  filter_upwards [hRaw,hCap,eventually_ge_atTop (2 : ℝ)] with L hRawL hCapL hL2
  refine ⟨hRawL.1,hRawL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let psiH : ℝ → ℂ := fun t => (t : ℂ)*psi t
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let N := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let R := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    N 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH (fun _ _ => 1)
  let T := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    N 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
    (fun n np => 1 - parityOriginalPhysicalPairPcap434 L n np)
  let C := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    N 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
    (parityOriginalPhysicalPairPcap434 L)
  have hLp : 0 < L := by linarith
  have hZ : 0 < Z := (mul_pos (Real.exp_pos L)
    (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hL1 : 1 < L := by linarith
  have hSupportH : ∀ t : ℝ, psiH t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64 := by
    intro t ht
    apply hSupport t
    intro hz
    exact ht (by simp only [psiH,hz,mul_zero])
  have hRegH : sourceLogDerivativeBudget Cpsi KH L
      (fun u => psiH (Real.exp u)) :=
    source_actual_normalized_log_derivative_budget 64 Cpsi L Kpsi psi
      (by norm_num) hCpsi hKpsi hL1.le hSmooth hSupport hReg
  have hSup : ∀ t : ℝ, ‖psiH t‖ ≤ KH 0 * L^Cpsi :=
    parity_original_log_budget_sup434 L Cpsi KH psiH hLp (hKH 0) hSupportH hRegH
  have hkReal : |(k : ℝ)| ≤ L^Ck := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hkBound
  have hR : ‖(Z : ℂ)*R‖ ≤ Z*L^(-(target+1)) :=
    hRawL.2.2 hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
      chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
      prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  have hT : ‖(Z : ℂ)*T‖ ≤ Z*L^(-(target+1)) := by
    have hTmp := hCapL.2.2 prime lFine uFine hFineLow
      20 (sourceOriginalLiteralDepth 20 L) (by norm_num) band slot delta freq
      (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma hFamily 0 (Nat.zero_le J) 1 1 1 xi3
      Z k hZlo hZhi hkReal 1 (parityDyadicLimit434 L) tw psiH
      (fun t ht => (hSupportH t ht)) hSup N
    rw [parity_raw_endpoint_weight_physical_aggregate434 L hL1 hFamily
      J 0 (Nat.zero_le J) 1 1 1 (-xi3) Z k N
      1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
      (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np)] at hTmp
    exact hTmp
  have hC : C = R-T :=
    parity_raw_physical_pcap_difference434 L hFamily J (-xi3) Z k N
      1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
  have hPower : L*L^(-(target+1)) = L^(-target) := by
    calc
      _ = L^(1+(-(target+1))) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hLp (1 : ℝ) (-(target+1))).symm
      _ = L^(-target) := by congr 1; ring
  change ‖(Z : ℂ)*C‖ ≤ Z*L^(-target)
  calc
    _ = ‖(Z : ℂ)*R-(Z : ℂ)*T‖ := by rw [hC]; congr 1; ring
    _ ≤ ‖(Z : ℂ)*R‖+‖(Z : ℂ)*T‖ := norm_sub_le _ _
    _ ≤ Z*L^(-(target+1))+Z*L^(-(target+1)) := add_le_add hR hT
    _ = Z*(2*L^(-(target+1))) := by ring
    _ ≤ Z*(L*L^(-(target+1))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hL2 (Real.rpow_nonneg hLp.le _)) hZ.le
    _ = Z*L^(-target) := by rw [hPower]

/-- Actual original source estimate with precision fixed before both fine parameters. -/
theorem parity_eventually_actual_capped_physical_B521_source_saving_common_precision434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
        let N := parityPositiveNaturalPositions434 positions
        let physical := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
          positions 1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
          (fun t => (t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L)
        let original := sourceNativeGatedChannel N (sourceOriginalPAllActualBands 20 L)
          (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
          Ecore Gcore k (rho+xi3) (-rho)
          (fun n => if ((n : ℤ)+2*k).toNat∈N then
            (Z : ℂ)⁻¹*psi ((n : ℝ)/Z) else 0) tw tw
        ‖(Z : ℂ)*(physical-original)‖ ≤ Z*L^(-target) ∧
        ‖(Z : ℂ)*original‖ ≤ Z*L^(-target) := by
  let KH : ℕ → ℝ := sourceNormalizedLogDerivativeConstants 64 Kpsi
  have hKH : ∀ j, 0 ≤ KH j :=
    source_normalized_log_derivative_constants_nonneg 64 Kpsi (by norm_num) hKpsi
  obtain ⟨J,B,S,hSB,hRaw⟩ :=
    parity_eventually_B633_actual_literal_raw_harmonic_saving_common_precision434 jQ (target+1)
      Cfreq CZ Ck Cpsi Kpsi (by linarith) hCZ hCk
      hCpsi hKpsi
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hRaw := hRaw beta gamma hbeta hgamma
  have hSpos : 0 < S := by
    nlinarith [show (0 : ℝ) ≤ (B : ℝ) from Nat.cast_nonneg B]
  have hTail := parity_eventually_actual_literal_raw_cap_outer_Z_saving434
    J S beta gamma CZ Ck Cpsi (KH 0) (target+1)
    hSpos hbeta hgamma hCZ (hKH 0)
  have hRest := parity_eventually_actual_physical_raw_stripping434
    J S beta gamma CZ Ck Cpsi (KH 0) (target+1)
    hSpos hbeta hgamma hCZ (hKH 0)
  have hQuot := parity_eventually_actual_normalized_raw_quotient_cap_loss434
    S beta gamma CZ Ck Cpsi (target+1) Kpsi
    hSpos hbeta hgamma hCZ hCpsi hKpsi
  filter_upwards [hRaw,hTail,hRest,hQuot,eventually_ge_atTop (3 : ℝ)]
    with L hRawL hTailL hRestL hQuotL hL3
  refine ⟨hRawL.1,hRawL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let psiH : ℝ → ℂ := fun t => (t : ℂ)*psi t
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let N := parityPositiveNaturalPositions434 positions
  let P := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    positions 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH (fun _ _ => 1)
  let Pc := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    positions 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
    (parityOriginalPhysicalPairPcap434 L)
  let T := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    positions 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
    (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np)
  let U := parityRawStrippedHarmonic434 L hFamily rho xi3 Z k N E G tw psiH (fun _ _ => 1)
  let C := parityRawStrippedHarmonic434 L hFamily rho xi3 Z k N E G tw psiH
    (parityOriginalPhysicalPairPcap434 L)
  let Src := sourceNativeGatedChannel N (sourceOriginalPAllActualBands 20 L)
    (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
    E G k (rho+xi3) (-rho)
    (fun n => if ((n : ℤ)+2*k).toNat∈N then
      (Z : ℂ)⁻¹*psi ((n : ℝ)/Z) else 0) tw tw
  have hLp : 0 < L := by linarith
  have hL1 : 1 < L := by linarith
  have hZ : 0 < Z := (mul_pos (Real.exp_pos L)
    (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hSupportH : ∀ t : ℝ, psiH t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64 := by
    intro t ht
    apply hSupport t
    intro hz
    exact ht (by simp only [psiH,hz,mul_zero])
  have hRegH : sourceLogDerivativeBudget Cpsi KH L
      (fun u => psiH (Real.exp u)) :=
    source_actual_normalized_log_derivative_budget 64 Cpsi L Kpsi psi
      (by norm_num) hCpsi hKpsi hL1.le hSmooth hSupport hReg
  have hSup : ∀ t : ℝ, ‖psiH t‖ ≤ KH 0 * L^Cpsi :=
    parity_original_log_budget_sup434 L Cpsi KH psiH hLp (hKH 0) hSupportH hRegH
  have hkReal : |(k : ℝ)| ≤ L^Ck := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hkBound
  have hNpos : ∀ n ∈ N, 0 < n := by
    intro n hn
    exact ((parity_positive_natural_positions_mem434 _ n).mp hn).1
  have hRawSmall : ‖(Z : ℂ)*P‖ ≤ Z*L^(-(target+1)) :=
    hRawL.2.2 hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
      chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
      prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  have hTailSmall : ‖(Z : ℂ)*T‖ ≤ Z*L^(-(target+1)) := by
    have hTmp := hTailL.2.2 prime lFine uFine hFineLow
      20 (sourceOriginalLiteralDepth 20 L) (by norm_num) band slot delta freq
      (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma hFamily 0 (Nat.zero_le J) 1 1 1 xi3
      Z k hZlo hZhi hkReal 1 (parityDyadicLimit434 L) tw psiH
      (fun t ht => (hSupportH t ht)) hSup positions
    rw [parity_raw_endpoint_weight_physical_aggregate434 L hL1 hFamily
      J 0 (Nat.zero_le J) 1 1 1 (-xi3) Z k positions
      1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
      (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np)] at hTmp
    exact hTmp
  have hRestPair := hRestL.2.2 prime lFine uFine hFineLow
      20 (sourceOriginalLiteralDepth 20 L) (by norm_num) band slot delta freq
      (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma hFamily xi3 Z k hZlo hZhi hkBound tw psiH
      (fun t ht => Set.mem_Icc.mpr (hSupportH t ht)) hSup
  have hRestSmall : ‖(Z : ℂ)*(P-U)‖ ≤ Z*L^(-(target+1)) := hRestPair.2
  have hQuotPair := hQuotL.2.2 prime lFine uFine hFineLow
      20 (sourceOriginalLiteralDepth 20 L) (by norm_num) band slot delta freq
      (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma hFamily xi3 Z k hZlo hZhi hkReal
      tw psi hSmooth hSupport hReg positions
  have hQuotSmall : ‖(Z : ℂ)*(U-C)‖ ≤ Z*L^(-(target+1)) := hQuotPair.2
  have hPhysicalCap : Pc=P-T :=
    parity_raw_physical_pcap_difference434 L hFamily J (-xi3) Z k positions
      1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
  have hTailDiff : ‖(Z : ℂ)*(Pc-P)‖ ≤ Z*L^(-(target+1)) := by
    have heq : Pc-P = -T := by rw [hPhysicalCap]; ring
    rw [heq,mul_neg,norm_neg]
    exact hTailSmall
  have hSource : C=Src :=
    parity_raw_stripped_original_B521_normalized434
      L hL1 hFamily rho xi3 Z hZ k hk N hNpos E G tw psi hSupport
  have hPower : L*L^(-(target+1)) = L^(-target) := by
    calc
      _ = L^(1+(-(target+1))) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hLp (1 : ℝ) (-(target+1))).symm
      _ = L^(-target) := by congr 1; ring
  have hBudget : 3*(Z*L^(-(target+1))) ≤ Z*L^(-target) := by
    calc
      _ = Z*(3*L^(-(target+1))) := by ring
      _ ≤ Z*(L*L^(-(target+1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hL3 (Real.rpow_nonneg hLp.le _)) hZ.le
      _ = Z*L^(-target) := by rw [hPower]
  have hBridge : ‖(Z : ℂ)*(Pc-C)‖ ≤ Z*L^(-target) := by
    have heq : Pc-C = (Pc-P)+(P-U)+(U-C) := by ring
    rw [heq,mul_add,mul_add]
    have hTrip := (norm_add_le ((Z : ℂ)*(Pc-P)+(Z : ℂ)*(P-U)) ((Z : ℂ)*(U-C)))
    have hDuo := (norm_add_le ((Z : ℂ)*(Pc-P)) ((Z : ℂ)*(P-U)))
    have hBound : ‖(Z : ℂ)*(Pc-P)+(Z : ℂ)*(P-U)+(Z : ℂ)*(U-C)‖ ≤
        3*(Z*L^(-(target+1))) := by
      calc
        _ ≤ ‖(Z : ℂ)*(Pc-P)+(Z : ℂ)*(P-U)‖+‖(Z : ℂ)*(U-C)‖ := hTrip
        _ ≤ (‖(Z : ℂ)*(Pc-P)‖+‖(Z : ℂ)*(P-U)‖)+‖(Z : ℂ)*(U-C)‖ :=
          add_le_add_left hDuo _
        _ ≤ 3*(Z*L^(-(target+1))) := by linarith
    exact hBound.trans hBudget
  have hSourceSmall : ‖(Z : ℂ)*C‖ ≤ Z*L^(-target) := by
    have heq : C = P-(P-U)-(U-C) := by ring
    rw [heq,mul_sub,mul_sub]
    have hTrip := norm_sub_le ((Z : ℂ)*P-(Z : ℂ)*(P-U)) ((Z : ℂ)*(U-C))
    have hDuo := norm_sub_le ((Z : ℂ)*P) ((Z : ℂ)*(P-U))
    have hBound : ‖(Z : ℂ)*P-(Z : ℂ)*(P-U)-(Z : ℂ)*(U-C)‖ ≤
        3*(Z*L^(-(target+1))) := by
      calc
        _ ≤ ‖(Z : ℂ)*P-(Z : ℂ)*(P-U)‖+‖(Z : ℂ)*(U-C)‖ := hTrip
        _ ≤ (‖(Z : ℂ)*P‖+‖(Z : ℂ)*(P-U)‖)+‖(Z : ℂ)*(U-C)‖ :=
          add_le_add_left hDuo _
        _ ≤ 3*(Z*L^(-(target+1))) := by linarith
    exact hBound.trans hBudget
  change ‖(Z : ℂ)*(Pc-Src)‖ ≤ Z*L^(-target) ∧
    ‖(Z : ℂ)*Src‖ ≤ Z*L^(-target)
  rw [←hSource]
  exact ⟨hBridge,hSourceSmall⟩

/-- Actual original source estimate with precision fixed before both fine parameters. -/
theorem parity_eventually_actual_capped_physical_B521_full_interval_saving_common_precision434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
        let physical := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
          positions 1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
          (fun t => (t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L)
        let original := sourceNativeGatedChannel (Finset.Icc 1 ⌊64*Z⌋₊)
          (sourceOriginalPAllActualBands 20 L)
          (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
          Ecore Gcore k (rho+xi3) (-rho)
          (fun n => psi ((n : ℝ)/Z)) tw tw
        ‖(Z : ℂ)*physical-original‖ ≤ Z*L^(-target) ∧
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hBridge⟩ :=
    parity_eventually_actual_capped_physical_B521_source_saving_common_precision434 jQ target
      Cfreq CZ Ck Cpsi Kpsi hTarget hCZ hCk hCpsi hKpsi
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hBridge := hBridge beta gamma hbeta hgamma
  have hNorm := parity_eventually_raw_original_B521_outer_Z434 CZ Ck hCZ
  filter_upwards [hBridge,hNorm] with L hBridgeL hNormL
  refine ⟨hBridgeL.1,hBridgeL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let N := parityPositiveNaturalPositions434 positions
  let P := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    positions 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0
    (fun t => (t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L)
  let SrcN := sourceNativeGatedChannel N (sourceOriginalPAllActualBands 20 L)
    (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
    E G k (rho+xi3) (-rho)
    (fun n => if ((n : ℤ)+2*k).toNat∈N then
      (Z : ℂ)⁻¹*psi ((n : ℝ)/Z) else 0) tw tw
  let SrcFull := sourceNativeGatedChannel (Finset.Icc 1 ⌊64*Z⌋₊)
    (sourceOriginalPAllActualBands 20 L)
    (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
    E G k (rho+xi3) (-rho) (fun n => psi ((n : ℝ)/Z)) tw tw
  have hL1 : 1 < L := hNormL.1
  have hLp : 0 < L := by linarith
  have hZ : 0 < Z := (mul_pos (Real.exp_pos L)
    (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hNpos : ∀ n ∈ N, 0 < n := by
    intro n hn
    exact ((parity_positive_natural_positions_mem434 _ n).mp hn).1
  have hStripped :
    parityRawStrippedHarmonic434 L hFamily rho xi3 Z k N E G tw
      (fun t => (t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L) = SrcN :=
    parity_raw_stripped_original_B521_normalized434
      L hL1 hFamily rho xi3 Z hZ k hk N hNpos E G tw psi hSupport
  have hOldNorm := hNormL.2 hFamily J rho xi3 Z hZlo hZhi k hk hkBound E G tw psi hSupport
  have hSrcEq : (Z : ℂ)*SrcN = SrcFull := by
    rw [←hStripped]
    exact hOldNorm
  have hPair := hBridgeL.2.2 hFamily Z hZlo hZhi band hband slot delta freq
    k hk hkBound chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  change ‖(Z : ℂ)*(P-SrcN)‖ ≤ Z*L^(-target) ∧
    ‖(Z : ℂ)*SrcN‖ ≤ Z*L^(-target) at hPair
  change ‖(Z : ℂ)*P-SrcFull‖ ≤ Z*L^(-target) ∧
    ‖SrcFull‖ ≤ Z*L^(-target)
  constructor
  · calc
      _ = ‖(Z : ℂ)*(P-SrcN)‖ := by rw [←hSrcEq]; congr 1; ring
      _ ≤ Z*L^(-target) := hPair.1
  · rw [←hSrcEq]
    exact hPair.2

/-- Actual original source estimate with precision fixed before both fine parameters. -/
theorem parity_eventually_B633_original_ungated_eq417_saving_common_precision434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
        let original := parityOriginalEq417Ungated434 L rho xi3 Z k
          (Finset.Icc 1 ⌊64*Z⌋₊) Ecore Gcore tw psi
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hCapped⟩ :=
    parity_eventually_actual_capped_physical_B521_full_interval_saving_common_precision434
      jQ (target+1) Cfreq CZ Ck Cpsi Kpsi
      (by linarith) hCZ hCk hCpsi hKpsi
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hCapped := hCapped beta gamma hbeta hgamma
  have hSpos : 0 < S := by
    nlinarith [show (0 : ℝ) ≤ (B : ℝ) from Nat.cast_nonneg B]
  have hQuot := parity_eventually_actual_normalized_raw_quotient_cap_loss434
    S beta gamma CZ Ck Cpsi (target+1) Kpsi
    hSpos hbeta hgamma hCZ hCpsi hKpsi
  have hSource := parity_eventually_raw_original_B521_outer_Z434 CZ Ck hCZ
  have hUngated := parity_eventually_raw_original_ungated_eq417434 CZ Ck hCZ
  filter_upwards [hCapped,hQuot,hSource,hUngated,eventually_ge_atTop (2 : ℝ)]
    with L hCappedL hQuotL hSourceL hUngatedL hL2
  refine ⟨hCappedL.1,hCappedL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let psiH : ℝ → ℂ := fun t => (t : ℂ)*psi t
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let N := parityPositiveNaturalPositions434 positions
  let U := parityRawStrippedHarmonic434 L hFamily rho xi3 Z k N E G tw psiH (fun _ _ => 1)
  let C := parityRawStrippedHarmonic434 L hFamily rho xi3 Z k N E G tw psiH
    (parityOriginalPhysicalPairPcap434 L)
  let SrcC := sourceNativeGatedChannel (Finset.Icc 1 ⌊64*Z⌋₊)
    (sourceOriginalPAllActualBands 20 L)
    (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
    E G k (rho+xi3) (-rho) (fun n => psi ((n : ℝ)/Z)) tw tw
  let SrcU := parityOriginalEq417Ungated434 L rho xi3 Z k
    (Finset.Icc 1 ⌊64*Z⌋₊) E G tw psi
  have hLp : 0 < L := by linarith
  have hZ : 0 < Z := (mul_pos (Real.exp_pos L)
    (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hkReal : |(k : ℝ)| ≤ L^Ck := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hkBound
  have hCappedSmall : ‖SrcC‖ ≤ Z*L^(-(target+1)) :=
    (hCappedL.2.2 hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
      chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
      prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg).2
  have hQuotPair := hQuotL.2.2 prime lFine uFine hFineLow
    20 (sourceOriginalLiteralDepth 20 L) (by norm_num) band slot delta freq
    (Finset.Icc a b) (2*k.natAbs) chi 0 0
    xi1 xi2 rho sigma hFamily xi3 Z k hZlo hZhi hkReal
    tw psi hSmooth hSupport hReg positions
  have hQuotSmall : ‖(Z : ℂ)*(U-C)‖ ≤ Z*L^(-(target+1)) := hQuotPair.2
  have hCappedEq : (Z : ℂ)*C = SrcC :=
    hSourceL.2 hFamily J rho xi3 Z hZlo hZhi k hk hkBound E G tw psi hSupport
  have hUngatedEq : (Z : ℂ)*U = SrcU :=
    hUngatedL.2 hFamily J rho xi3 Z hZlo hZhi k hk hkBound E G tw psi hSupport
  have hCappedZ : ‖(Z : ℂ)*C‖ ≤ Z*L^(-(target+1)) := by
    rw [hCappedEq]
    exact hCappedSmall
  have hPower : L*L^(-(target+1)) = L^(-target) := by
    calc
      _ = L^(1+(-(target+1))) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hLp (1 : ℝ) (-(target+1))).symm
      _ = L^(-target) := by congr 1; ring
  change ‖SrcU‖ ≤ Z*L^(-target)
  rw [←hUngatedEq]
  have hSplit : U = C+(U-C) := by ring
  rw [hSplit,mul_add]
  calc
    _ ≤ ‖(Z : ℂ)*C‖+‖(Z : ℂ)*(U-C)‖ := norm_add_le _ _
    _ ≤ Z*L^(-(target+1))+Z*L^(-(target+1)) := add_le_add hCappedZ hQuotSmall
    _ = Z*(2*L^(-(target+1))) := by ring
    _ ≤ Z*(L*L^(-(target+1))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hL2 (Real.rpow_nonneg hLp.le _)) hZ.le
    _ = Z*L^(-target) := by rw [hPower]

/-- Actual original source estimate with precision fixed before both fine parameters. -/
theorem parity_eventually_B633_original_Parity417_direct_saving_common_precision434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Fparity := b633ParityFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        let original := parityOriginalEq417WithFirstCore434 L rho xi3 Z k
          (Finset.Icc 1 ⌊64*Z⌋₊) Fparity Gcore tw psi
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hOld⟩ :=
    parity_eventually_B633_original_ungated_eq417_saving_common_precision434 jQ target
      Cfreq CZ Ck Cpsi Kpsi hTarget hCZ hCk hCpsi hKpsi
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hOld := hOld beta gamma hbeta hgamma
  filter_upwards [hOld] with L hOldL
  refine ⟨hOldL.1,hOldL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let Fparity := b633ParityFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let SrcE := parityOriginalEq417Ungated434 L rho xi3 Z k
    (Finset.Icc 1 ⌊64*Z⌋₊) E G tw psi
  let SrcF := parityOriginalEq417WithFirstCore434 L rho xi3 Z k
    (Finset.Icc 1 ⌊64*Z⌋₊) Fparity G tw psi
  have hBound : ‖SrcE‖ ≤ Z*L^(-target) :=
    hOldL.2.2 hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
      chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
      prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  have hIdentity : SrcE = SrcF :=
    parity_original_eq417_literal_first_core434 L rho xi3 Z xi2 sigma k
      (Finset.Icc 1 ⌊64*Z⌋₊) F.alpha F.residual (2*k.natAbs) chi F.lo F.hi
      G tw psi
  change ‖SrcF‖ ≤ Z*L^(-target)
  rw [←hIdentity]
  exact hBound

/-- Actual original source estimate with precision fixed before both fine parameters. -/
theorem parity_eventually_actual_original_Parity417_physical_cofactor_saving_common_precision434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let original := parityOriginalEq417PhysicalCofactors434 L rho xi1 xi2 xi3 sigma Z k
          (Finset.Icc 1 ⌊64*Z⌋₊) F.alpha F.residual (2*k.natAbs) chi F.lo F.hi tw psi
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hDirect⟩ :=
    parity_eventually_B633_original_Parity417_direct_saving_common_precision434 jQ target
      Cfreq CZ Ck Cpsi Kpsi hTarget hCZ hCk hCpsi hKpsi
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hDirect := hDirect beta gamma hbeta hgamma
  have hSpos : 0 < S := by
    nlinarith [show (0 : ℝ) ≤ (B : ℝ) from Nat.cast_nonneg B]
  have hRough := parity_actual_fine_K_restricted_rough434 S beta gamma
    hSpos hbeta hgamma
  filter_upwards [hDirect,hRough,eventually_ge_atTop (1 : ℝ)]
    with L hDirectL hRoughL hL
  refine ⟨hDirectL.1,hDirectL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let First := b633ParityFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let Second := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let N := Finset.Icc 1 ⌊64*Z⌋₊
  let SumPhysical := parityOriginalEq417PhysicalCofactors434 L rho xi1 xi2 xi3 sigma Z k N
    F.alpha F.residual (2*k.natAbs) chi F.lo F.hi tw psi
  let SumDirect := parityOriginalEq417WithFirstCore434 L rho xi3 Z k N First Second tw psi
  have hFullGroup := parity_original_actual_full_P_prime_rough_cap434 L hL
  have hp : ∀ g p, p ∈ sourceOriginalPAllActualBands 20 L g → p.Prime :=
    fun g p h => (hFullGroup g p h).1
  have hW : ∀ g p, p ∈ sourceOriginalPAllActualBands 20 L g →
      (p:ℝ) ≤ Real.exp (Real.sqrt L) :=
    fun g p h => (hFullGroup g p h).2
  have hRough' : ∀ m, F.alpha m ≠ 0 →
      sourceD20Rough (Real.exp (Real.sqrt L)) m := by
    intro m hm
    exact hRoughL prime lFine uFine hl hFineLow (Finset.Icc a b) m hm
  have hN : ∀ z∈N,0<z := by
    intro z hz
    exact (Finset.mem_Icc.mp hz).1
  have hEq : SumPhysical = SumDirect :=
    parity_original_eq417_physical_cofactors_exact434 L rho xi1 xi2 xi3 sigma Z k N hN
      F.alpha F.residual (2*k.natAbs) chi F.lo F.hi tw psi
      (Real.exp (Real.sqrt L)) hp hW hRough'
  have hSaving : ‖SumDirect‖ ≤ Z*L^(-target) :=
    hDirectL.2.2 hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
      chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
      prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  change ‖SumPhysical‖ ≤ Z*L^(-target)
  rw [hEq]
  exact hSaving

end Green64Analytic.Parity

end

end

/-! ## ShiftTwoRoughUnit -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 28000

/-- Derive, rather than assume, the original Parity (2.5) m-unit property:
a genuinely W-rough integer cannot share any prime factor with a
positive modulus q<=W. The original roughness is the exact sourceD20Rough
condition, including its minimum-prime-factor strict inequality. -/
theorem parity_actual_rough_modulus_unit434
    (W : ℝ) (m q : ℕ)
    (hm : sourceD20Rough W m) (hq : 0 < q) (hqW : (q : ℝ) ≤ W) :
    IsUnit (m : ZMod q) := by
  apply (ZMod.isUnit_iff_coprime m q).mpr
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hn
  have hgpos : 0 < m.gcd q := Nat.gcd_pos_of_pos_right m hq
  have hg2 : 2 ≤ m.gcd q := by omega
  have hp : Nat.Prime (m.gcd q).minFac := Nat.minFac_prime (by omega)
  have hpdivm : (m.gcd q).minFac ∣ m :=
    (Nat.minFac_dvd (m.gcd q)).trans (Nat.gcd_dvd_left m q)
  have hpdivq : (m.gcd q).minFac ∣ q :=
    (Nat.minFac_dvd (m.gcd q)).trans (Nat.gcd_dvd_right m q)
  have hlow : m.minFac ≤ (m.gcd q).minFac :=
    Nat.minFac_le_of_dvd hp.two_le hpdivm
  have hupp : (m.gcd q).minFac ≤ q := Nat.le_of_dvd hq hpdivq
  have hbound : (m.minFac : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hlow.trans hupp
  exact (not_lt_of_ge (hbound.trans hqW)) hm.2
end Green64Analytic.Parity

end

end

/-! ## ShiftTwoActualRoughUnit -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 28000

/-- At every actual logarithmic signed shift k and sufficiently large L,
the genuine W=exp(sqrt L) roughness forces the original cofactor m to be
a unit modulo Q=2|k|. No source unit hypothesis is assumed. -/
theorem parity_eventually_actual_rough_shift_unit434 (Ck : ℝ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
      ∀ (m : ℕ), sourceD20Rough (Real.exp (Real.sqrt L)) m →
        IsUnit (m : ZMod (2*k.natAbs)) := by
  filter_upwards [b638_eventually_poly_exp434 2 Ck (1/2) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hPoly hL
  refine ⟨hL,?_⟩
  intro k hk hkBound m hm
  have hq : 0 < 2*k.natAbs := by
    have hkpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
    omega
  have hPoly' : 2*L^Ck ≤ Real.exp (Real.sqrt L) := by
    simpa only [Real.sqrt_eq_rpow] using hPoly
  have hqW : ((2*k.natAbs : ℕ) : ℝ) ≤ Real.exp (Real.sqrt L) := by
    calc
      _ = 2*(k.natAbs : ℝ) := by push_cast; ring
      _ ≤ 2*L^Ck := mul_le_mul_of_nonneg_left hkBound (by norm_num)
      _ ≤ Real.exp (Real.sqrt L) := hPoly'
  exact parity_actual_rough_modulus_unit434 _ m _ hm hq hqW

/-- On the ACTUAL original b629 K-restricted prime/proxy coefficient,
the true Parity (2.5) modulus Q=2|k| unit property follows automatically
for every nonzero α(m), not supplied as an extra hypothesis. Holds for
all signed logarithmic k and every retained K interval and prime toggle. -/
theorem parity_eventually_actual_fine_alpha_shift_unit434
    (S beta gamma Ck : ℝ)
    (hS : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ (prime : Bool) (l u : ℕ), 2 ≤ l →
        Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k ≠ 0 →
        (k.natAbs : ℝ) ≤ L^Ck →
      ∀ (m : ℕ),
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) m ≠ 0 →
        IsUnit (m : ZMod (2*k.natAbs)) := by
  filter_upwards [parity_actual_fine_K_restricted_rough434 S beta gamma hS hbeta hgamma,
    parity_eventually_actual_rough_shift_unit434 Ck] with L hRough hUnit
  refine ⟨hUnit.1,?_⟩
  intro prime l u hl hlow K k hk hkBound m hm
  exact hUnit.2 k hk hkBound m (hRough prime l u hl hlow K m hm)
end Green64Analytic.Parity

end

end

/-! ## ShiftTwoActualRoughOdd -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 28000

/-- Original W-rough m is automatically odd once W>=2; zero and
unit m=1 are already excluded by sourceD20Rough's genuine 2<=m.
This derives rather than assumes Parity (2.5)'s odd source cofactor. -/
theorem parity_original_rough_cofactor_odd434
    (W : ℝ) (m : ℕ) (hW : 2 ≤ W)
    (hm : sourceD20Rough W m) : Odd m := by
  by_contra hn
  have he : Even m := Nat.not_odd_iff_even.mp hn
  rcases he with ⟨t,ht⟩
  have hd : 2 ∣ m := ⟨t,by omega⟩
  have hmin : m.minFac ≤ 2 := Nat.minFac_le_of_dvd (by norm_num) hd
  have hreal : (m.minFac : ℝ) ≤ 2 := by exact_mod_cast hmin
  exact (not_lt_of_ge (hreal.trans hW)) hm.2

/-- On original L>=1 roughness scale, exp(sqrt L) is at least two.
No separate parity support condition is required. -/
theorem parity_rough_cutoff_at_least_two434 (L : ℝ) (hL : 1 ≤ L) :
    (2 : ℝ) ≤ Real.exp (Real.sqrt L) := by
  have hroot : (1 : ℝ) ≤ Real.sqrt L := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  calc
    (2 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
    _ ≤ Real.exp (Real.sqrt L) := Real.exp_le_exp.mpr hroot

/-- Every actual long-prime/fine proxy coefficient is odd and a unit
modulo 2|k| whenever nonzero, uniformly for every original operator
interval K and signed logarithmic k. This derives BOTH Parity (2.5) gates. -/
theorem parity_eventually_actual_fine_alpha_odd_and_unit434
    (S beta gamma Ck : ℝ)
    (hS : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ (prime : Bool) (l u : ℕ), 2 ≤ l →
        Real.exp (beta*L) ≤ (l : ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k ≠ 0 →
        (k.natAbs : ℝ) ≤ L^Ck →
      ∀ (m : ℕ),
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) m ≠ 0 →
        Odd m ∧ IsUnit (m : ZMod (2*k.natAbs)) := by
  filter_upwards [parity_actual_fine_K_restricted_rough434 S beta gamma hS hbeta hgamma,
    parity_eventually_actual_fine_alpha_shift_unit434 S beta gamma Ck hS hbeta hgamma]
    with L hRough hUnit
  refine ⟨hUnit.1,?_⟩
  intro prime l u hl hlow K k hk hkBound m hm
  have hR : sourceD20Rough (Real.exp (Real.sqrt L)) m :=
    hRough prime l u hl hlow K m hm
  exact ⟨parity_original_rough_cofactor_odd434 _ m
    (parity_rough_cutoff_at_least_two434 L hUnit.1) hR,
    hUnit.2 prime l u hl hlow K k hk hkBound m hm⟩
end Green64Analytic.Parity

end

end

/-! ## ShiftTwoActualIntegerPairs -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 30000

/-- GENUINE actual b629 alpha support discharges all original odd/unit
hypotheses for the h=-2 Parity (2.3)-(2.7) finite-cofactor Fourier mask.
The amplitudes and pair index set remain arbitrary and the exact source
character mask is used. This does NOT assume a character-sum estimate. -/
theorem parity_eventually_actual_fine_integer_pair_mask_fourier434
    (S beta gamma Ck : ℝ)
    (hS : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ (prime : Bool) (l u : ℕ), 2 ≤ l →
        Real.exp (beta*L) ≤ (l : ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k ≠ 0 →
        (k.natAbs : ℝ) ≤ L^Ck →
      ∀ {I : Type} [DecidableEq I] (T : Finset I)
        (m mp : I → ℕ),
        (∀ i ∈ T,
          restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) (m i) ≠ 0 ∧
          restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) (mp i) ≠ 0) →
      ∀ (A : I → ℂ),
      (∑ i ∈ T, A i *
        (if k ∣ ((mp i : ℕ) : ℤ)-((m i : ℕ) : ℤ) ∧
          Odd ((((mp i : ℕ) : ℤ)-((m i : ℕ) : ℤ))/k)
          then (1 : ℂ) else 0)) =
      ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
        (∑ i ∈ T, A i * chi ((mp i : ℕ) : ZMod (2*k.natAbs)) *
          star (chi ((m i : ℕ) : ZMod (2*k.natAbs)))) := by
  filter_upwards [parity_eventually_actual_fine_alpha_odd_and_unit434
    S beta gamma Ck hS hbeta hgamma] with L hInput
  refine ⟨hInput.1,?_⟩
  intro prime l u hl hlow K k hk hkBound I instI T m mp hNonzero A
  have hmOdd : ∀ i ∈ T, Odd ((m i : ℕ) : ℤ) := by
    intro i hi
    have h := (hInput.2 prime l u hl hlow K k hk hkBound (m i) (hNonzero i hi).1).1
    exact_mod_cast h
  have hmpOdd : ∀ i ∈ T, Odd ((mp i : ℕ) : ℤ) := by
    intro i hi
    have h := (hInput.2 prime l u hl hlow K k hk hkBound (mp i) (hNonzero i hi).2).1
    exact_mod_cast h
  have hmUnit : ∀ i ∈ T,
      IsUnit (((m i : ℕ) : ℤ) : ZMod (2*k.natAbs)) := by
    intro i hi
    have h := (hInput.2 prime l u hl hlow K k hk hkBound (m i) (hNonzero i hi).1).2
    simpa using h
  simpa only [Int.cast_natCast] using
    (parity_signed_k_finite_integer_pair_fourier_expansion434 k hk T
      (fun i => ((m i : ℕ) : ℤ)) (fun i => ((mp i : ℕ) : ℤ))
      hmOdd hmpOdd hmUnit A)
end Green64Analytic.Parity

end

end

/-! ## ShiftTwoBilinearMaskSource -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 28000

/-- In the original h=-2 source with odd e and two odd rough cofactors,
any derived integer Cauchy shift k must be even. This is a genuine unit
compatibility condition, not a parity approximation to the ratio mask. -/
theorem parity_original_shift_even_of_odd_bilinear434
    (e m mp : ℕ) (he : Odd e) (hm : Odd m) (hp : Odd mp)
    (k : ℤ) (hshift : (mp : ℤ)-(m : ℤ)=(e : ℤ)*k) : Even k := by
  have heI : Odd (e : ℤ) := by exact_mod_cast he
  have hmI : Odd (m : ℤ) := by exact_mod_cast hm
  have hpI : Odd (mp : ℤ) := by exact_mod_cast hp
  have hdiff : Even ((mp : ℤ)-(m : ℤ)) := hpI.sub_odd hmI
  have hprod : Even ((e : ℤ)*k) := by rw [←hshift]; exact hdiff
  by_contra hn
  have hkOdd : Odd k := Int.not_even_iff_odd.mp hn
  have hOddProd : Odd ((e : ℤ)*k) := heI.mul hkOdd
  rcases hprod with ⟨a,ha⟩
  rcases hOddProd with ⟨b,hb⟩
  omega

/-- Literal odd e = (mp-m)/k, NOT a substituted odd-quotient gate.
This is the original Parity (2.2) shift equation for signed k. -/
theorem parity_original_shift_quotient_eq_e434
    (e m mp : ℕ) (k : ℤ) (hk : k ≠ 0)
    (hshift : (mp : ℤ)-(m : ℤ)=(e : ℤ)*k) :
    (((mp : ℤ)-(m : ℤ))/k)=(e : ℤ) := by
  rw [hshift]
  rw [mul_comm]
  exact Int.mul_ediv_cancel_left (e : ℤ) hk

/-- On the exact original Parity h=-2 Cauchy pair with m'-m=e*k and
original odd e,m,m', the entire original character Fourier projector
is IDENTICALLY ONE. The m-unit condition is derived from actual W-rough
support plus q=2|k|<=W; no mask cancellation or assumed E theorem. -/
theorem parity_original_bilinear_shift_mask_fourier_one434
    (e m mp : ℕ) (he : Odd e) (hm : Odd m) (hp : Odd mp)
    (k : ℤ) (hk : k ≠ 0)
    (hshift : (mp : ℤ)-(m : ℤ)=(e : ℤ)*k)
    (W : ℝ) (hrough : sourceD20Rough W m)
    (hq : ((2*k.natAbs : ℕ) : ℝ) ≤ W) :
    Even k ∧
      (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
        chi (mp : ZMod (2*k.natAbs)) * star (chi (m : ZMod (2*k.natAbs))))=1 := by
  have hEven := parity_original_shift_even_of_odd_bilinear434 e m mp he hm hp k hshift
  have hunit : IsUnit (m : ZMod (2*k.natAbs)) :=
    parity_actual_rough_modulus_unit434 W m _ hrough
      (by have hpos := Int.natAbs_pos.mpr hk; omega) hq
  have heI : Odd (e : ℤ) := by exact_mod_cast he
  have hmI : Odd (m : ℤ) := by exact_mod_cast hm
  have hpI : Odd (mp : ℤ) := by exact_mod_cast hp
  have hdiv : k ∣ (mp : ℤ)-(m : ℤ) := by
    refine ⟨(e : ℤ),?_⟩
    rw [hshift]
    ring
  have hquot : Odd (((mp : ℤ)-(m : ℤ))/k) := by
    rw [parity_original_shift_quotient_eq_e434 e m mp k hk hshift]
    exact heI
  have hunitI : IsUnit ((m : ℤ) : ZMod (2*k.natAbs)) := by
    simpa only [Int.cast_natCast] using hunit
  have hFour := parity_signed_k_original_integer_fourier_expansion434
    k hk (m : ℤ) (mp : ℤ) hmI hpI hunitI
  have hOne : (if k ∣ (mp : ℤ)-(m : ℤ) ∧
      Odd (((mp : ℤ)-(m : ℤ))/k) then (1 : ℂ) else 0)=1 := by
    simp [hdiv,hquot]
  have heq := hFour.symm.trans hOne
  refine ⟨hEven,?_⟩
  simpa only [Int.cast_natCast] using heq

/-- FULL FORWARD SOURCE BRIDGE: the two original positive Cauchy bilinear
equations with odd e and distinct odd rough m,m' DERIVE an actual signed
nonzero k, both original shifts, determinant, and the exact full Parity(2.6)
character projector value 1, whenever roughness makes Q=2|k| admissible.
No integrality, parity of k, unit modulus or Fourier gate is assumed. -/
theorem parity_original_bilinear_forward_fourier_mask_one434
    (e m mp n v vp : ℕ)
    (he : Odd e) (hm : Odd m) (hp : Odd mp)
    (h1 : m*n=e*v+2) (h2 : mp*n=e*vp+2)
    (hmneq : m ≠ mp) :
    ∃ k : ℤ, k ≠ 0 ∧
      ((mp : ℤ)-(m : ℤ))=(e : ℤ)*k ∧
      ((vp : ℤ)-(v : ℤ))=k*(n : ℤ) ∧
      ((m : ℤ)*(vp : ℤ)-(mp : ℤ)*(v : ℤ))=2*k ∧
      ∀ (W : ℝ), sourceD20Rough W m →
        ((2*k.natAbs : ℕ) : ℝ) ≤ W →
        Even k ∧
          (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
            parityShiftTwoMaskCoefficient434 k.natAbs chi *
            chi (mp : ZMod (2*k.natAbs)) *
            star (chi (m : ZMod (2*k.natAbs))))=1 := by
  obtain ⟨k,hk,hshift,hv,hdet⟩ :=
    parity_shift_two_original_forward_bilinear434 e m mp n v vp he h1 h2 hmneq
  refine ⟨k,hk,hshift,hv,hdet,?_⟩
  intro W hrough hq
  exact parity_original_bilinear_shift_mask_fourier_one434
    e m mp he hm hp k hk hshift W hrough hq
end Green64Analytic.Parity

end

end

/-! ## ShiftTwoActualBilinearMask -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- Native actual b629 Cauchy input: two nonzero fine coefficients and the
original odd-e bilinear equations produce a genuine nonzero signed k and
both determinant identities. If the derived k lies in the original
polynomial shift range, the full original Parity Fourier mask (2.6) is one
and k is even. Oddness, roughness and m-unit are DERIVED from actual
fine alpha; no extra SOURCE gate or E4.1 bound is assumed here. -/
theorem parity_eventually_actual_fine_bilinear_fourier_mask_one434
    (S beta gamma Ck : ℝ)
    (hS : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ (prime : Bool) (l u : ℕ), 2 ≤ l →
        Real.exp (beta*L) ≤ (l : ℝ) →
      ∀ (K : Finset ℕ) (m mp n e v vp : ℕ),
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) m ≠ 0 →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) mp ≠ 0 →
        Odd e → m*n=e*v+2 → mp*n=e*vp+2 → m ≠ mp →
      ∃ k : ℤ, k ≠ 0 ∧
        ((mp : ℤ)-(m : ℤ))=(e : ℤ)*k ∧
        ((vp : ℤ)-(v : ℤ))=k*(n : ℤ) ∧
        ((m : ℤ)*(vp : ℤ)-(mp : ℤ)*(v : ℤ))=2*k ∧
        ((k.natAbs : ℝ) ≤ L^Ck →
          Even k ∧
          (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
            parityShiftTwoMaskCoefficient434 k.natAbs chi *
            chi (mp : ZMod (2*k.natAbs)) *
            star (chi (m : ZMod (2*k.natAbs))))=1) := by
  filter_upwards [parity_actual_fine_K_restricted_rough434 S beta gamma hS hbeta hgamma,
    b638_eventually_poly_exp434 2 Ck (1/2) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hRough hPoly hL
  refine ⟨hL,?_⟩
  intro prime l u hl hlow K m mp n e v vp hm hmp he h1 h2 hmneq
  have hRoughM := hRough prime l u hl hlow K m hm
  have hRoughMp := hRough prime l u hl hlow K mp hmp
  have hW : (2 : ℝ) ≤ Real.exp (Real.sqrt L) :=
    parity_rough_cutoff_at_least_two434 L hL
  have hmOdd : Odd m := parity_original_rough_cofactor_odd434 _ m hW hRoughM
  have hmpOdd : Odd mp := parity_original_rough_cofactor_odd434 _ mp hW hRoughMp
  obtain ⟨k,hk,hshift,hv,hdet,hMask⟩ :=
    parity_original_bilinear_forward_fourier_mask_one434
      e m mp n v vp he hmOdd hmpOdd h1 h2 hmneq
  refine ⟨k,hk,hshift,hv,hdet,?_⟩
  intro hkBound
  have hPoly' : 2*L^Ck ≤ Real.exp (Real.sqrt L) := by
    simpa only [Real.sqrt_eq_rpow] using hPoly
  have hq : ((2*k.natAbs : ℕ) : ℝ) ≤ Real.exp (Real.sqrt L) := by
    calc
      _ = 2*(k.natAbs : ℝ) := by push_cast; ring
      _ ≤ 2*L^Ck := mul_le_mul_of_nonneg_left hkBound (by norm_num)
      _ ≤ Real.exp (Real.sqrt L) := hPoly'
  exact hMask (Real.exp (Real.sqrt L)) hRoughM hq
end Green64Analytic.Parity

end

end

/-! ## ActualAllocatedEOdd -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- All actual r=20 ordinary Q slot primes, with the ORIGINAL reserved
(jQ,slot) removed from the ordered allocation, are eventually >=4 and
prime. Uses the real dynamic Q depth and its admissibility gate. -/
theorem parity_eventually_actual_sorted_Q_slot_prime_floor434 :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (j : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length) (p : ℕ),
        p ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot j → p.Prime ∧ 4 ≤ p := by
  filter_upwards [source_original_literal_depth_properties_eventually 20 (by norm_num),
    eventually_ge_atTop (4 : ℝ)] with L hDepth hL
  refine ⟨hL,?_⟩
  intro band slot j p hp
  let d := sourceOriginalLiteralDepth 20 L
  let q := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L) band slot j).val.1
  have hq : p ∈ sourceOriginalQActualBands 20 d L q := by
    exact hp
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hscale : 20*Real.log L ≤ sourceOriginalQActualExponent 20 q.val*L :=
    b635_admissible_all_scales434 20 d q.val L (by norm_num) hLp.le hDepth.1 (by omega)
  have hs : sourceOriginalQActualExponent 20 q.val*L =
      sourceOriginalPGroupScale 20 L q.val :=
    source_original_Q_actual_scale_eq_P_scale 20 q.val L (by norm_num)
  have hRange := (source_original_Q_actual_prime_range 20 d L (by norm_num) q p hq).1
  have hlog : Real.exp (20*Real.log L) = L^20 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hLp] using (Real.exp_nat_mul (Real.log L) 20)
  have hLower : L^20 ≤ (p:ℝ) := by
    calc
      L^20 = Real.exp (20*Real.log L) := hlog.symm
      _ ≤ Real.exp (sourceOriginalQActualExponent 20 q.val*L) := Real.exp_le_exp.mpr hscale
      _ = Real.exp (sourceOriginalPGroupScale 20 L q.val) := by rw [hs]
      _ ≤ (p:ℝ) := hRange
  have hFour : (4:ℝ) ≤ L^20 := by
    calc
      (4:ℝ) ≤ L := hL
      _ = L*1 := by ring
      _ ≤ L*L^19 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL1) hLp.le
      _ = L^20 := by ring
  exact ⟨source_original_Q_actual_prime 20 d L q p hq,
    by exact_mod_cast (hFour.trans hLower)⟩

/-- The ORIGINAL true/false slot split of all nonreserved ordered Q primes.
A source full assignment provides a prime at EACH true original Q-band slot.
Delta true means the slot is assigned to e; the reserved prime is absent
from this index type, exactly as in Parity §4.2 and native OrderedQSkip. -/
def paritySourceOrderedAllocatedE434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (delta : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i}) : ℕ :=
  ∏ i : Fin n, if delta i then (p i).val else 1

/-- The complement is the original OrderedQSkip PRODUCT used in the
ported source residual fibre, with no new substitute prime tuple. -/
def paritySourceOrderedAllocatedV434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (delta : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i}) : ℕ :=
  orderedSkipProduct (fun i : {i : Fin n // ¬delta i = true} => p i.val)

/-- For ANY original ordered-slot assignment, an odd prime in EVERY Q
slot makes the genuine delta-selected e-product odd. This is independent
of Fourier phases or the number of source slots and does not discard
repeated prime factors. -/
theorem parity_source_ordered_allocated_e_odd434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (delta : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i})
    (hOdd : ∀ i, Odd (p i).val) :
    Odd (paritySourceOrderedAllocatedE434 delta p) := by
  unfold paritySourceOrderedAllocatedE434
  apply Finset.prod_induction (p := Odd)
  · intro a b ha hb
    exact ha.mul hb
  · decide
  · intro i hi
    by_cases h : delta i = true
    · simpa only [h, ite_true] using hOdd i
    · simpa [h] using (show Odd (1 : ℕ) by decide)

/-- Exact original QSkip allocation partition: the δ-selected e-product
times the *unchanged* `orderedSkipProduct` of the unselected Q slots is
the complete original nonreserved Q-prime product. No slot, factorial,
character or numerical loss is inserted at this source identity. -/
theorem parity_source_ordered_allocation_partition434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (delta : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i}) :
    paritySourceOrderedAllocatedE434 delta p *
      paritySourceOrderedAllocatedV434 delta p =
      ∏ i : Fin n, (p i).val := by
  have he : paritySourceOrderedAllocatedE434 delta p =
      ∏ i ∈ (Finset.univ.filter (fun i : Fin n => delta i = true)), (p i).val := by
    unfold paritySourceOrderedAllocatedE434
    rw [Finset.prod_filter]
  have hv : paritySourceOrderedAllocatedV434 delta p =
      ∏ i ∈ (Finset.univ.filter (fun i : Fin n => ¬delta i = true)), (p i).val := by
    unfold paritySourceOrderedAllocatedV434 orderedSkipProduct
    exact (Finset.prod_subtype
      (s := Finset.univ.filter (fun i : Fin n => ¬delta i = true))
      (p := fun i : Fin n => ¬delta i = true)
      (by intro i; simp)
      (fun i => (p i).val)).symm
  rw [he,hv]
  exact Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset (Fin n)) (fun i : Fin n => delta i = true)
    (fun i => (p i).val)

/-- The ACTUAL SOURCE sorted nonreserved Q-slot allocation (all 20 marks,
all original moving Q bands and actual ordered labels) has e odd,
positive and a unit modulo R=2 on EVERY branch δ, at every actual prime
tuple. Moreover e times the exact native OrderedQSkip residual product
is the whole nonreserved Q product, with no missing factors. -/
theorem parity_eventually_actual_Q_allocated_e_odd_unit434 :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (p : (i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length) →
          {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
            L band slot i}),
      let e := paritySourceOrderedAllocatedE434 delta p
      Odd e ∧ 0 < e ∧ IsUnit (e : ZMod 2) ∧
        e * paritySourceOrderedAllocatedV434 delta p =
          ∏ i, (p i).val := by
  filter_upwards [parity_eventually_actual_sorted_Q_slot_prime_floor434] with L hQ
  refine ⟨hQ.1,?_⟩
  intro band slot delta p
  dsimp only
  have hOdds : ∀ i, Odd (p i).val := by
    intro i
    have hp := hQ.2 band slot i (p i).val (p i).property
    exact hp.1.odd_of_ne_two (by omega)
  have hE := parity_source_ordered_allocated_e_odd434 delta p hOdds
  refine ⟨hE,hE.pos,?_,parity_source_ordered_allocation_partition434 delta p⟩
  exact (ZMod.isUnit_iff_coprime _ 2).mpr
    (Nat.coprime_two_right.mpr hE)
end Green64Analytic.Parity

end

end

/-! ## ActualAllocatedEBilinear -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 30000

/-- The actual ORIGINAL e supplied by EVERY ordered Q-slot allocation
branch, NOT an arbitrary odd surrogate, is admitted by the h=-2
bilinear/Cauchy signed-k and literal Fourier-mask construction.
The original e is the product of precisely the delta=true primes from
sourceActualSortedQ excluding its reserved (band,slot). At both endpoints
the actual K-restricted fine alpha coefficients are used. No additional
e parity, odd m/m', m-unit or initial integer k hypothesis is made.
This is not the still-missing full Fourier-weighted allocation a_e or
complete Type-II Cauchy-sum identity. -/
theorem parity_eventually_actual_Q_allocated_e_bilinear_mask434
    (S beta gamma Ck : ℝ)
    (hS : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (p : (i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length) →
          {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
            L band slot i}),
      let e := paritySourceOrderedAllocatedE434 delta p
      ∀ (prime : Bool) (l u : ℕ), 2 ≤ l →
        Real.exp (beta*L) ≤ (l : ℝ) →
      ∀ (K : Finset ℕ) (m mp n v vp : ℕ),
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) m ≠ 0 →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) mp ≠ 0 →
        m*n=e*v+2 → mp*n=e*vp+2 → m ≠ mp →
      ∃ k : ℤ, k ≠ 0 ∧
        ((mp : ℤ)-(m : ℤ))=(e : ℤ)*k ∧
        ((vp : ℤ)-(v : ℤ))=k*(n : ℤ) ∧
        ((m : ℤ)*(vp : ℤ)-(mp : ℤ)*(v : ℤ))=2*k ∧
        ((k.natAbs : ℝ) ≤ L^Ck →
          Even k ∧
          (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
            parityShiftTwoMaskCoefficient434 k.natAbs chi *
            chi (mp : ZMod (2*k.natAbs)) *
            star (chi (m : ZMod (2*k.natAbs))))=1) := by
  filter_upwards [parity_eventually_actual_Q_allocated_e_odd_unit434,
    parity_eventually_actual_fine_bilinear_fourier_mask_one434
      S beta gamma Ck hS hbeta hgamma] with L hE hB
  refine ⟨hE.1,?_⟩
  intro band slot delta p
  have hOdd : Odd (paritySourceOrderedAllocatedE434 delta p) :=
    (hE.2 band slot delta p).1
  dsimp only
  intro prime l u hl hlow K m mp n v vp hm hmp h1 h2 hneq
  exact hB.2 prime l u hl hlow K m mp n
    (paritySourceOrderedAllocatedE434 delta p) v vp
    hm hmp hOdd h1 h2 hneq
end Green64Analytic.Parity

end

end

/-! ## ActualAllocatedEFibre -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 30000

/-- Actual ORIGINAL ordered slot-allocation coefficient fibre indexed by
the SELECTED product e. It ranges over all true/false choices delta and
all full Q prime tuples, and retains an arbitrary complex branch weight.
The endpoint map is the true selected Q product, not an assumed odd e.
The native SOURCE endpoint summation is literally sourceEndpointFibre. -/
def paritySourceOrderedAllocatedEFibre434
    {n : ℕ} (Q : Fin n → Finset ℕ)
    (weight : (Fin n → Bool) → ((i : Fin n) → {q : ℕ // q ∈ Q i}) → ℂ)
    (e : ℕ) : ℂ :=
  sourceEndpointFibre
    (Finset.univ : Finset ((Fin n → Bool) × ((i : Fin n) → {q : ℕ // q ∈ Q i})))
    (fun x => paritySourceOrderedAllocatedE434 x.1 x.2)
    (fun x => weight x.1 x.2) e

/-- ANY signed/Fourier-smoothed original allocation branch weights give
exactly ZERO at an even e, provided the true Q-band prime inputs are odd.
No positivity/noncancellation of weights, phase estimate or bound on e is
assumed: even e has literally NO contributing source branch. -/
theorem parity_source_ordered_allocated_e_fibre_even_zero434
    {n : ℕ} (Q : Fin n → Finset ℕ)
    (hOdd : ∀ i q, q ∈ Q i → Odd q)
    (weight : (Fin n → Bool) → ((i : Fin n) → {q : ℕ // q ∈ Q i}) → ℂ)
    (e : ℕ) (he : Even e) :
    paritySourceOrderedAllocatedEFibre434 Q weight e = 0 := by
  unfold paritySourceOrderedAllocatedEFibre434 sourceEndpointFibre
  apply Finset.sum_eq_zero
  intro x hx
  have hMatch : paritySourceOrderedAllocatedE434 x.1 x.2 = e :=
    (Finset.mem_filter.mp hx).2
  have hOddE : Odd (paritySourceOrderedAllocatedE434 x.1 x.2) :=
    parity_source_ordered_allocated_e_odd434 x.1 x.2
      (fun i => hOdd i (x.2 i).val (x.2 i).property)
  have hO : Odd e := hMatch ▸ hOddE
  have hNot : ¬Even e := Nat.not_even_iff_odd.mpr hO
  exact (hNot he).elim

/-- Exact actual r20 dynamic-depth e-allocation support: for EVERY
reserved Q slot, actual ordered remaining Q bands, all delta branches
and every supplied complex (including Fourier) branch weight, the
literal selected-product sourceEndpointFibre vanishes at every even e.
This is a genuine support theorem; identifying the historical weighted
a_e with this explicit coefficient requires a separate SOURCE equality. -/
theorem parity_eventually_actual_Q_allocated_e_fibre_even_zero434 :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (weight :
          (Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → Bool) →
          ((i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length) →
            {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
              L band slot i}) → ℂ)
        (e : ℕ), Even e →
      paritySourceOrderedAllocatedEFibre434
        (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot)
        weight e = 0 := by
  filter_upwards [parity_eventually_actual_sorted_Q_slot_prime_floor434] with L hQ
  refine ⟨hQ.1,?_⟩
  intro band slot weight e he
  have hOdd : ∀ i q,
      q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot i →
      Odd q := by
    intro i q hq
    have hp := hQ.2 band slot i q hq
    exact hp.1.odd_of_ne_two (by omega)
  exact parity_source_ordered_allocated_e_fibre_even_zero434
    (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot)
    hOdd weight e he

/-- Exact finite support of the ORIGINAL delta-selected Q-prime product e.
It contains precisely e-values from all actual full prime tuples and
branch choices; no artificial interval, squarefree restriction, or source
weight filter is substituted for the true e fibres. -/
def paritySourceOrderedAllocatedESupport434
    {n : ℕ} (Q : Fin n → Finset ℕ) : Finset ℕ :=
  (Finset.univ : Finset ((Fin n → Bool) × ((i : Fin n) → {q : ℕ // q ∈ Q i}))).image
    (fun x => paritySourceOrderedAllocatedE434 x.1 x.2)

/-- Exact finite regrouping of ALL original ordered Q-slot/branch tuples
by their selected product e. No source phase, factorial, Fourier weight or
sign is changed: the input weight is arbitrary and is copied byte-for-byte
into the genuine native sourceEndpointFibre. -/
theorem parity_source_ordered_e_fibre_reindex434
    {n : ℕ} (Q : Fin n → Finset ℕ)
    (weight : (Fin n → Bool) → ((i : Fin n) → {q : ℕ // q ∈ Q i}) → ℂ) :
    (∑ x : ((Fin n → Bool) × ((i : Fin n) → {q : ℕ // q ∈ Q i})),
      weight x.1 x.2) =
      ∑ e ∈ paritySourceOrderedAllocatedESupport434 Q,
        paritySourceOrderedAllocatedEFibre434 Q weight e := by
  unfold paritySourceOrderedAllocatedESupport434
  let S : Finset ((Fin n → Bool) × ((i : Fin n) → {q : ℕ // q ∈ Q i})) := Finset.univ
  let E : ((Fin n → Bool) × ((i : Fin n) → {q : ℕ // q ∈ Q i})) → ℕ :=
    fun x => paritySourceOrderedAllocatedE434 x.1 x.2
  have hReindex := Finset.sum_image'
    (s := S) (g := E) (f := fun e => paritySourceOrderedAllocatedEFibre434 Q weight e)
    (fun x => weight x.1 x.2) (by intro x hx; rfl)
  simpa only [S,E,paritySourceOrderedAllocatedEFibre434,sourceEndpointFibre] using hReindex.symm

/-- Every e in the *actual source support*, not merely every individual
summand, is odd under the original odd Q-prime hypothesis. -/
theorem parity_source_ordered_e_support_odd434
    {n : ℕ} (Q : Fin n → Finset ℕ)
    (hOdd : ∀ i q, q ∈ Q i → Odd q)
    (e : ℕ) (he : e ∈ paritySourceOrderedAllocatedESupport434 Q) : Odd e := by
  rcases Finset.mem_image.mp he with ⟨x,hx,heq⟩
  have hValue := parity_source_ordered_allocated_e_odd434 x.1 x.2
    (fun i => hOdd i (x.2 i).val (x.2 i).property)
  exact heq ▸ hValue
end Green64Analytic.Parity

end

end

/-! ## ActualAllocatedEPWeight -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 30000

/-- Every prime dividing the original delta-selected e comes from the
actual nonreserved Q bands and NONE from ANY original P group. This is
proved from literal sourceOriginalQActualBands/sourceOriginalPAllActualBands
disjointness, not an assumed Q/P-coprimality input. -/
theorem parity_actual_Q_allocated_e_no_P_prime434
    (L : ℝ) (hL : 0 < L)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → Bool)
    (p : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length) →
      {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
        L band slot i})
    (g : sourceOriginalPAllGroupType 20 L) (q : ℕ)
    (hq : q ∈ sourceOriginalPAllActualBands 20 L g) :
    ¬ q ∣ paritySourceOrderedAllocatedE434 delta p := by
  let d := sourceOriginalLiteralDepth 20 L
  have hqPrime := source_original_P_all_actual_band_prime 20 L g q hq
  unfold paritySourceOrderedAllocatedE434
  apply source_original_prime_not_dvd_finset_product
    q hqPrime (fun i => if delta i then (p i).val else 1) Finset.univ
  intro i hi
  by_cases hsel : delta i = true
  · simp only [hsel, ite_true]
    let j := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
      band slot i).val.1
    have hpq : (p i).val ∈ sourceOriginalQActualBands 20 d L j := (p i).property
    have hpPrime := source_original_Q_actual_prime 20 d L j (p i).val hpq
    intro hdiv
    have heq : q = (p i).val :=
      (Nat.prime_dvd_prime_iff_eq hqPrime hpPrime).mp hdiv
    exact source_original_Q_actual_all_P_disjoint 20 d L (by norm_num)
      hL j g q (heq ▸ hpq) hq
  · simpa [hsel] using hqPrime.not_dvd_one

/-- No selected slot prime is zero; the actual e product is a positive
ordinary integer before any asymptotic e-range or allocation weight. -/
theorem parity_actual_Q_allocated_e_ne_zero434
    (L : ℝ)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → Bool)
    (p : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length) →
      {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
        L band slot i}) :
    paritySourceOrderedAllocatedE434 delta p ≠ 0 := by
  unfold paritySourceOrderedAllocatedE434
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  by_cases hsel : delta i = true
  · simp only [hsel, ite_true]
    let d := sourceOriginalLiteralDepth 20 L
    let j := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L)
      band slot i).val.1
    have hp : (p i).val ∈ sourceOriginalQActualBands 20 d L j := (p i).property
    exact (source_original_Q_actual_prime 20 d L j (p i).val hp).ne_zero
  · simp only [hsel, ite_false]
    norm_num

/-- Exact original Parity (4.9) P-geometry invariance for the actual
Q-allocation e (every delta, every actual ordered nonreserved Q tuple).
The signed original P-parity counts prime multiplicities and the W1
marks count distinct group primes, both retained literally. Multiplying
by e changes NEITHER W1 NOR P-parity nor either groupSign. -/
theorem parity_actual_Q_allocated_e_P_weight_parity_invariant434
    (L : ℝ) (hL : 0 < L)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → Bool)
    (p : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length) →
      {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
        L band slot i})
    (R : ℕ) (hR : R ≠ 0) :
    let P := sourceOriginalPAllActualBands 20 L
    let e := paritySourceOrderedAllocatedE434 delta p
    sourceOriginalW1 P (e*R) = sourceOriginalW1 P R ∧
      sourceOriginalPParityExponent (Finset.univ.biUnion P) (e*R) =
        sourceOriginalPParityExponent (Finset.univ.biUnion P) R ∧
      ∀ (tw : Bool), groupSign P tw (e*R) = groupSign P tw R := by
  dsimp only
  let P := sourceOriginalPAllActualBands 20 L
  let e := paritySourceOrderedAllocatedE434 delta p
  have heNZ : e ≠ 0 := parity_actual_Q_allocated_e_ne_zero434 L band slot delta p
  have hPrime : ∀ g q, q ∈ P g → q.Prime := by
    intro g q hq
    exact source_original_P_all_actual_band_prime 20 L g q hq
  have hNoP : ∀ g q, q ∈ P g → ¬q ∣ e := by
    intro g q hq
    exact parity_actual_Q_allocated_e_no_P_prime434 L hL band slot delta p g q hq
  have hNoAll : ∀ q ∈ Finset.univ.biUnion P, ¬q ∣ e := by
    intro q hq
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hq
    exact hNoP g q hpg
  have hW : sourceOriginalW1 P (e*R)=sourceOriginalW1 P R :=
    source_original_W1_nonP_mul P e R hPrime hNoP
  have hParity :
      sourceOriginalPParityExponent (Finset.univ.biUnion P) (e*R) =
        sourceOriginalPParityExponent (Finset.univ.biUnion P) R :=
    source_original_P_multiplicity_nonP_mul
      (Finset.univ.biUnion P) e R heNZ hR hNoAll
  refine ⟨hW,hParity,?_⟩
  intro tw
  cases tw with
  | false => simp [groupSign]
  | true =>
      change (-1 : ℝ) ^ sourceOriginalPParityExponent
        (Finset.univ.biUnion P) (e*R) =
          (-1 : ℝ) ^ sourceOriginalPParityExponent (Finset.univ.biUnion P) R
      rw [hParity]

/-- In particular the selected original e has E(e)=+1 EXACTLY;
the P-parity exponent of e is zero, with no modulo-2 approximation. -/
theorem parity_actual_Q_allocated_e_P_parity_zero434
    (L : ℝ) (hL : 0 < L)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → Bool)
    (p : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length) →
      {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
        L band slot i}) :
    sourceOriginalPParityExponent
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
      (paritySourceOrderedAllocatedE434 delta p) = 0 := by
  have h := (parity_actual_Q_allocated_e_P_weight_parity_invariant434
    L hL band slot delta p 1 (by norm_num)).2.1
  have hOne : sourceOriginalPParityExponent
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) 1 = 0 := by
    simp [sourceOriginalPParityExponent]
  simpa only [mul_one,hOne] using h
end Green64Analytic.Parity

end

end

/-! ## ActualAllocatedESupport -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 30000

/-- A NONZERO original e-coefficient fibre (whatever the original complex
Fourier/smooth branch weights are) requires at least one ACTUAL full
prime-slot assignment with that exact selected product e. No surrogate
support bound or absence of phase cancellation is assumed. -/
theorem parity_source_ordered_e_fibre_nonzero_mem_support434
    {n : ℕ} (Q : Fin n → Finset ℕ)
    (weight : (Fin n → Bool) → ((i : Fin n) → {q : ℕ // q ∈ Q i}) → ℂ)
    (e : ℕ)
    (hNonzero : paritySourceOrderedAllocatedEFibre434 Q weight e ≠ 0) :
    e ∈ paritySourceOrderedAllocatedESupport434 Q := by
  by_contra hNot
  have hEmpty : (Finset.univ : Finset
      ((Fin n → Bool) × ((i : Fin n) → {q : ℕ // q ∈ Q i}))).filter
      (fun x => paritySourceOrderedAllocatedE434 x.1 x.2 = e) = ∅ := by
    ext x
    constructor
    · intro hx
      have hEq := (Finset.mem_filter.mp hx).2
      exact False.elim (hNot (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,hEq⟩))
    · simp
  have hZero : paritySourceOrderedAllocatedEFibre434 Q weight e = 0 := by
    unfold paritySourceOrderedAllocatedEFibre434 sourceEndpointFibre
    rw [hEmpty]
    simp
  exact hNonzero hZero

/-- Q-allocated e in the literal source IMAGE leaves the original P-mark
weight, multiplicity-counted parity and common epsilon twist unchanged,
for all source R>0. No branch weight or e parity is an added hypothesis. -/
theorem parity_actual_Q_e_support_P_weight_invariant434
    (L : ℝ) (hL : 0 < L)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (e : ℕ)
    (hSupport : e ∈ paritySourceOrderedAllocatedESupport434
      (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot))
    (R : ℕ) (hR : R ≠ 0) :
    let P := sourceOriginalPAllActualBands 20 L
    sourceOriginalW1 P (e*R) = sourceOriginalW1 P R ∧
      sourceOriginalPParityExponent (Finset.univ.biUnion P) (e*R) =
        sourceOriginalPParityExponent (Finset.univ.biUnion P) R ∧
      ∀ (tw : Bool), groupSign P tw (e*R) = groupSign P tw R := by
  rcases Finset.mem_image.mp hSupport with ⟨x,hx,hE⟩
  have hW := parity_actual_Q_allocated_e_P_weight_parity_invariant434
    L hL band slot x.1 x.2 R hR
  simpa only [hE] using hW

/-- The complete actual moving-Q allocated-e FIBRE satisfies ALL original
Parity (4.9) arithmetic support gates ON ITS NONZERO COEFFICIENT, with
arbitrary complex branch weights (including normalized Fourier weights).
This requires only identification of the historical a_e with the literal
SOURCE fibre; no amplitude positivity, character bound or cancellation is
assumed or used here. -/
theorem parity_eventually_actual_e_fibre_nonzero_original_support434 :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (weight :
          (Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → Bool) →
          ((i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length) →
            {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
              L band slot i}) → ℂ)
        (e : ℕ),
      paritySourceOrderedAllocatedEFibre434
        (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot)
        weight e ≠ 0 →
      let P := sourceOriginalPAllActualBands 20 L
      Odd e ∧ 0 < e ∧ IsUnit (e : ZMod 2) ∧
      sourceOriginalPParityExponent (Finset.univ.biUnion P) e = 0 ∧
      ∀ (R : ℕ), R ≠ 0 →
        sourceOriginalW1 P (e*R) = sourceOriginalW1 P R ∧
        sourceOriginalPParityExponent (Finset.univ.biUnion P) (e*R) =
          sourceOriginalPParityExponent (Finset.univ.biUnion P) R ∧
        ∀ tw : Bool, groupSign P tw (e*R) = groupSign P tw R := by
  filter_upwards [parity_eventually_actual_sorted_Q_slot_prime_floor434] with L hQ
  refine ⟨hQ.1,?_⟩
  intro band slot weight e hF
  dsimp only
  have hSupport : e ∈ paritySourceOrderedAllocatedESupport434
      (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot) :=
    parity_source_ordered_e_fibre_nonzero_mem_support434 _ weight e hF
  have hOddQ : ∀ i q,
      q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot i →
      Odd q := by
    intro i q hq
    have h := hQ.2 band slot i q hq
    exact h.1.odd_of_ne_two (by omega)
  have heOdd : Odd e :=
    parity_source_ordered_e_support_odd434 _ hOddQ e hSupport
  have hLp : 0 < L := by linarith [hQ.1]
  have hP0 : sourceOriginalPParityExponent
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) e = 0 := by
    have h := (parity_actual_Q_e_support_P_weight_invariant434
      L hLp band slot e hSupport 1 (by norm_num)).2.1
    have hOne : sourceOriginalPParityExponent
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) 1 = 0 := by
      simp [sourceOriginalPParityExponent]
    simpa only [mul_one,hOne] using h
  refine ⟨heOdd,heOdd.pos,
    (ZMod.isUnit_iff_coprime _ 2).mpr (Nat.coprime_two_right.mpr heOdd),
    hP0,?_⟩
  intro R hR
  exact parity_actual_Q_e_support_P_weight_invariant434 L hLp band slot e
    hSupport R hR
end Green64Analytic.Parity

end

end

/-! ## ActualAllocatedEFibreBilinear -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 30000

/-- Full original weighted e-coefficient SOURCE-to-Cauchy gate: a NONZERO
exact native sourceEndpointFibre from all original sorted Q slots and
all delta branches, with arbitrary complex allocation/Fourier weights,
automatically has odd positive e, e coprime 2, E(e)=1 and W1(eR)=W1(R).
Using the ACTUAL b629 K-restricted rough m,m' in both original bilinear
equations, it then produces the signed k, shifts, determinant and exact
Parity(2.6) Fourier mask=1. No separate Odd e, rough m or unit(m modQ)
premise is passed. The sole unresolved source interface is the equality
of Parity's historical a_e with this explicitly defined weighted Q-fibre,
plus full Cauchy amplitude reindex and analytic TypeII savings. -/
theorem parity_eventually_actual_e_fibre_bilinear_mask434
    (S beta gamma Ck : ℝ)
    (hS : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (weight :
          (Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → Bool) →
          ((i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length) →
            {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
              L band slot i}) → ℂ)
        (e : ℕ),
      paritySourceOrderedAllocatedEFibre434
        (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot)
        weight e ≠ 0 →
      let P := sourceOriginalPAllActualBands 20 L
      Odd e ∧ 0 < e ∧ IsUnit (e : ZMod 2) ∧
      sourceOriginalPParityExponent (Finset.univ.biUnion P) e = 0 ∧
      (∀ (R : ℕ), R ≠ 0 → sourceOriginalW1 P (e*R) = sourceOriginalW1 P R) ∧
      ∀ (prime : Bool) (l u : ℕ), 2 ≤ l →
        Real.exp (beta*L) ≤ (l : ℝ) →
      ∀ (K : Finset ℕ) (m mp n v vp : ℕ),
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) m ≠ 0 →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) mp ≠ 0 →
        m*n=e*v+2 → mp*n=e*vp+2 → m ≠ mp →
      ∃ k : ℤ, k ≠ 0 ∧
        ((mp : ℤ)-(m : ℤ))=(e : ℤ)*k ∧
        ((vp : ℤ)-(v : ℤ))=k*(n : ℤ) ∧
        ((m : ℤ)*(vp : ℤ)-(mp : ℤ)*(v : ℤ))=2*k ∧
        ((k.natAbs : ℝ) ≤ L^Ck →
          Even k ∧
          (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
            parityShiftTwoMaskCoefficient434 k.natAbs chi *
            chi (mp : ZMod (2*k.natAbs)) *
            star (chi (m : ZMod (2*k.natAbs))))=1) := by
  filter_upwards [parity_eventually_actual_e_fibre_nonzero_original_support434,
    parity_eventually_actual_fine_bilinear_fourier_mask_one434
      S beta gamma Ck hS hbeta hgamma] with L hSource hB
  refine ⟨hSource.1,?_⟩
  intro band slot weight e hF
  have hS0 := hSource.2 band slot weight e hF
  dsimp only at hS0
  refine ⟨hS0.1,hS0.2.1,hS0.2.2.1,hS0.2.2.2.1,?_,?_⟩
  · intro R hR
    exact (hS0.2.2.2.2 R hR).1
  · intro prime l u hl hlow K m mp n v vp hm hmp h1 h2 hneq
    exact hB.2 prime l u hl hlow K m mp n e v vp
      hm hmp hS0.1 h1 h2 hneq
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearKRange -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 28000

/-- EXACT Parity (4.13) shift-range arithmetic: original m,m' lie in
[U,2U] and genuine positive allocated e satisfies e>=U*L^(-D).
Then any signed k with m'-m=e*k automatically obeys |k|<=L^D.
No restriction on sign of k, no informal ~, and no analytic character
saving is assumed. The genuine allocation lower bound (4.5) remains a
separate SOURCE task and is explicitly an input to this lemma. -/
theorem parity_original_signed_k_bound_of_e_lower434
    (L U D : ℝ) (hL : 0 < L) (hU : 0 < U)
    (e m mp : ℕ)
    (he : U*L^(-D) ≤ (e : ℝ))
    (hmLow : U ≤ (m : ℝ)) (hmHi : (m : ℝ) ≤ 2*U)
    (hmpLow : U ≤ (mp : ℝ)) (hmpHi : (mp : ℝ) ≤ 2*U)
    (k : ℤ) (hshift : (mp : ℤ)-(m : ℤ)=(e : ℤ)*k) :
    (k.natAbs : ℝ) ≤ L^D := by
  have hDiff : |(mp : ℝ)-(m : ℝ)| ≤ U :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  have hShiftR : (mp : ℝ)-(m : ℝ)=(e : ℝ)*(k : ℝ) := by
    exact_mod_cast hshift
  have hK : |(k : ℝ)|=(k.natAbs : ℝ) := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  have hProd : (e : ℝ)*(k.natAbs : ℝ) ≤ U := by
    calc
      (e : ℝ)*(k.natAbs : ℝ) = |(e : ℝ)*(k : ℝ)| := by
        rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg e),hK]
      _ = |(mp : ℝ)-(m : ℝ)| := by rw [hShiftR]
      _ ≤ U := hDiff
  have hKn : 0 ≤ (k.natAbs : ℝ) := Nat.cast_nonneg _
  have hLowProd : (U*L^(-D))*(k.natAbs : ℝ) ≤ U :=
    (mul_le_mul_of_nonneg_right he hKn).trans hProd
  have hR : L^(-D)*(k.natAbs : ℝ) ≤ 1 := by
    nlinarith [hLowProd]
  have hInv : L^D*L^(-D)=1 := by
    rw [← Real.rpow_add hL]
    simp
  calc
    (k.natAbs : ℝ) = (L^D*L^(-D))*(k.natAbs : ℝ) := by rw [hInv,one_mul]
    _ = L^D*(L^(-D)*(k.natAbs : ℝ)) := by ring
    _ ≤ L^D*1 := mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hL.le _)
    _ = L^D := mul_one _
end Green64Analytic.Parity

end

end

/-! ## ActualAllocatedEFibreKBound -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 30000

/-- ACTUAL Q-slot allocated-e weighted fibre, original bilinear Cauchy
arithmetic, and original Parity (4.13) signed-k polynomial RANGE together.
The lower support e>=U*L^-D is explicit: closing the original smooth
allocation theorem Parity (4.5) is still independent analytical work.
For every genuine Q-support nonzero fibre, b629 rough alpha endpoints,
original h=-2 e,n,m,m',v,v' equations, and m,m' in [U,2U], the EXACT
character projector equals 1 without a residual k-range guard.
No inferred original a_e identification, E4.1 or TypeII savings claimed. -/
theorem parity_eventually_actual_e_fibre_bilinear_unconditional_mask_of_e_range434
    (S beta gamma D : ℝ)
    (hS : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (weight :
          (Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → Bool) →
          ((i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length) →
            {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
              L band slot i}) → ℂ)
        (e : ℕ),
      paritySourceOrderedAllocatedEFibre434
        (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot)
        weight e ≠ 0 →
      ∀ U : ℝ, 0 < U → U*L^(-D) ≤ (e : ℝ) →
      ∀ (prime : Bool) (l u : ℕ), 2 ≤ l →
        Real.exp (beta*L) ≤ (l : ℝ) →
      ∀ (K : Finset ℕ) (m mp n v vp : ℕ),
        U ≤ (m:ℝ) → (m:ℝ) ≤ 2*U →
        U ≤ (mp:ℝ) → (mp:ℝ) ≤ 2*U →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) m ≠ 0 →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) mp ≠ 0 →
        m*n=e*v+2 → mp*n=e*vp+2 → m ≠ mp →
      ∃ k : ℤ, k ≠ 0 ∧
        ((mp : ℤ)-(m : ℤ))=(e : ℤ)*k ∧
        ((vp : ℤ)-(v : ℤ))=k*(n : ℤ) ∧
        ((m : ℤ)*(vp : ℤ)-(mp : ℤ)*(v : ℤ))=2*k ∧
        (k.natAbs : ℝ) ≤ L^D ∧
        Even k ∧
        (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
          chi (mp : ZMod (2*k.natAbs)) *
          star (chi (m : ZMod (2*k.natAbs))))=1 := by
  filter_upwards [parity_eventually_actual_e_fibre_bilinear_mask434
    S beta gamma D hS hbeta hgamma] with L hF
  refine ⟨hF.1,?_⟩
  intro band slot weight e hSupport U hU he prime l u hl hlow
    K m mp n v vp hmLow hmHi hmpLow hmpHi hm hmp h1 h2 hneq
  have hBil := (hF.2 band slot weight e hSupport).2.2.2.2.2
    prime l u hl hlow K m mp n v vp hm hmp h1 h2 hneq
  rcases hBil with ⟨k,hk,hShift,hV,hDet,hFourier⟩
  have hkBound : (k.natAbs : ℝ) ≤ L^D :=
    parity_original_signed_k_bound_of_e_lower434 L U D
      (by linarith [hF.1]) hU e m mp he hmLow hmHi hmpLow hmpHi k hShift
  rcases hFourier hkBound with ⟨hkEven,hMask⟩
  exact ⟨k,hk,hShift,hV,hDet,hkBound,hkEven,hMask⟩
end Green64Analytic.Parity

end

end

/-! ## SmoothOriginalAllocationUpper -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

/-- Original Parity 4.2 smooth allocation's remaining logarithmic capacity
before ordered Q slot i, on the LITERAL δ-labelled prime assignment. -/
def parityOriginalQAllocationResidual434
    {n : ℕ} (E : ℝ) (delta : Fin n → Bool) (p : Fin n → ℕ)
    (i : Fin n) : ℝ :=
  Real.log E - ∑ j ∈ (Finset.univ.filter (fun j : Fin n => j < i)),
    if delta j then Real.log (p j : ℝ) else 0

/-- The EXACT ported SOURCE smooth Fourier gate f_delta, evaluated at
Parity's original (R_i - log p_i)/s_{j(i)}. We use the native source
`sourceBufferedGateReal`, not a newly invented cutoff. -/
def parityOriginalQAllocationBranchWeight434
    {n : ℕ} (r : ℕ) (E : ℝ)
    (scales : Fin n → ℝ) (delta : Fin n → Bool)
    (p : Fin n → ℕ) : ℝ :=
  ∏ i : Fin n, sourceBufferedGateReal r (delta i)
    ((parityOriginalQAllocationResidual434 E delta p i - Real.log (p i : ℝ)) / scales i)

/-- Exact logarithm of the original delta-selected e-product, including
prime multiplicities and the absence of the reserved slot. -/
theorem parity_original_Q_allocation_log_selected_e434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (delta : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i})
    (hPos : ∀ i, 0 < (p i).val) :
    Real.log (paritySourceOrderedAllocatedE434 delta p : ℝ) =
      ∑ i ∈ (Finset.univ.filter (fun i : Fin n => delta i = true)),
        Real.log ((p i).val : ℝ) := by
  have he : paritySourceOrderedAllocatedE434 delta p =
      ∏ i ∈ (Finset.univ.filter (fun i : Fin n => delta i = true)), (p i).val := by
    unfold paritySourceOrderedAllocatedE434
    rw [Finset.prod_filter]
  rw [he]
  push_cast
  rw [Real.log_prod]
  intro i hi
  exact_mod_cast (Nat.ne_of_gt (hPos i))

/-- The ported smooth positive f1 gate FORBIDS overdrawing remaining
logarithmic capacity: every truly selected ordered source Q slot has
R_i > log p_i. This is a mathematical consequence of the exact zero
support of `Real.smoothTransition`, not a separate assumption on δ. -/
theorem parity_original_Q_smooth_positive_branch_slot_budget434
    {n : ℕ} (r : ℕ) (E : ℝ) (scales : Fin n → ℝ)
    (delta : Fin n → Bool) (p : Fin n → ℕ)
    (hScales : ∀ i, 0 < scales i)
    (hWeight : parityOriginalQAllocationBranchWeight434 r E scales delta p ≠ 0)
    (i : Fin n) (hSelected : delta i = true) :
    Real.log (p i : ℝ) < parityOriginalQAllocationResidual434 E delta p i := by
  have hNZ : sourceBufferedGateReal r (delta i)
      ((parityOriginalQAllocationResidual434 E delta p i - Real.log (p i : ℝ)) /
        scales i) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hWeight) i (Finset.mem_univ i)
  rw [hSelected] at hNZ
  have hGammaNZ : Real.smoothTransition
      ((parityOriginalQAllocationResidual434 E delta p i - Real.log (p i : ℝ)) /
        scales i) ≠ 0 := by
    intro hzero
    apply hNZ
    simp [sourceBufferedGateReal,hzero]
  have hPos : 0 <
      (parityOriginalQAllocationResidual434 E delta p i - Real.log (p i : ℝ)) /
        scales i := by
    by_contra hNot
    exact hGammaNZ (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hNot))
  have hNum : 0 < parityOriginalQAllocationResidual434 E delta p i -
      Real.log (p i : ℝ) := (div_pos_iff_of_pos_right (hScales i)).mp hPos
  linarith

/-- Original Parity (4.4) upper residual budget: take the LAST Q slot
positively allocated to e. All selected previous slot logarithms form
precisely its original residual R_i. The native smooth f1 support
forces total selected log-product below log ℰ. -/
theorem parity_original_Q_smooth_positive_branch_log_budget434
    {n : ℕ} (r : ℕ) (E : ℝ)
    (scales : Fin n → ℝ) (delta : Fin n → Bool) (p : Fin n → ℕ)
    (hE : 1 ≤ E) (hScales : ∀ i, 0 < scales i)
    (hWeight : parityOriginalQAllocationBranchWeight434 r E scales delta p ≠ 0) :
    (∑ i ∈ (Finset.univ.filter (fun i : Fin n => delta i = true)),
      Real.log (p i : ℝ)) ≤ Real.log E := by
  let B : Finset (Fin n) := Finset.univ.filter (fun i => delta i = true)
  rcases B.eq_empty_or_nonempty with hEmpty | hNonempty
  · change (∑ i ∈ B, Real.log (p i : ℝ)) ≤ Real.log E
    rw [hEmpty]
    simpa using Real.log_nonneg hE
  · let j := B.max' hNonempty
    have hj : j ∈ B := Finset.max'_mem B hNonempty
    have hjSelect : delta j = true := (Finset.mem_filter.mp hj).2
    have hErase : B.erase j =
        (Finset.univ.filter (fun i : Fin n => i < j)).filter (fun i => delta i = true) := by
      ext i
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨hne,hi⟩
        have hle : i ≤ j := Finset.le_max' B i hi
        exact ⟨lt_of_le_of_ne hle hne, (Finset.mem_filter.mp hi).2⟩
      · intro ⟨hlt,hi⟩
        exact ⟨ne_of_lt hlt, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    have hPrefix :
        (∑ i ∈ B.erase j, Real.log (p i : ℝ)) =
          ∑ i ∈ (Finset.univ.filter (fun i : Fin n => i < j)),
            if delta i then Real.log (p i : ℝ) else 0 := by
      rw [hErase, Finset.sum_filter]
    have hSlot := parity_original_Q_smooth_positive_branch_slot_budget434
      r E scales delta p hScales hWeight j hjSelect
    unfold parityOriginalQAllocationResidual434 at hSlot
    have hSum := Finset.sum_erase_add B (fun i => Real.log (p i : ℝ)) hj
    rw [hPrefix] at hSum
    change (∑ i ∈ B, Real.log (p i : ℝ)) ≤ Real.log E
    linarith

/-- FIRST half of Parity (4.5) on a true positive SOURCE smooth branch:
1<=ℰ and all slot prime p>0 imply EXACT original assigned e<=ℰ.
This does not assume upper e range as an added allocation hypothesis.
The lower ℰ L^-C_s <= e requires the independent terminal residual bound. -/
theorem parity_original_Q_smooth_positive_branch_e_le_capacity434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (r : ℕ) (E : ℝ) (scales : Fin n → ℝ)
    (delta : Fin n → Bool)
    (p : (i : Fin n) → {q : ℕ // q ∈ Q i})
    (hE : 1 ≤ E) (hScales : ∀ i, 0 < scales i)
    (hP : ∀ i, 0 < (p i).val)
    (hWeight : parityOriginalQAllocationBranchWeight434 r E scales delta
      (fun i => (p i).val) ≠ 0) :
    (paritySourceOrderedAllocatedE434 delta p : ℝ) ≤ E := by
  have hLog : Real.log (paritySourceOrderedAllocatedE434 delta p : ℝ) =
      ∑ i ∈ (Finset.univ.filter (fun i : Fin n => delta i = true)),
        Real.log ((p i).val : ℝ) :=
    parity_original_Q_allocation_log_selected_e434 delta p hP
  have hLogLe : Real.log (paritySourceOrderedAllocatedE434 delta p : ℝ) ≤
      Real.log E := by
    rw [hLog]
    exact parity_original_Q_smooth_positive_branch_log_budget434
      r E scales delta (fun i => (p i).val) hE hScales hWeight
  have hPositive : 0 < paritySourceOrderedAllocatedE434 delta p := by
    unfold paritySourceOrderedAllocatedE434
    apply Finset.prod_pos
    intro i hi
    by_cases hs : delta i = true
    · simpa [hs] using hP i
    · simp [hs]
  have hEPos : 0 < E := lt_of_lt_of_le (by norm_num) hE
  have hExp := Real.exp_le_exp.mpr hLogLe
  rwa [Real.exp_log (Nat.cast_pos.mpr hPositive), Real.exp_log hEPos] at hExp
end Green64Analytic.Parity

end

end

/-! ## ActualSmoothAllocatedEUpper -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 30000

/-- Every original sourceActualSortedFrequencyScales for the full r=20
moving Q family has strictly positive original dyadic scale, including
all 20*depth-1 positions and the nonreserved original slot labelling. -/
theorem parity_actual_sorted_Q_allocation_scales_positive434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (b : Fin (d+1)) (slot : Fin 20) :
    ∀ i, 0 < sourceActualSortedFrequencyScales 20 d L b slot i := by
  intro i
  let j := (sourceSortedLabelEquiv 20 (sourceActualSortedScales 20 d L) b slot i).val.1
  change 0 < sourceOriginalPGroupScale 20 L j.val
  exact source_original_positive_dyadic_scale 20 j.val L (by norm_num) hL

/-- Literal Parity (4.5) UPPER e-range for original actual moving source
Q bands, original frequencies/scales, and literal native B590 smooth
allocation weights: EVERY branch with NONZERO smooth product has e<=ℰ,
not an assumed range gate. Proof applies to any original marked band,
reserved labelled slot and prime tuple, including repeated Q primes. -/
theorem parity_actual_sorted_Q_smooth_e_upper434
    (L E : ℝ) (hL : 0 < L) (hE : 1 ≤ E)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length → Bool)
    (p : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length) →
      {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
        L band slot i})
    (hWeight : parityOriginalQAllocationBranchWeight434 20 E
      (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L band slot)
      delta (fun i => (p i).val) ≠ 0) :
    (paritySourceOrderedAllocatedE434 delta p : ℝ) ≤ E := by
  have hS := parity_actual_sorted_Q_allocation_scales_positive434
    (sourceOriginalLiteralDepth 20 L) L hL band slot
  have hp : ∀ i, 0 < (p i).val := by
    intro i
    let j := (sourceSortedLabelEquiv 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot i).val.1
    exact (source_original_Q_actual_prime 20
      (sourceOriginalLiteralDepth 20 L) L j (p i).val (p i).property).pos
  exact parity_original_Q_smooth_positive_branch_e_le_capacity434 20 E
    (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L band slot)
    delta p hE hS hp hWeight
end Green64Analytic.Parity

end

end

/-! ## ActualSmoothAllocatedEFibre -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000
set_option maxRecDepth 30000

/-- Literal actual r20/dynamic-Q e-allocation coefficient, with the
PORTED actual B590 smooth transition gate product at EACH original
ordered Q slot, and arbitrary complex Fourier/factorial phase factors.
The source factor `sourceBufferedGateReal` is not approximated or swapped
for a new cutoff. Historical Parity a_e additionally requires an exact
identification of the remaining original branch phase and grouping. -/
def parityActualSortedQSmoothEFibre434
    (L E : ℝ)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (phase :
      (Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) →
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) → ℂ)
    (e : ℕ) : ℂ :=
  paritySourceOrderedAllocatedEFibre434
    (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot)
    (fun delta p =>
      (parityOriginalQAllocationBranchWeight434 20 E
        (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
          band slot) delta (fun i => (p i).val) : ℂ) * phase delta p) e

/-- Exact ZERO outside the original upper range Parity (4.5), for ANY
complex Fourier-phase, factorial or signed weights. Each SOURCE-labelled
Q-branch with e>E has its ACTUAL smooth allocation gate product zero;
no unjustified cancellation argument is used. -/
theorem parity_actual_sorted_Q_smooth_e_fibre_above_cap_zero434
    (L E : ℝ) (hL : 0 < L) (hE : 1 ≤ E)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (phase :
      (Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) →
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) → ℂ)
    (e : ℕ) (hAbove : E < (e : ℝ)) :
    parityActualSortedQSmoothEFibre434 L E band slot phase e = 0 := by
  unfold parityActualSortedQSmoothEFibre434
    paritySourceOrderedAllocatedEFibre434 sourceEndpointFibre
  apply Finset.sum_eq_zero
  intro x hx
  have hMatch : paritySourceOrderedAllocatedE434 x.1 x.2 = e :=
    (Finset.mem_filter.mp hx).2
  have hZero : parityOriginalQAllocationBranchWeight434 20 E
        (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
          band slot) x.1 (fun i => (x.2 i).val) = 0 := by
    by_contra hNonzero
    have hBound := parity_actual_sorted_Q_smooth_e_upper434
      L E hL hE band slot x.1 x.2 hNonzero
    rw [hMatch] at hBound
    exact (not_lt_of_ge hBound) hAbove
  simp [hZero]

/-- The finite source Q sum with native smooth gate weights is EXACTLY
its sum by original allocated e fibres, for any complex Fourier phase.
Factorial normalization and other phases are carried as-is; the
sourceFibre is the SAME `sourceEndpointFibre` used throughout Green64. -/
theorem parity_actual_sorted_Q_smooth_e_fibre_reindex434
    (L E : ℝ)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (phase :
      (Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) →
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i}) → ℂ) :
    (∑ x :
      ((Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool) ×
      ((i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length) →
        {q : ℕ // q ∈ sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L)
          L band slot i})),
      (parityOriginalQAllocationBranchWeight434 20 E
        (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
          band slot) x.1 (fun i => (x.2 i).val) : ℂ) * phase x.1 x.2) =
    ∑ e ∈ paritySourceOrderedAllocatedESupport434
      (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot),
      parityActualSortedQSmoothEFibre434 L E band slot phase e := by
  exact parity_source_ordered_e_fibre_reindex434
    (sourceActualSortedQ 20 (sourceOriginalLiteralDepth 20 L) L band slot)
    (fun delta p =>
      (parityOriginalQAllocationBranchWeight434 20 E
        (sourceActualSortedFrequencyScales 20 (sourceOriginalLiteralDepth 20 L) L
          band slot) delta (fun i => (p i).val) : ℂ) * phase delta p)
end Green64Analytic.Parity

end

end

/-! ## SmoothAllocationLastSkip -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000
set_option maxRecDepth 30000

/-- Original sorted Q slots split exactly into earlier, the current
slot, and later. No prime slot or repeated prime label disappears. -/
theorem parity_original_sorted_Q_slot_sum_before_at_after434
    {n : ℕ} (j : Fin n) (f : Fin n → ℝ) :
    (∑ i : Fin n, f i) =
      (∑ i ∈ (Finset.univ.filter (fun i : Fin n => i < j)), f i) + f j +
      (∑ i ∈ (Finset.univ.filter (fun i : Fin n => j < i)), f i) := by
  let B := (Finset.univ.filter (fun i : Fin n => i < j))
  let A := (Finset.univ.filter (fun i : Fin n => j < i))
  have hSplit : (Finset.univ : Finset (Fin n)).erase j = B ∪ A := by
    ext i
    simp only [B,A,Finset.mem_erase,Finset.mem_univ,Finset.mem_union,
      Finset.mem_filter,true_and]
    constructor
    · intro h
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact Or.inl hlt
      · exact (h.1 heq).elim
      · exact Or.inr hgt
    · intro h
      rcases h with hlt | hgt
      · exact ⟨ne_of_lt hlt,trivial⟩
      · exact ⟨Ne.symm (ne_of_lt hgt),trivial⟩
  have hDisjoint : Disjoint B A := by
    apply Finset.disjoint_left.mpr
    intro i hi hia
    have hb : i < j := (Finset.mem_filter.mp hi).2
    have ha : j < i := (Finset.mem_filter.mp hia).2
    exact (not_lt_of_ge hb.le) ha
  have hSum := Finset.sum_erase_add (Finset.univ : Finset (Fin n)) f
    (Finset.mem_univ j)
  rw [hSplit,Finset.sum_union hDisjoint] at hSum
  dsimp only [B,A] at hSum
  linarith

/-- A positive original f0 (skipped) smooth branch has
`R_i - log p_i < s_i`. This is the complement to the f1 no-overdraft
lemma and comes from the ACTUAL native B590 `Real.smoothTransition` gate. -/
theorem parity_original_Q_smooth_positive_skip_slot_budget434
    {n : ℕ} (r : ℕ) (E : ℝ) (scales : Fin n → ℝ)
    (delta : Fin n → Bool) (p : Fin n → ℕ)
    (hScales : ∀ i, 0 < scales i)
    (hWeight : parityOriginalQAllocationBranchWeight434 r E scales delta p ≠ 0)
    (i : Fin n) (hSkipped : delta i = false) :
    parityOriginalQAllocationResidual434 E delta p i <
      Real.log (p i : ℝ) + scales i := by
  have hNZ : sourceBufferedGateReal r (delta i)
      ((parityOriginalQAllocationResidual434 E delta p i - Real.log (p i : ℝ)) /
        scales i) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hWeight) i (Finset.mem_univ i)
  rw [hSkipped] at hNZ
  have hNotOne : Real.smoothTransition
      ((parityOriginalQAllocationResidual434 E delta p i - Real.log (p i : ℝ)) /
        scales i) ≠ 1 := by
    intro hOne
    apply hNZ
    simp [sourceBufferedGateReal,hOne]
  have ht :
      (parityOriginalQAllocationResidual434 E delta p i - Real.log (p i : ℝ)) /
        scales i < 1 := by
    by_contra hNo
    exact hNotOne (Real.smoothTransition.one_of_one_le (le_of_not_gt hNo))
  have hNum : parityOriginalQAllocationResidual434 E delta p i -
      Real.log (p i : ℝ) < scales i :=
    (div_lt_one (hScales i)).mp ht
  linarith
end Green64Analytic.Parity

end

end

