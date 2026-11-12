module

public import Green64.Library.Sieve.Foundations.Part049
public import Green64.Library.Sieve.Foundations.Part050
public import Green64.Library.Sieve.Foundations.Part044
public import Green64.Library.Sieve.Foundations.Part036
public import Green64.Library.Sieve.Foundations.Part045

@[expose] public section

/-!
# Sieve / Foundations / Part051

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SignedFullCellGlobalAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Genuine original FULL-CELL signed factorial/epsilon TypeII
source enjoys arbitrary logarithmic saving uniformly over ALL
actually attained quarter UV cuts, with true log-square dyadic loss.
All parameters H,J,B,S are selected before L. This is a SINGLE
original full-cell prime/rough test, one reserved original Q band
and slot, one signed branch and one original beta interval; NOT
all external Parity §7.3 sieve/test/fine families or arbitrary alpha. -/
theorem parity_eventually_original_signed_fullcell_quarter_b629_anylog434
    (jQ : ℕ) (goal target C0 beta betaP bstar gamma K0 A R : ℝ)
    (hbetaP : 0<betaP)
    (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
          ∀ (slot : Fin 20) (prime : Bool)
            (betaCoeff : ℕ → ℂ) (signed : Bool),
            (∀n∈Finset.Icc c e,‖betaCoeff n‖≤1) →
          let d := sourceOriginalLiteralDepth 20 L
          let T := (parityOriginalActualTypeIIDyadicPairScales434
              (parityOriginalTypeIIPhysicalPairs434
                (Finset.Icc a b) (Finset.Icc c e) Y)).filter
              (parityOriginalTypeIIQuarterProductGate434 L)
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          ‖parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
             betaCoeff signed 0 Y‖ ≤
            (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ)*Bound := by
  have hPaid := parity_eventually_original_signed_quarter_actual_cut_sum_paid434
    jQ goal target C0 beta betaP bstar gamma K0 A R
    hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
    hbeta hgamma hK0 hA hR buf hSmooth hSupport hOne4 hCube
    Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  obtain ⟨H,J,B,S,hBS,hPaidL⟩ := hPaid
  refine ⟨H,J,B,S,hBS,?_⟩
  filter_upwards [hPaidL] with L hLnow
  rcases hLnow with ⟨hBig,h128,h24,hFam,hReserved,hRest⟩
  refine ⟨hBig,h128,h24,hFam,hReserved,?_⟩
  intro hL hFamily a b c e Y ha hc hab hExpB hY band hBandNow
    slot prime betaCoeff signed hBetaWhole
  subst Y
  let Y : ℕ := ⌊2*Real.exp L⌋₊
  classical
  let T := (parityOriginalActualTypeIIDyadicPairScales434
      (parityOriginalTypeIIPhysicalPairs434
        (Finset.Icc a b) (Finset.Icc c e) Y)).filter
      (parityOriginalTypeIIQuarterProductGate434 L)
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+24*(2+Cphys+24*C1)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let Bound := (4+Csource*(∫s : ℝ,
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
       20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
  have hSum := hRest hL hFamily a b c e Y ha hc hab hExpB
    band hBandNow slot prime betaCoeff signed hBetaWhole
  have haPos : 0<a := by
    have hr : (0:ℝ)<(a:ℝ) := (Real.exp_pos _).trans_le ha
    exact_mod_cast hr
  have hcPos : 0<c := by
    have hr : (0:ℝ)<(c:ℝ) := (Real.exp_pos _).trans_le hc
    exact_mod_cast hr
  have hExact := parity_original_signed_fullcell_eq_quarter_b629_cut_sources434
    (sourceOriginalLiteralDepth 20 L) L Psi (by linarith : 0≤L)
    hPsiSet a b c e Y haPos hcPos prime S gamma betaCoeff signed 0
  have hCard := parity_original_actual_quarter_Icc_dyadic_card_le_log_sq434
    a b c e Y L
  have hCmoment : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hC1 : 0≤C1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hLog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hCsource : 0≤Csource := by dsimp [Csource,Cphys]; positivity
  have hM0 : 0≤(∫s : ℝ,
      ‖(𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) :=
    integral_nonneg (fun s => norm_nonneg _)
  have hMH : 0≤M_H := by
    dsimp [M_H]
    apply integral_nonneg
    intro s
    exact mul_nonneg (by positivity) (norm_nonneg _)
  have hBoundNonneg : 0≤Bound := by
    dsimp [Bound]
    have hp : 0≤(2*Real.pi)^H := pow_nonneg (by positivity) _
    positivity
  have hCardReal : (T.card:ℝ) ≤
      (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ) := by
    exact_mod_cast hCard
  change ‖parityOriginalShiftTwoSignedBilinearMellinSource434
    (sourceOriginalLiteralDepth 20 L) L Psi (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
    betaCoeff signed 0 Y‖ ≤ _
  rw [hExact]
  calc
    _ ≤ (T.card:ℝ)*Bound := by
      simpa only [T,Bound,C1,Cmoment,Cphys,Csource,M_H] using hSum
    _ ≤ (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ)*Bound :=
      mul_le_mul_of_nonneg_right hCardReal hBoundNonneg
end Green64Analytic.Parity

end

end

/-! ## QuarterLogSquareAbsorption -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- Actual original smooth cutoff Y0=floor(2 exp L) has only O(L)
binary factor scales, with fixed source-ordered constant
Cdyad=1+2/log2. No arbitrary new Y cap or external family count. -/
theorem parity_original_actual_Y0_binary_log_count_le_linear434
    (L : ℝ) (hL : 8≤L) :
    let Y0 := ⌊2*Real.exp L⌋₊
    ((Nat.log 2 (Y0+2)+1:ℕ):ℝ) ≤
      (1+2/Real.log 2)*L := by
  dsimp
  let Y0 : ℕ := ⌊2*Real.exp L⌋₊
  have he : 0<Real.exp L := Real.exp_pos _
  have heOne : 1≤Real.exp L := by
    have hh := Real.add_one_le_exp L
    linarith
  have hFloor : (Y0:ℝ)≤2*Real.exp L :=
    Nat.floor_le (by positivity)
  have hUpper : ((Y0+2:ℕ):ℝ)≤4*Real.exp L := by
    push_cast
    nlinarith [hFloor,heOne]
  have hPos : 0<((Y0+2:ℕ):ℝ) := by
    exact_mod_cast (show 0<Y0+2 by omega)
  have hLog : Real.log ((Y0+2:ℕ):ℝ)≤2*L := by
    have hh := Real.log_le_log hPos hUpper
    rw [Real.log_mul (by norm_num : (4:ℝ)≠0) (Real.exp_ne_zero L),
      Real.log_exp] at hh
    have h4 : Real.log (4:ℝ)≤3 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
      linarith
    linarith
  have hLogTwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hNatLog : ((Nat.log 2 (Y0+2):ℕ):ℝ) ≤ 2*L/Real.log 2 := by
    have h := Real.natLog_le_logb (Y0+2) 2
    apply h.trans
    unfold Real.logb
    exact div_le_div_of_nonneg_right hLog hLogTwo.le
  calc
    _ = ((Nat.log 2 (Y0+2):ℕ):ℝ)+1 := by push_cast; ring
    _ ≤ 2*L/Real.log 2+1 := by linarith
    _ ≤ 2*L/Real.log 2+L := by linarith
    _ = (1+2/Real.log 2)*L := by ring

/-- The actual original finite signed quarter-dyad count cost on
the source Ψ window Y0 is at most Cdyad² L², with Cdyad fixed
BEFORE original Parity TypeII precision and before the large L. -/
theorem parity_original_actual_Y0_quarter_log_sq_le_L_sq434
    (L : ℝ) (hL : 8≤L) :
    (((Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1)*
       (Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1):ℕ):ℝ) ≤
      (1+2/Real.log 2)^2*L^2 := by
  have hh := parity_original_actual_Y0_binary_log_count_le_linear434 L hL
  dsimp only at hh
  have hCount : 0≤(1+2/Real.log 2)*L := by
    have hLog : 0<Real.log 2 := Real.log_pos (by norm_num)
    positivity
  calc
    _ = (((Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1:ℕ):ℝ))^2 := by
      push_cast
      ring
    _ ≤ ((1+2/Real.log 2)*L)^2 := pow_le_pow_left₀ (by positivity) hh 2
    _ = (1+2/Real.log 2)^2*L^2 := by ring

/-- Paying the two *actual* quarter-dyadic logarithmic losses never
changes the requested final exponent: just request local precision
D=goal+2 before the source K0/J/B/S choices. -/
theorem parity_original_actual_quarter_log_sq_power_absorption434
    (L goal : ℝ) (hL : 8≤L) :
    (((Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1)*
       (Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1):ℕ):ℝ)*
      L^(-(goal+2)) ≤
      (1+2/Real.log 2)^2*L^(-goal) := by
  have hCnt := parity_original_actual_Y0_quarter_log_sq_le_L_sq434 L hL
  have hLp : 0<L := by linarith
  have hPower : L^2*L^(-(goal+2)) = L^(-goal) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hLp]
    congr 1
    ring
  have hNonneg : 0≤L^(-(goal+2)) := (Real.rpow_pos_of_pos hLp _).le
  calc
    _ ≤ ((1+2/Real.log 2)^2*L^2)*L^(-(goal+2)) :=
      mul_le_mul_of_nonneg_right hCnt hNonneg
    _ = (1+2/Real.log 2)^2*L^(-goal) := by rw [mul_assoc,hPower]
end Green64Analytic.Parity

end

end

/-! ## SignedFullCellGlobalIntegratedAudit -/

section



end

/-! ## SignedFullCellNoLogLoss -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- COMPLETE source-true original signed full-cell prime/rough
factorial/epsilon proxy with all physically attained quarter UV
binary dyads paid: original selected-band one-slot source saving
O_goal(exp L L^-goal) without any leftover log-square factor.
The source precision goal+2 is fixed BEFORE K0 and H,J,B,S;
real original beta/test/region external families remain outside. -/
theorem parity_eventually_original_signed_fullcell_quarter_b629_no_log_loss434
    (jQ : ℕ) (goal target C0 beta betaP bstar gamma K0 A R : ℝ)
    (hbetaP : 0<betaP)
    (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
          ∀ (slot : Fin 20) (prime : Bool)
            (betaCoeff : ℕ → ℂ) (signed : Bool),
            (∀n∈Finset.Icc c e,‖betaCoeff n‖≤1) →
          let d := sourceOriginalLiteralDepth 20 L
          let T := (parityOriginalActualTypeIIDyadicPairScales434
              (parityOriginalTypeIIPhysicalPairs434
                (Finset.Icc a b) (Finset.Icc c e) Y)).filter
              (parityOriginalTypeIIQuarterProductGate434 L)
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          ‖parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
             betaCoeff signed 0 Y‖ ≤
            (1+2/Real.log 2)^2*Bound := by
  have hPrev := parity_eventually_original_signed_fullcell_quarter_b629_anylog434
    jQ (goal+2) target C0 beta betaP bstar gamma K0 A R
    hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
    hbeta hgamma hK0 hA hR buf hSmooth hSupport hOne4 hCube
    Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  obtain ⟨H,J,B,S,hBS,hPrevL⟩ := hPrev
  refine ⟨H,J,B,S,hBS,?_⟩
  filter_upwards [hPrevL] with L hLnow
  rcases hLnow with ⟨hBig,h128,h24,hFam,hReserved,hRest⟩
  refine ⟨hBig,h128,h24,hFam,hReserved,?_⟩
  intro hL hFamily a b c e Y ha hc hab hExpB hY band hBandNow
    slot prime betaCoeff signed hBetaWhole
  classical
  have hBound := hRest hL hFamily a b c e Y ha hc hab hExpB hY
    band hBandNow slot prime betaCoeff signed hBetaWhole
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+24*(2+Cphys+24*C1)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let Coef := 4+Csource*(∫s : ℝ,
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
       20*(2*Real.pi)^H*M_H
  have hCmoment : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hC1 : 0≤C1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hLog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hCsource : 0≤Csource := by dsimp [Csource,Cphys]; positivity
  have hM0 : 0≤(∫s : ℝ,
      ‖(𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) :=
    integral_nonneg (fun s => norm_nonneg _)
  have hMH : 0≤M_H := by
    dsimp [M_H]
    apply integral_nonneg
    intro s
    exact mul_nonneg (by positivity) (norm_nonneg _)
  have hCoef : 0≤Coef*Real.exp L := by
    dsimp [Coef]
    positivity
  have hPower := parity_original_actual_quarter_log_sq_power_absorption434
    L goal (by linarith : 8≤L)
  rw [hY] at hBound ⊢
  change ‖parityOriginalShiftTwoSignedBilinearMellinSource434
    (sourceOriginalLiteralDepth 20 L) L Psi (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
    betaCoeff signed 0 ⌊2*Real.exp L⌋₊‖ ≤ _
  calc
    _ ≤ (((Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1)*
        (Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1):ℕ):ℝ)*
        (Coef*Real.exp L*L^(-(goal+2))) := by
      simpa only [Coef,C1,Cmoment,Cphys,Csource,M_H,mul_assoc] using hBound
    _ = (Coef*Real.exp L)*
      ((((Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1)*
        (Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1):ℕ):ℝ)*
        L^(-(goal+2))) := by ring
    _ ≤ (Coef*Real.exp L)*((1+2/Real.log 2)^2*L^(-goal)) :=
      mul_le_mul_of_nonneg_left hPower hCoef
    _ = (1+2/Real.log 2)^2*(Coef*Real.exp L*L^(-goal)) := by ring
end Green64Analytic.Parity

end

end

/-! ## BothParityFirstProxyAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem parity_original_signed_first_proxy_difference434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (K J : Finset ℕ)
    (sharp proxy betaCoeff : ℕ → ℂ) (signed : Bool) (rho : ℝ) (Y : ℕ) :
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J sharp betaCoeff signed rho Y -
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J proxy betaCoeff signed rho Y =
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J (fun m => sharp m-proxy m) betaCoeff signed rho Y := by
  rw [parity_original_signed_two_factor_proxy_telescoping434]
  simp [parityOriginalShiftTwoSignedBilinearMellinSource434]

/-- The actual one-factor source error used in Parity section 8.3:
replace the first prime/rough test by its unchanged full-cell B_I,
while keeping an arbitrary bounded second coefficient (in particular
the sharp prime test). Both original Aρ projections use ONE H,J,B,S.
This estimate is not inferred from the combined two-step error. -/
theorem parity_eventually_original_both_parity_first_fullcell_proxy_anylog434
    (jQ : ℕ) (goal target C0 beta betaP bstar gamma K0 A R : ℝ)
    (hbetaP : 0<betaP)
    (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (prime : Bool) (betaCoeff : ℕ → ℂ) (rho : ℝ),
            rho=1 ∨ rho=(-1) →
            (∀n∈Finset.Icc c e,‖betaCoeff n‖≤1) →
          let d := sourceOriginalLiteralDepth 20 L
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          ‖parityOriginalParityBilinearSource434 d L rho Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullCellSharpTest434 prime L gamma a b) betaCoeff Y -
            parityOriginalParityBilinearSource434 d L rho Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b) betaCoeff Y‖ ≤
            (1+2/Real.log 2)^2*Bound := by
  obtain ⟨H,J,B,S,hBS,hSource⟩ :=
    parity_eventually_original_signed_fullcell_quarter_b629_no_log_loss434
      jQ goal target C0 beta betaP bstar gamma K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hgamma hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  refine ⟨H,J,B,S,hBS,?_⟩
  filter_upwards [hSource] with L hSourceL
  rcases hSourceL with ⟨hBig,h128,h24,hFamily,hReserved,hRest⟩
  refine ⟨hBig,h128,h24,hFamily,hReserved,?_⟩
  intro a b c e Y ha hc hab hExpB hY prime betaCoeff rho hSigns hBetaWhole
  let band : Fin (sourceOriginalLiteralDepth 20 L+1) :=
    ⟨jQ,Nat.lt_succ_of_le hReserved⟩
  have hFalse := hRest h128 hFamily a b c e Y ha hc hab hExpB hY
    band rfl (0:Fin 20) prime betaCoeff false hBetaWhole
  have hTrue := hRest h128 hFamily a b c e Y ha hc hab hExpB hY
    band rfl (0:Fin 20) prime betaCoeff true hBetaWhole
  have hDelta :
      (fun m => parityOriginalActualFullCellSharpTest434 prime L gamma a b m -
        parityOriginalActualFullCellProxyBeta434 prime L S gamma a b m) =
      parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b := by
    funext m
    have h := parity_original_actual_fullcell_proxy_plus_delta_eq_test434
      prime L S gamma a b m
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)
  dsimp only at hFalse hTrue
  rw [←hDelta] at hFalse hTrue
  rw [←parity_original_signed_first_proxy_difference434
    (sourceOriginalLiteralDepth 20 L) L Psi (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalActualFullCellSharpTest434 prime L gamma a b)
    (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b)
    betaCoeff false 0 Y] at hFalse
  rw [←parity_original_signed_first_proxy_difference434
    (sourceOriginalLiteralDepth 20 L) L Psi (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalActualFullCellSharpTest434 prime L gamma a b)
    (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b)
    betaCoeff true 0 Y] at hTrue
  have hLpos : 0<L := by linarith
  have hRho : |rho|≤1 := by
    rcases hSigns with rfl | rfl <;> norm_num
  exact parity_original_parity_replacement_norm_le434
    (sourceOriginalLiteralDepth 20 L) L rho hLpos hRho
    Psi (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalActualFullCellSharpTest434 prime L gamma a b) betaCoeff
    (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b) betaCoeff
    Y _ hFalse hTrue
end Green64Analytic.Parity

end

end

/-! ## BothParityJointProxySteps -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Exact factor exchange and half scaling for the independently defined
original parity source. Neither the arithmetic weight nor the full-cell
coefficient is changed. -/
theorem parity_original_parity_source_swapped_half_exact434
    (d : ℕ) (L rho : ℝ) (hL : 0 < L) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalParityBilinearSource434 d L rho Psi K J alpha beta Y =
      2 * parityOriginalParityBilinearSource434
        d L rho Psi J K beta (fun m => alpha m/(2:ℂ)) Y := by
  rw [parity_original_parity_bilinear_eq_signed_mellin_projection434
    d L rho hL Psi K J alpha beta Y,
    parity_original_parity_bilinear_eq_signed_mellin_projection434
    d L rho hL Psi J K beta (fun m => alpha m/(2:ℂ)) Y]
  rw [parity_original_signed_second_proxy_swapped_half_exact434
    d L Psi K J alpha beta false 0 Y,
    parity_original_signed_second_proxy_swapped_half_exact434
    d L Psi K J alpha beta true 0 Y]
  ring

/-- A real second-step source difference with an already nonsmooth
companion is controlled by the switched first-step difference. -/
theorem parity_original_parity_second_difference_half_norm_paid434
    (d : ℕ) (L rho : ℝ) (hL : 0 < L) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta beta' : ℕ → ℂ) (Y : ℕ)
    (M : ℝ)
    (hSwapped : ‖parityOriginalParityBilinearSource434
        d L rho Psi J K beta (fun m => alpha m/(2:ℂ)) Y -
      parityOriginalParityBilinearSource434
        d L rho Psi J K beta' (fun m => alpha m/(2:ℂ)) Y‖ ≤ M) :
    ‖parityOriginalParityBilinearSource434 d L rho Psi K J alpha beta Y -
      parityOriginalParityBilinearSource434 d L rho Psi K J alpha beta' Y‖ ≤ 2*M := by
  rw [parity_original_parity_source_swapped_half_exact434
    d L rho hL Psi K J alpha beta Y,
    parity_original_parity_source_swapped_half_exact434
    d L rho hL Psi K J alpha beta' Y, ←mul_sub, norm_mul]
  rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num [Complex.norm_def]]
  exact mul_le_mul_of_nonneg_left hSwapped (by norm_num)

/-- One source-ordered H,J,B,S simultaneously bounds each individual
replacement, the SUM of their error norms, and the combined difference
for both original parity signs and all four prime/rough test choices
at a fixed gamma. The second companion is the actual nonsmooth B_I.
The universal interval variables also permit either factor orientation.
No total over external source families or Xrho comparison is asserted. -/
theorem parity_eventually_original_both_parity_joint_proxy_steps_anylog434
    (jQ : ℕ) (goal target C0 beta betaP bstar gamma K0 A R : ℝ)
    (hbetaP : 0<betaP) (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hce : e≤2*c) (hExpE : (e:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (prime secondPrime : Bool) (rho : ℝ), rho=1 ∨ rho=(-1) →
          let d := sourceOriginalLiteralDepth 20 L
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          let sharpSharp := parityOriginalParityBilinearSource434 d L rho Psi
            (Finset.Icc a b) (Finset.Icc c e)
            (parityOriginalActualFullCellSharpTest434 prime L gamma a b)
            (parityOriginalActualFullCellSharpTest434 secondPrime L gamma c e) Y
          let proxySharp := parityOriginalParityBilinearSource434 d L rho Psi
            (Finset.Icc a b) (Finset.Icc c e)
            (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b)
            (parityOriginalActualFullCellSharpTest434 secondPrime L gamma c e) Y
          let proxyProxy := parityOriginalParityBilinearSource434 d L rho Psi
            (Finset.Icc a b) (Finset.Icc c e)
            (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b)
            (parityOriginalActualFullCellProxyBeta434 secondPrime L S gamma c e) Y
          let C := (1+2/Real.log 2)^2*Bound
          ‖sharpSharp-proxySharp‖ ≤ C ∧
          ‖proxySharp-proxyProxy‖ ≤ 2*C ∧
          ‖sharpSharp-proxySharp‖+‖proxySharp-proxyProxy‖ ≤ 3*C ∧
          ‖sharpSharp-proxyProxy‖ ≤ 3*C := by
  obtain ⟨H,J,B,S,hBS,hSource⟩ :=
    parity_eventually_original_both_parity_first_fullcell_proxy_anylog434
      jQ goal target C0 beta betaP bstar gamma K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hgamma hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  have hS : 0 < S := by
    have hB : (0:ℝ) ≤ (B:ℝ) := Nat.cast_nonneg _
    linarith
  have hbpos : 0 < bstar := by linarith
  have hProxy := parity_eventually_original_actual_fullcell_second_proxy_beta_uniform434
    S bstar gamma hS hbpos hgamma
  refine ⟨H,J,B,S,hBS,?_⟩
  filter_upwards [hSource,hProxy] with L hSourceL hProxyL
  rcases hSourceL with ⟨hBig,h128,h24,hFamily,hReserved,hRest⟩
  refine ⟨hBig,h128,h24,hFamily,hReserved,?_⟩
  intro a b c e Y ha hc hab hExpB hce hExpE hY prime secondPrime rho hSigns
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let N := Finset.Icc c e
  let sharpM := parityOriginalActualFullCellSharpTest434 prime L gamma a b
  let sharpN := parityOriginalActualFullCellSharpTest434 secondPrime L gamma c e
  let proxyM := parityOriginalActualFullCellProxyBeta434 prime L S gamma a b
  let proxyN := parityOriginalActualFullCellProxyBeta434 secondPrime L S gamma c e
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 0
  let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+24*(2+Cphys+24*C1)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let Bound := (4+Csource*(∫s : ℝ,
      ‖(𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
        20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
  let C := (1+2/Real.log 2)^2*Bound
  let s0 := parityOriginalParityBilinearSource434 d L rho Psi K N sharpM sharpN Y
  let s1 := parityOriginalParityBilinearSource434 d L rho Psi K N proxyM sharpN Y
  let s2 := parityOriginalParityBilinearSource434 d L rho Psi K N proxyM proxyN Y
  change ‖s0-s1‖ ≤ C ∧ ‖s1-s2‖ ≤ 2*C ∧
    ‖s0-s1‖+‖s1-s2‖ ≤ 3*C ∧ ‖s0-s2‖ ≤ 3*C
  have hSharpN : ∀n∈N,‖sharpN n‖≤1 := by
    intro n hn
    exact parity_original_actual_fullcell_sharp_test_norm_le_one434
      secondPrime L gamma c e n
  have hFirst : ‖s0-s1‖ ≤ C := by
    simpa only [s0,s1,d,K,N,sharpM,sharpN,proxyM,C,Bound,C1,Cmoment,Cphys,Csource,M_H]
      using hRest a b c e Y ha hc hab hExpB hY prime sharpN rho hSigns hSharpN
  have hMlow : Real.exp (bstar*L) ≤ (a:ℝ) := by
    calc
      _ ≤ Real.exp (2*bstar*L) := by
        apply Real.exp_le_exp.mpr
        nlinarith [h128,hbpos]
      _ ≤ (a:ℝ) := ha
  have hProxyNorm : ∀m∈K,‖proxyM m/(2:ℂ)‖≤1 := by
    intro m hm
    exact (hProxyL prime a b hMlow m).2
  have hSwapped :
      ‖parityOriginalParityBilinearSource434 d L rho Psi N K
          sharpN (fun m => proxyM m/(2:ℂ)) Y -
        parityOriginalParityBilinearSource434 d L rho Psi N K
          proxyN (fun m => proxyM m/(2:ℂ)) Y‖ ≤ C := by
    simpa only [d,K,N,sharpN,proxyN,proxyM,C,Bound,C1,Cmoment,Cphys,Csource,M_H]
      using hRest c e a b Y hc ha hce hExpE hY secondPrime
        (fun m => proxyM m/(2:ℂ)) rho hSigns hProxyNorm
  have hLpos : 0 < L := by linarith
  have hSecond : ‖s1-s2‖ ≤ 2*C :=
    parity_original_parity_second_difference_half_norm_paid434
      d L rho hLpos Psi K N proxyM sharpN proxyN Y C hSwapped
  have hSum : ‖s0-s1‖+‖s1-s2‖ ≤ 3*C := by linarith
  refine ⟨hFirst,hSecond,hSum,?_⟩
  calc
    ‖s0-s2‖ = ‖(s0-s1)+(s1-s2)‖ := by congr 1 <;> ring
    _ ≤ ‖s0-s1‖+‖s1-s2‖ := norm_add_le _ _
    _ ≤ 3*C := hSum
end Green64Analytic.Parity

end

end

/-! ## SignedSecondProxyBetaScaling -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- Exact homogeneous linearity of the ORIGINAL 20! factorial/epsilon
signed h=-2 source in its nonsmooth SECOND coefficient beta.
No assumption on beta, no loss in source weights, and valid even
at rho≠0, Y=0, both epsilon branches and all physical m,n factors. -/
theorem parity_original_signed_source_beta_two_scaling434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) :
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J alpha beta signed rho Y =
    (2:ℂ)*parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J alpha (fun n => beta n/2) signed rho Y := by
  classical
  unfold parityOriginalShiftTwoSignedBilinearMellinSource434
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hFibre :
      (∑ z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
         alpha z.1*beta z.2) =
      (2:ℂ)*(∑ z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
         alpha z.1*(beta z.2/2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hFibre]
  ring

/-- The normalized original full-cell prime/rough nonsmooth proxy
is uniformly bounded in native source at all m once the ORIGINAL
whole factor interval starts at exp(beta L). We use independently
proved full-cell delta coefficient |I-B_I|≤1, not an invented B_I≤1.
-/
theorem parity_eventually_original_second_proxy_beta_half_norm_one434
    (S beta gamma : ℝ) (hS : 0<S)
    (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, ∀(prime : Bool) (a b : ℕ),
      Real.exp (beta*L)≤(a:ℝ) → ∀n : ℕ,
      ‖parityOriginalActualFullCellProxyBeta434 prime L S gamma a b n/2‖≤1 := by
  filter_upwards [parity_eventually_original_full_dyad_proxy_norm_rough434
      S beta gamma hS hbeta hgamma] with L hAlpha
  intro prime a b ha n
  have hh := (hAlpha prime a b ha n).1
  exact parity_original_actual_second_proxy_beta_half_norm_le_one434
    prime L S gamma a b n hh
end Green64Analytic.Parity

end

end

/-! ## SignedSecondNonsmoothFullCell -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Original second nonsmooth proxy: first factor I-B_I, second
already replaced B_I, both literal prime/rough full-cell proxies.
Uniform source O_A for all quarter dyads with just constant 2. -/
theorem parity_eventually_original_signed_fullcell_second_nonsmooth_proxy_anylog434
    (jQ : ℕ) (goal target C0 beta betaP bstar gamma K0 A R : ℝ)
    (hbetaP : 0<betaP)
    (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (gammaSecond : ℝ) (hgammaSecond : 0<gammaSecond)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
          ∀ (slot : Fin 20) (prime secondPrime : Bool) (signed : Bool),
          let d := sourceOriginalLiteralDepth 20 L
          let T := (parityOriginalActualTypeIIDyadicPairScales434
              (parityOriginalTypeIIPhysicalPairs434
                (Finset.Icc a b) (Finset.Icc c e) Y)).filter
              (parityOriginalTypeIIQuarterProductGate434 L)
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          ‖parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
             (parityOriginalActualFullCellProxyBeta434 secondPrime
                L S gammaSecond c e) signed 0 Y‖ ≤
            2*(1+2/Real.log 2)^2*Bound := by
  have hSource := parity_eventually_original_signed_fullcell_quarter_b629_no_log_loss434
    jQ goal target C0 beta betaP bstar gamma K0 A R
    hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
    hbeta hgamma hK0 hA hR buf hSmooth hSupport hOne4 hCube
    Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  obtain ⟨H,J,B,S,hBS,hOld⟩ := hSource
  have hS : 0<S := by
    have hb : (0:ℝ)≤(B:ℝ) := Nat.cast_nonneg _
    linarith
  have hBstar : 0<bstar := by linarith
  have hProxy := parity_eventually_original_second_proxy_beta_half_norm_one434
    S bstar gammaSecond hS hBstar hgammaSecond
  refine ⟨H,J,B,S,hBS,?_⟩
  filter_upwards [hOld,hProxy] with L hOldL hProxyL
  rcases hOldL with ⟨hBig,h128,h24,hFam,hReserved,hRest⟩
  refine ⟨hBig,h128,h24,hFam,hReserved,?_⟩
  intro hL hFamily a b c e Y ha hc hab hExpB hY band hBandNow
    slot prime secondPrime signed
  have hSecondLower : Real.exp (bstar*L)≤(c:ℝ) := by
    calc
      _ ≤ Real.exp (2*bstar*L) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hL,hBstar]
      _ ≤ (c:ℝ) := hc
  let secondBeta : ℕ → ℂ := parityOriginalActualFullCellProxyBeta434
    secondPrime L S gammaSecond c e
  have hBeta : ∀n∈Finset.Icc c e,‖secondBeta n/2‖≤1 := by
    intro n hn
    exact hProxyL secondPrime c e hSecondLower n
  have hBound := hRest hL hFamily a b c e Y ha hc hab hExpB hY
    band hBandNow slot prime (fun n => secondBeta n/2) signed hBeta
  have hScale := parity_original_signed_source_beta_two_scaling434
    (sourceOriginalLiteralDepth 20 L) L Psi
    (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
    secondBeta signed 0 Y
  dsimp only [secondBeta] at hScale hBound ⊢
  rw [hScale,norm_mul]
  have hTwo : ‖(2:ℂ)‖=(2:ℝ) := by norm_num
  rw [hTwo]
  have hh := mul_le_mul_of_nonneg_left hBound (by norm_num : (0:ℝ)≤2)
  simpa only [mul_assoc] using hh
end Green64Analytic.Parity

end

end

/-! ## SignedSecondNonsmoothOppositeOrientation -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- Source-faithful O_A error for the OPPOSITE orientation of Parity §7.3
second nonsmooth replacement: first original factor already holds
its full-cell prime/rough proxy B_I, while the SECOND factor is
(I-B_I). The signed 20! Q/P and h=-2 source is not changed:
apply the already verified source second-proxy theorem with the two
factor supports swapped by the new native signed source symmetry.
Both original positive factor intervals meet the same full-cell
source legality; the new fine gate is on [c,e] (second factor). -/
theorem parity_eventually_original_signed_fullcell_second_proxy_opposite_orientation_anylog434
    (jQ : ℕ) (goal target C0 beta betaP bstar gamma K0 A R : ℝ)
    (hbetaP : 0<betaP) (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (gammaSecond : ℝ) (hgammaSecond : 0<gammaSecond)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hce : e≤2*c) (hExpE : (e:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
          ∀ (slot : Fin 20) (firstPrime secondPrime : Bool) (signed : Bool),
          let d := sourceOriginalLiteralDepth 20 L
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          ‖parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullCellProxyBeta434 firstPrime L S gammaSecond a b)
             (parityOriginalActualFullDyadProxyDifference434 secondPrime L S gamma c e)
             signed 0 Y‖ ≤
            2*(1+2/Real.log 2)^2*Bound := by
  obtain ⟨H,J,B,S,hBS,hOld⟩ :=
    parity_eventually_original_signed_fullcell_second_nonsmooth_proxy_anylog434
      jQ goal target C0 beta betaP bstar gamma K0 A R
      hbetaP hbstar hBeta gammaSecond hgammaSecond hBand hC0 hTarget
      hK0Target hPrecision hbeta hgamma hK0 hA hR
      buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  refine ⟨H,J,B,S,hBS,?_⟩
  filter_upwards [hOld] with L hOldL
  rcases hOldL with ⟨hBig,h128,h24,hFam,hReserved,hRest⟩
  refine ⟨hBig,h128,h24,hFam,hReserved,?_⟩
  intro hL hFamily a b c e Y ha hc hce hExpE hY band hBand
    slot firstPrime secondPrime signed
  have hBound := hRest hL hFamily c e a b Y hc ha hce hExpE hY
    band hBand slot secondPrime firstPrime signed
  have hSwap := parity_original_signed_source_swap_factors434
    (sourceOriginalLiteralDepth 20 L) L Psi
    (Finset.Icc c e) (Finset.Icc a b)
    (parityOriginalActualFullDyadProxyDifference434 secondPrime L S gamma c e)
    (parityOriginalActualFullCellProxyBeta434 firstPrime L S gammaSecond a b)
    signed 0 Y
  dsimp only at hBound ⊢
  rw [hSwap] at hBound
  simpa only using hBound
end Green64Analytic.Parity

end

end

/-! ## SignedTwoReplacementSharedSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10500000

/-- BOTH original Parity §7.3 factor replacements for one fullcell
prime/rough source, with shared exponent gamma and a SINGLE
source-ordered H,J,B,S, chosen before L. The first step has sharp
second coefficient <=1, the second has nonsmooth first B_I <=2
and is paid via the original signed swap and B_I/2 bound. Hence
sharp-sharp minus nonsmooth-proxy-proxy has ≤3 TIMES the native
single whole-source signed saving. No arbitrary-alpha or external
sieve/test family count is claimed here. -/
theorem parity_eventually_original_signed_two_fullcell_proxy_shared_parameters_anylog434
    (jQ : ℕ) (goal target C0 beta betaP bstar gamma K0 A R : ℝ)
    (hbetaP : 0<betaP) (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hce : e≤2*c) (hExpE : (e:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)),band.val=jQ →
          ∀(slot : Fin 20) (prime secondPrime : Bool) (signed : Bool),
          let d := sourceOriginalLiteralDepth 20 L
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          ‖parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullCellSharpTest434 prime L gamma a b)
             (parityOriginalActualFullCellSharpTest434 secondPrime L gamma c e)
             signed 0 Y -
            parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b)
             (parityOriginalActualFullCellProxyBeta434 secondPrime L S gamma c e)
             signed 0 Y‖ ≤
            3*(1+2/Real.log 2)^2*Bound := by
  obtain ⟨H,J,B,S,hBS,hSource⟩ :=
    parity_eventually_original_signed_fullcell_quarter_b629_no_log_loss434
      jQ goal target C0 beta betaP bstar gamma K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hgamma hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  have hS : 0<S := by
    have hB : (0:ℝ)≤(B:ℝ) := Nat.cast_nonneg _
    linarith
  have hbpos : 0<bstar := by linarith
  have hProxy := parity_eventually_original_actual_fullcell_second_proxy_beta_uniform434
    S bstar gamma hS hbpos hgamma
  refine ⟨H,J,B,S,hBS,?_⟩
  filter_upwards [hSource,hProxy] with L hSourceL hProxyL
  rcases hSourceL with ⟨hBig,h128,h24,hFamily,hReserved,hRest⟩
  refine ⟨hBig,h128,h24,hFamily,hReserved,?_⟩
  intro hL hFamily0 a b c e Y ha hc hab hExpB hce hExpE hY band hBandNow
    slot prime secondPrime signed
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let N := Finset.Icc c e
  let sharpM := parityOriginalActualFullCellSharpTest434 prime L gamma a b
  let sharpN := parityOriginalActualFullCellSharpTest434 secondPrime L gamma c e
  let proxyM := parityOriginalActualFullCellProxyBeta434 prime L S gamma a b
  let proxyN := parityOriginalActualFullCellProxyBeta434 secondPrime L S gamma c e
  let deltaM := parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b
  let deltaN := parityOriginalActualFullDyadProxyDifference434 secondPrime L S gamma c e
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 0
  let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+24*(2+Cphys+24*C1)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let Bound := (4+Csource*(∫s : ℝ,
      ‖(𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
        20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
  have hSharpN : ∀n∈N,‖sharpN n‖≤1 := by
    intro n hn
    exact parity_original_actual_fullcell_sharp_test_norm_le_one434
      secondPrime L gamma c e n
  have hFirst := hRest hL hFamily0 a b c e Y ha hc hab hExpB hY
    band hBandNow slot prime sharpN signed hSharpN
  have hMlow : Real.exp (bstar*L)≤(a:ℝ) := by
    calc
      _ ≤ Real.exp (2*bstar*L) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hL,hbpos]
      _ ≤ (a:ℝ) := ha
  have hProxyNorm : ∀m∈K,‖proxyM m/(2:ℂ)‖≤1 := by
    intro m hm
    exact (hProxyL prime a b hMlow m).2
  have hSecondSwapped := hRest hL hFamily0 c e a b Y hc ha hce hExpE hY
    band hBandNow slot secondPrime (fun m => proxyM m/(2:ℂ)) signed
    hProxyNorm
  have hSecond : ‖parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K N proxyM deltaN signed 0 Y‖ ≤
      2*(1+2/Real.log 2)^2*Bound := by
    have hh := parity_original_signed_second_proxy_swapped_half_norm_paid434
      d L Psi K N proxyM deltaN signed 0 Y
      ((1+2/Real.log 2)^2*Bound)
      (by simpa only [d,K,N,deltaN,proxyM,Bound,C1,Cmoment,Cphys,Csource,M_H]
        using hSecondSwapped)
    simpa only [mul_assoc] using hh
  have hFirst' : ‖parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K N deltaM sharpN signed 0 Y‖ ≤
      (1+2/Real.log 2)^2*Bound := by
    simpa only [d,K,N,deltaM,sharpN,Bound,C1,Cmoment,Cphys,Csource,M_H]
      using hFirst
  have hSharpDiffM (m : ℕ) : sharpM m-proxyM m=deltaM m := by
    have h := parity_original_actual_fullcell_proxy_plus_delta_eq_test434
      prime L S gamma a b m
    dsimp only [sharpM,proxyM,deltaM]
    exact (sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm))
  have hSharpDiffN (n : ℕ) : sharpN n-proxyN n=deltaN n := by
    have h := parity_original_actual_fullcell_proxy_plus_delta_eq_test434
      secondPrime L S gamma c e n
    dsimp only [sharpN,proxyN,deltaN]
    exact (sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm))
  have hLedger := parity_original_signed_two_factor_proxy_replacement_norm_ledger434
    d L Psi K N sharpM proxyM sharpN proxyN signed 0 Y
    ((1+2/Real.log 2)^2*Bound) (2*(1+2/Real.log 2)^2*Bound)
    (by simpa only [hSharpDiffM] using hFirst')
    (by simpa only [hSharpDiffN] using hSecond)
  dsimp only [d,K,N,sharpM,sharpN,proxyM,proxyN,Bound,C1,Cmoment,Cphys,Csource,M_H] at hLedger ⊢
  nlinarith [hLedger]
end Green64Analytic.Parity

end

end

