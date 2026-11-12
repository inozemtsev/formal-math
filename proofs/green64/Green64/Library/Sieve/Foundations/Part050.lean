module

public import Green64.Library.Sieve.Foundations.Part046
public import Green64.Library.Sieve.Foundations.Part047
public import Green64.Library.Sieve.Foundations.Part049
public import Green64.Library.Sieve.Foundations.Part045
public import Green64.Library.Sieve.Foundations.Part044
public import Green64.Library.Sieve.Foundations.Part005
public import Green64.Library.Sieve.Foundations.Part012
public import Green64.Library.Sieve.Foundations.Part010

@[expose] public section

/-!
# Sieve / Foundations / Part050

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## UniformQuarterMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option maxRecDepth 32000

/-- Common precision for the original source expression; all local source hypotheses are retained. -/
theorem parity_eventually_original_actual_quarter_fine_postCauchy_OD_anylog_common_precision434
    (jQ : ℕ) (Agoal C0 K0 Cbox A R : ℝ)
    (hAgoal : 0≤Agoal)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (rho U E V : ℝ) (signed : Bool),
          0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
          E=U*L^(-K0) → |rho|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) → 2≤lFine →
          uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let Ybox := Nat.ceil (6*U*V)
        let EF := parityOriginalHistoricalFullOddEEnvelope434 E
        let Jn := parityOriginalHistoricalFullNEnvelope434 V
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
        ‖parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
          d L band slot delta freq rho K EF Jn alpha signed Ybox
          (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw)‖ ≤
          (Cphys+24*C1)*Real.exp L*L^(-Agoal) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
  let CW : ℝ := parityOriginalW1PolylogExponent434
  let Dghost : ℝ := Agoal+K0+200
  let Dmain : ℝ := K0+315+Dghost
  let Cf : ℝ := X+Dmain+2*CW+30
  have hChoose := parity_original_quarter_cauchy_full_ball_precision_compatible434
    Agoal K0 hAgoal hK0
  dsimp only at hChoose
  rcases hChoose with ⟨hDghost,hDmain,hPrecision,hCfmain,hCftail⟩
  have hBall := parity_eventually_original_actual_true_full_psi_physical_ball_any_log_quarter_common_precision434
    jQ Agoal Dmain C0 Cf K0 Cbox A R
    hDmain hPrecision (by simpa only [Cf,X,CW,P] using hCfmain) hK0 hCbox hA hR buf hSmooth hSupport hCube
  have hTail := parity_eventually_original_capfree_Cauchy_OD_full_ball_tail_any_log_quarter434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  obtain ⟨J,B,S,hBS,hBallL⟩ := hBall
  refine ⟨J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hBallL := hBallL beta gamma hbeta hgamma
  have hS : 0<S := by linarith
  have hAlpha := parity_eventually_original_actual_b629_K_fine_alpha_norm_one434
    S beta gamma hS hbeta hgamma
  filter_upwards [hBallL,hTail,hAlpha] with L hMain hTailL hAlphaL
  rcases hMain with ⟨h128,h6,hFamily,hReserved,hRest⟩
  rcases hTailL with ⟨_,_,hTRest⟩
  refine ⟨h128,h6,hFamily,hReserved,?_⟩
  intro hLw hFamily0 band hBand slot delta freq rho U E V signed
    hU hV hUV hUVhi hEscale hrho
    prime lFine uFine a b hFineLow hl hu huExp hDyad
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let Ybox := Nat.ceil (6*U*V)
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let Jn := parityOriginalHistoricalFullNEnvelope434 V
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Ybox K
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Ybox K
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 0
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 1
  let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
  let T : ℝ := L^Cf
  have hEpos : 0<E := by rw [hEscale]; positivity
  have hLbig : 128≤L := h128
  have hCoef : ∀m∈K,‖alpha m‖≤1 := by
    intro m hm
    exact hAlphaL prime lFine uFine hFineLow K m
  have hFull := hRest hLw hFamily0 band hBand slot delta freq rho U E V T signed
    hU hEpos hV hUV hEscale rfl hrho
    prime lFine uFine a b hFineLow hl hu huExp hDyad hUVhi
  have hError := hTRest hLbig U V E hU hV hUV hUVhi hEscale
    band slot delta freq rho K alpha signed 1 (by norm_num) hCoef hDyad
    Dghost hDghost
  let OD : ℂ := parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
    d L band slot delta freq rho K EF Jn alpha signed Ybox
    (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw)
  let Full : ℂ := parityOriginalActualTruePsiGlobalPhysicalBall434
    d L U E V hLw band slot delta freq rho alpha signed Ybox K KS
    (parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG)
    buf (-Real.log A) (Real.log A) T hSmooth hSupport
  have hCfEq : Cf = (X+(K0+89)+(2*CW+256))+Dghost := by
    simpa only [Cf,X,CW,P] using hCftail
  have hNormFull : ‖Full‖ ≤ Cphys*Real.exp L*L^(-Agoal) := by
    simpa only [Full,T,KS,ZG,Ybox,Cphys,Cmoment,C1,alpha,K,d] using hFull
  have hNormError : ‖OD-Full‖ ≤ 24*C1*Real.exp L*L^(-Dghost) := by
    dsimp only [OD,Full,T] at ⊢
    rw [hCfEq]
    simpa only [X,CW,P,KS,ZG,Ybox,EF,Jn,alpha,K,d,C1,
      one_pow,one_mul,mul_one] using hError
  have hPow : L^(-Dghost) ≤ L^(-Agoal) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤L) (by linarith : -Dghost≤-Agoal)
  have hPositive : 0≤24*C1*Real.exp L := by
    have hC1 : 0≤C1 := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
    positivity
  change ‖OD‖ ≤ _
  calc
    ‖OD‖ = ‖(OD-Full)+Full‖ := by ring
    _ ≤ ‖OD-Full‖+‖Full‖ := norm_add_le _ _
    _ ≤ 24*C1*Real.exp L*L^(-Dghost)+Cphys*Real.exp L*L^(-Agoal) :=
      add_le_add hNormError hNormFull
    _ ≤ 24*C1*Real.exp L*L^(-Agoal)+Cphys*Real.exp L*L^(-Agoal) := by
      have hh := mul_le_mul_of_nonneg_left hPow hPositive
      nlinarith [hh]
    _ = _ := by ring

/-- Common precision for the original source expression; all local source hypotheses are retained. -/
theorem parity_eventually_original_actual_quarter_fine_Cauchy_square_common_precision434
    (jQ : ℕ) (Agoal C0 K0 Cbox A R : ℝ)
    (hAgoal : 0≤Agoal)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
          E=U*L^(-K0) → 1≤E → 1≤V →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (rho : ℝ), |rho|≤L^C0 →
        ∀ (a b : ℕ) (Jn : Finset ℕ) (prime : Bool)
          (lFine uFine : ℕ) (betaCoeff : ℕ → ℂ) (signed : Bool),
          Real.exp (beta*L)≤(lFine:ℝ) → 2≤lFine →
          uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
          (∀n∈Jn,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
          (∀n∈Jn,‖betaCoeff n‖≤1) →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
        let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
          (∏ i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length,
            ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
        let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
          d L E band slot delta freq rho K Jn alpha betaCoeff signed
        ‖Bp‖^2 ≤ (6*E*V*AGate^2) *
          (2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
            (Cphys+24*C1)*Real.exp L*L^(-Agoal)) := by
  have hOD := parity_eventually_original_actual_quarter_fine_postCauchy_OD_anylog_common_precision434
    jQ Agoal C0 K0 Cbox A R hAgoal hK0 hCbox
    hA hR buf hSmooth hSupport hOne4 hCube
  have hPre := parity_eventually_original_capfree_Bprime_Cauchy_box_precursor434
    Cbox hCbox
  have hW := parity_eventually_original_actual_cauchy_Wout_EV_all_log434
  have hSpos : ∀ S : ℝ, 2*((0:ℝ)+1)+3<S → 0<S := by intros; linarith
  obtain ⟨J,B,S,hBS,hODL⟩ := hOD
  refine ⟨J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hODL := hODL beta gamma hbeta hgamma
  have hS : 0<S := by linarith
  have hAlpha := parity_eventually_original_actual_b629_K_fine_alpha_norm_one434
    S beta gamma hS hbeta hgamma
  filter_upwards [hODL,hPre,hW,hAlpha] with L hODdata hP hWdata hAlphadata
  rcases hODdata with ⟨h128,h6,hFamily,hReserved,hODrest⟩
  refine ⟨h128,h6,hFamily,hReserved,?_⟩
  intro hLw hFamily0 U V E hU hV hUV hUVhi hE hEone hVone band hBand
    slot delta freq rho hrho a b Jn prime lFine uFine betaCoeff signed
    hlFine hl hu huExp hDyad hJn hBeta
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
    (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 0
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 1
  let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
    d L E band slot delta freq rho K Jn alpha betaCoeff signed
  let Wout := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
    d L E band slot delta, ∑n∈Jn,
      ‖parityOriginalHistoricalWindowAE434 d L E band slot delta freq rho e*betaCoeff n‖^2
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let NFull := parityOriginalHistoricalFullNEnvelope434 V
  let Y := Nat.ceil (6*U*V)
  let hLold : 8≤L := hLw
  let OD := parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
    d L band slot delta freq rho K EF NFull alpha signed Y
    (parityOriginalHistoricalDyadicEtaWeight434 L E V hLold)
  have hCoef : ∀m∈K,‖alpha m‖≤1 := by
    intro m hm
    exact hAlphadata prime lFine uFine hlFine K m
  have hPrec := hP.2.2 hLw U V E hU hV hUVhi (by rw [hE]; positivity)
    band slot delta freq rho K Jn alpha betaCoeff signed 1 hDyad hJn
    (by norm_num) hCoef
  have hODbound := hODrest hLw hFamily0 band hBand slot delta freq rho
    U E V signed hU hV hUV hUVhi hE hrho prime lFine uFine a b
    hlFine hl hu huExp hDyad
  have hWbound := hWdata band slot E V hEone hVone delta freq rho Jn betaCoeff
    (fun n hn => (hJn n hn).2) hBeta
  have hWpos : 0≤Wout := by
    dsimp [Wout]
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hBracket : 0≤2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
      (Cphys+24*C1)*Real.exp L*L^(-Agoal) := by
    have hC0 : 0≤Cmoment := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
    have hC1 : 0≤C1 := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
    have hLog : 0<Real.log 2 := Real.log_pos (by norm_num)
    have hCphys : 0≤Cphys := by dsimp [Cphys]; positivity
    positivity
  have hPre : ‖Bp‖^2 ≤ Wout*(2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)+‖OD‖) := by
    simpa only [Bp,Wout,OD,one_pow,one_mul,mul_one,d,K,alpha,EF,NFull,Y] using hPrec
  have hODEst : ‖OD‖ ≤ (Cphys+24*C1)*Real.exp L*L^(-Agoal) := by
    simpa only [OD,K,alpha,Cphys,C1,d,EF,NFull,Y] using hODbound
  have hWEst : Wout ≤ 6*E*V*AGate^2 := by
    simpa only [Wout,AGate,d] using hWbound
  change ‖Bp‖^2 ≤ _
  calc
    _ ≤ Wout*(2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)+‖OD‖) := hPre
    _ ≤ Wout*(2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)+
        (Cphys+24*C1)*Real.exp L*L^(-Agoal)) :=
      mul_le_mul_of_nonneg_left (add_le_add_right hODEst _) hWpos
    _ ≤ (6*E*V*AGate^2)*(2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)+
        (Cphys+24*C1)*Real.exp L*L^(-Agoal)) :=
      mul_le_mul_of_nonneg_right hWEst hBracket

/-- Common precision for the original source expression; all local source hypotheses are retained. -/
theorem parity_eventually_original_actual_quarter_fine_preCauchy_norm_anylog_common_precision434
    (jQ : ℕ) (Agoal C0 K0 Cbox A R : ℝ)
    (hAgoal : 0≤Agoal)
    (hK0Target : 2*Agoal+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
          E=U*L^(-K0) → 1≤E → 1≤V →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (rho : ℝ), |rho|≤L^C0 →
        ∀ (a b : ℕ) (Jn : Finset ℕ) (prime : Bool)
          (lFine uFine : ℕ) (betaCoeff : ℕ → ℂ) (signed : Bool),
          Real.exp (beta*L)≤(lFine:ℝ) → 2≤lFine →
          uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
          (∀n∈Jn,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
          (∀n∈Jn,‖betaCoeff n‖≤1) →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
        let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
          (∏ i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length,
            ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
        let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
          d L E band slot delta freq rho K Jn alpha betaCoeff signed
        ‖Bp‖ ≤ (1+6*Cbox*(2+Cphys+24*C1))*AGate*Real.exp L*L^(-Agoal) := by
  have hSq := parity_eventually_original_actual_quarter_fine_Cauchy_square_common_precision434
    jQ Agoal C0 K0 Cbox A R hAgoal
    hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  obtain ⟨J,B,S,hBS,hSqL⟩ := hSq
  refine ⟨J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hSqL := hSqL beta gamma hbeta hgamma
  filter_upwards [hSqL] with L hS
  rcases hS with ⟨h128,h6,hFam,hReserved,hRest⟩
  refine ⟨h128,h6,hFam,hReserved,?_⟩
  intro hLw hFamily U V E hU hV hUV hUVhi hEscale hEone hVone
    band hBand slot delta freq rho hrho a b Jn prime lFine uFine
    betaCoeff signed hFine hl hu huExp hDyad hJn hBeta
  classical
  have hSquare := hRest hLw hFamily U V E hU hV hUV hUVhi
    hEscale hEone hVone band hBand slot delta freq rho hrho
    a b Jn prime lFine uFine betaCoeff signed hFine hl hu huExp
    hDyad hJn hBeta
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
    (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
    d L E band slot delta freq rho K Jn alpha betaCoeff signed
  have hEV : E*V ≤ Cbox*Real.exp L*L^(-K0) := by
    rw [hEscale]
    calc
      (U*L^(-K0))*V = (U*V)*L^(-K0) := by ring
      _ ≤ (Cbox*Real.exp L)*L^(-K0) :=
        mul_le_mul_of_nonneg_right hUVhi (Real.rpow_nonneg (by linarith : 0≤L) _)
      _ = _ := by ring
  have hC0 : 0≤Cmoment := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
    A R buf hSmooth hSupport 0 hR
  have hC1 : 0≤C1 := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
    A R buf hSmooth hSupport 1 hR
  have hLog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hCphys : 0≤Cphys := by dsimp [Cphys]; positivity
  have hAGate : 0≤AGate := by
    dsimp [AGate]
    exact mul_nonneg (Real.rpow_nonneg (by linarith : 0≤L) _)
      (Finset.prod_nonneg (by intro i hi; exact norm_nonneg _))
  have hBracket : 0≤2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
      (Cphys+24*C1)*Real.exp L*L^(-Agoal) := by positivity
  have hSquare' : ‖Bp‖^2 ≤ ((6*Cbox*Real.exp L*L^(-K0))*AGate^2)*
      (2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)+
       (Cphys+24*C1)*Real.exp L*L^(-Agoal)) := by
    have hSmaller := (show ‖Bp‖^2 ≤ (6*E*V*AGate^2)*
      (2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)+
       (Cphys+24*C1)*Real.exp L*L^(-Agoal)) from
         (by simpa only [Bp,AGate,Cphys,C1,Cmoment,d,K,alpha] using hSquare))
    have hFactor : 6*E*V*AGate^2 ≤ (6*Cbox*Real.exp L*L^(-K0))*AGate^2 := by
      have hh := mul_le_mul_of_nonneg_right hEV (by positivity : 0≤6*AGate^2)
      nlinarith [hh]
    exact hSmaller.trans (mul_le_mul_of_nonneg_right hFactor hBracket)
  have hNorm := parity_original_actual_cauchy_norm_power_absorption434
    L Agoal K0 parityOriginalW1PolylogExponent434 Agoal Cbox
    (Cphys+24*C1) 0 AGate Bp (by linarith : 1≤L)
    hAgoal parity_original_actual_W1_polylog_exponent_nonneg434
    hAgoal (by linarith : 0≤Cbox) (by positivity) (by positivity) hAGate
    hK0Target (by simpa [mul_assoc] using hSquare')
  dsimp only at hNorm ⊢
  simpa [Bp,Cphys,C1,Cmoment,AGate,zero_mul,add_zero,add_assoc] using hNorm

/-- Common precision for the original source expression; all local source hypotheses are retained. -/
theorem parity_eventually_original_actual_quarter_fine_Bprime_fullQ_positive_anylog_common_precision434
    (jQ : ℕ) (goal target C0 K0 Cbox A R : ℝ)
    (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
          E=U*L^(-K0) → 1≤E → 1≤V →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20) (rho : ℝ), |rho|≤L^C0 →
        ∀ (a b : ℕ) (Jbeta : Finset ℕ) (prime : Bool)
          (lFine uFine : ℕ) (betaCoeff : ℕ → ℂ) (signed : Bool),
          Real.exp (beta*L)≤(lFine:ℝ) → 2≤lFine →
          uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
          (∀n∈Jbeta,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
          (∀n∈Jbeta,‖betaCoeff n‖≤1) →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let nQ := (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length
        let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
        let Csource := 1+6*Cbox*(2+Cphys+24*C1)
        (∑delta : Fin nQ → Bool,
          ∫freq in parityOriginalActualFullQFrequencyCube434 L,
            ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta freq rho K Jbeta alpha betaCoeff signed‖) ≤
          Csource*Real.exp L*L^(-goal) := by
  obtain ⟨J,B,S,hBS,hLocal⟩ :=
    parity_eventually_original_actual_quarter_fine_preCauchy_norm_anylog_common_precision434
      jQ target C0 K0 Cbox A R
      hTarget hK0Target hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube
  refine ⟨J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hLocal := hLocal beta gamma hbeta hgamma
  have hVariation := parity_eventually_original_actual_post_cauchy_Q_gate_L1_polylog434
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+6*Cbox*(2+Cphys+24*C1)
  have hC1 : 0≤C1 := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
    A R buf hSmooth hSupport 1 hR
  have hCmoment : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hLogTwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hCphys : 0≤Cphys := by dsimp [Cphys]; positivity
  have hCsource : 0≤Csource := by dsimp [Csource]; positivity
  filter_upwards [hLocal,hVariation] with L hLocalL hVarL
  rcases hLocalL with ⟨hL32,hL6,hFamily,hReserved,hRest⟩
  refine ⟨hL32,hL6,hFamily,hReserved,?_⟩
  intro hL hFamily0 U V E hU hV hUV hUVhi hEscale hEone hVone
    band hBand slot rho hrho a b Jbeta prime lFine uFine betaCoeff signed
    hFineLow hl hu huExp hDyad hJ hBeta
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let nQ := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let K := Finset.Icc a b
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let sQ := sourceActualSortedFrequencyScales 20 d L band slot
  let F : (Fin nQ → Bool) → (Fin nQ → ℝ) → ℂ := fun delta freq =>
    parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
      d L E band slot delta freq rho K Jbeta alpha betaCoeff signed
  let C0p : ℝ := parityOriginalSelectedECoefficientPolylogExponent434
  let Cfp : ℝ := parityOriginalB590FixedFourierPolynomialExponent434
  let M : ℝ := Csource*L^C0p*Real.exp L*L^(-target)
  have hLp : 0<L := by linarith
  have hLone : (1:ℝ)≤L := by linarith
  have hM : 0≤M := by dsimp [M]; positivity
  have hMeas : ∀delta,AEStronglyMeasurable (F delta) := by
    intro delta
    exact (parity_original_capfree_Bprime_Q_frequency_continuous434
      d L E band slot delta rho K Jbeta alpha betaCoeff signed).aestronglyMeasurable
  have hPoint : ∀delta freq, freq∈parityOriginalActualFullQFrequencyCube434 L →
      ‖F delta freq‖≤M*‖parityOriginalActualPostCauchyQGate434 E sQ freq delta‖ := by
    intro delta freq hfreq
    have hLw : 8≤L := by linarith
    have hSingle := hRest hLw hFamily0 U V E hU hV hUV hUVhi
      hEscale hEone hVone band hBand slot delta freq rho hrho a b
      Jbeta prime lFine uFine betaCoeff signed
      hFineLow hl hu huExp hDyad hJ hBeta
    dsimp only at hSingle
    have hGate := parity_original_actual_post_cauchy_Q_gate_norm434 E sQ freq delta
    dsimp only [F,M,C0p,sQ]
    calc
      _ ≤ Csource*(L^parityOriginalSelectedECoefficientPolylogExponent434 *
        (∏i : Fin nQ,
          ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)) *
          Real.exp L*L^(-target) := by
            simpa only [Csource,Cphys,C1,Cmoment,F,d,K,alpha,nQ] using hSingle
      _ = _ := by rw [hGate]; ring
  have hIntegral := parity_original_actual_Bprime_fullQ_gate_dominated_positive_integral434
    E L M sQ hM F hMeas hPoint
  have hVar := hVarL band slot E
  have hBound := hIntegral.trans (mul_le_mul_of_nonneg_left hVar hM)
  have hExponent : C0p+Cfp-target≤-goal := by
    dsimp [C0p,Cfp]
    linarith
  have hPower : L^C0p*L^(-target)*L^Cfp=L^(C0p+Cfp-target) := by
    rw [←Real.rpow_add hLp,←Real.rpow_add hLp]
    congr 1
    ring
  have hAbsorb : L^(C0p+Cfp-target)≤L^(-goal) :=
    Real.rpow_le_rpow_of_exponent_le hLone hExponent
  have hCoef : 0≤Csource*Real.exp L := by positivity
  dsimp only at hIntegral hBound ⊢
  calc
    _ ≤ M*L^Cfp := by simpa only [Cfp,d,nQ,sQ,F] using hBound
    _ = (Csource*Real.exp L)*(L^C0p*L^(-target)*L^Cfp) := by dsimp [M]; ring
    _ = (Csource*Real.exp L)*L^(C0p+Cfp-target) := by rw [hPower]
    _ ≤ (Csource*Real.exp L)*L^(-goal) :=
      mul_le_mul_of_nonneg_left hAbsorb hCoef
    _ = Csource*Real.exp L*L^(-goal) := by ring

/-- Common precision for the original source expression; all local source hypotheses are retained. -/
theorem parity_eventually_original_actual_quarter_b629_single_slot_restricted_Psi_Mellin_Q_anylog_common_precision434
    (jQ : ℕ) (goal target C0 K0 Cbox A R : ℝ)
    (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
          E=U*L^(-K0) → 1≤E → 1≤V →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (a b : ℕ) (Jbeta : Finset ℕ) (prime : Bool)
          (betaCoeff : ℕ → ℂ) (signed : Bool),
          Real.exp (beta*L)≤(a:ℝ) → 2≤a →
          b≤2*a → (b:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
          (∀n∈Jbeta,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
          (∀n∈Jbeta,‖betaCoeff n‖≤1) →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma a b)
        let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
        let Csource := 1+6*Cbox*(2+Cphys+24*C1)
        let R_M : ℝ := L^C0/(2*Real.pi)
        ‖∫s in Set.Icc (-R_M) R_M,
          parityOriginalSignedWindowPsiMellinKernel434
            L Psi hPsiSmooth hPsiSupport s *
            (∑delta : Fin (sourceOrderedLabels 20
                (sourceActualSortedScales 20 d L) band slot).length → Bool,
                ∫freq in parityOriginalActualFullQFrequencyCube434 L,
                  parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                    d L E band slot delta freq (2*Real.pi*s)
                    K Jbeta alpha betaCoeff signed)‖ ≤
          (Csource*Real.exp L*L^(-goal)) *
            (∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) := by
  obtain ⟨J,B,S,hBS,hOne⟩ :=
    parity_eventually_original_actual_quarter_fine_Bprime_fullQ_positive_anylog_common_precision434
      jQ goal target C0 K0 Cbox A R
      hTarget hK0Target hPrecision hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube
  refine ⟨J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hOne := hOne beta gamma hbeta hgamma
  filter_upwards [hOne,parity_eventually_original_cartesian_selected_e_odd_unit434]
    with L hOneL hOdd
  rcases hOneL with ⟨hL32,hL6,hFam,hReserved,hOneRest⟩
  refine ⟨hL32,hL6,hFam,hReserved,?_⟩
  intro hL hFamily U V E hU hV hUV hUVhi hEscale hEone hVone
    band hb slot a b Jbeta prime betaCoeff signed
    hFineLow hTwo hUpper hExp hDyad hJ hBeta
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma a b)
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+6*Cbox*(2+Cphys+24*C1)
  have hSelected :
      ∀(delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool),
        ∀e∈parityOriginalHistoricalCauchyActiveESupport434
          d L E band slot delta,0<e := by
    intro delta e he
    exact (hOdd.2 band slot delta e (Finset.mem_filter.mp he).1).2.1
  have hK : ∀m∈K,(m:ℝ)≤2*U := by
    intro m hm
    exact (hDyad m hm).2.le
  have hN : ∀n∈Jbeta,(n:ℝ)≤3*V := by
    intro n hn
    have hn2 := (hJ n hn).2
    linarith
  have hC1 := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
    A R buf hSmooth hSupport 1 hR
  have hC0 := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
    A R buf hSmooth hSupport 0 hR
  have hLogTwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0≤Csource*Real.exp L*L^(-goal) := by
    dsimp [Csource,Cphys,C1,Cmoment]
    positivity
  have hPositive (rho : ℝ) (hrho : |rho|≤L^C0) :
      (∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫freq in parityOriginalActualFullQFrequencyCube434 L,
          ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
            d L E band slot delta freq rho K Jbeta alpha betaCoeff signed‖) ≤
        Csource*Real.exp L*L^(-goal) := by
    have h := hOneRest hL hFamily U V E hU hV hUV hUVhi hEscale hEone hVone
      band hb slot rho hrho a b Jbeta prime a b betaCoeff signed
      hFineLow hTwo hUpper hExp hDyad hJ hBeta
    simpa only [d,K,alpha,C1,Cmoment,Cphys,Csource] using h
  have hBound := parity_original_actual_capfree_single_slot_restricted_Psi_Mellin_L1_bound434
    d L E U V C0 L (Csource*Real.exp L*L^(-goal))
    (by linarith : 0<L) rfl hU.le hV.le hC band slot hSelected
    K Jbeta alpha betaCoeff signed hK hN
    Psi hPsiSmooth hPsiSupport hPositive
  simpa only [d,K,alpha,C1,Cmoment,Cphys,Csource] using hBound

/-- Common precision for the original source expression; all local source hypotheses are retained. -/
theorem parity_eventually_original_actual_quarter_b629_single_slot_full_Psi_Mellin_Q_anylog_common_precision434
    (jQ : ℕ) (goal target C0 K0 Cbox A R : ℝ)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ∃ H : ℕ, ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
          E=U*L^(-K0) → 1≤E → 1≤V →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (a b : ℕ) (Jbeta : Finset ℕ) (prime : Bool)
          (betaCoeff : ℕ → ℂ) (signed : Bool),
          Real.exp (beta*L)≤(a:ℝ) → 2≤a →
          b≤2*a → (b:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
          (∀n∈Jbeta,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
          (∀n∈Jbeta,‖betaCoeff n‖≤1) →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma a b)
        let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
        let Csource := 1+6*Cbox*(2+Cphys+24*C1)
        let R_M : ℝ := L^C0/(2*Real.pi)
        let M_H := ∫s : ℝ, ‖s‖^H *
          ‖(𝓕 (parityOriginalLogCutoff434
            (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
        ‖∫s : ℝ,
          parityOriginalSignedWindowPsiMellinKernel434
            L Psi hPsiSmooth hPsiSupport s *
            (∑delta : Fin (sourceOrderedLabels 20
                (sourceActualSortedScales 20 d L) band slot).length → Bool,
                ∫freq in parityOriginalActualFullQFrequencyCube434 L,
                  parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                    d L E band slot delta freq (2*Real.pi*s)
                    K Jbeta alpha betaCoeff signed)‖ ≤
          (Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
           20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
  obtain ⟨H,hHigh⟩ :=
    parity_eventually_original_true_Ybox_capfree_single_slot_high_anylog_noUVlower434
      Cbox goal C0 hCbox hC0 Psi hPsiSmooth hPsiSupport
  obtain ⟨J,B,S,hBS,hLow⟩ :=
    parity_eventually_original_actual_quarter_b629_single_slot_restricted_Psi_Mellin_Q_anylog_common_precision434
      jQ goal target C0 K0 Cbox A R
      hTarget hK0Target hPrecision hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube Psi hPsiSmooth hPsiSupport
  refine ⟨H,J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hLow := hLow beta gamma hbeta hgamma
  have hSpos : 0<S := by
    have hh : (0:ℝ)≤(B:ℝ) := Nat.cast_nonneg _
    linarith [hBS]
  filter_upwards [hLow,hHigh,
      parity_eventually_original_actual_b629_K_fine_alpha_norm_one434
        S beta gamma hSpos hbeta hgamma,
      parity_eventually_original_cartesian_selected_e_odd_unit434]
    with L hLowL hHighL hAlphaL hOdd
  rcases hLowL with ⟨hL32,hL6,hFamily,hReserved,hLowRest⟩
  rcases hHighL with ⟨hLone,hHighRest⟩
  refine ⟨hL32,hL6,hFamily,hReserved,?_⟩
  intro hL hFamily0 U V E hU hV hUV hUVhi hEscale hEone hVone
    band hBand slot a b Jbeta prime betaCoeff signed
    hFineLow hTwo hUpper hExp hDyad hJ hBeta
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma a b)
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+6*Cbox*(2+Cphys+24*C1)
  let R_M : ℝ := L^C0/(2*Real.pi)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let M0 := ∫s : ℝ,
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let Dlow : ℝ := (Csource*Real.exp L*L^(-goal))*M0
  let Dhigh : ℝ := (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
  have hLp : 0<L := by linarith
  have hSelected :
      ∀(delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool),
        ∀e∈parityOriginalHistoricalCauchyActiveESupport434
          d L E band slot delta,0<e := by
    intro delta e he
    exact (hOdd.2 band slot delta e (Finset.mem_filter.mp he).1).2.1
  have hK : ∀m∈K,(m:ℝ)≤2*U := by
    intro m hm
    exact (hDyad m hm).2.le
  have hN : ∀n∈Jbeta,(n:ℝ)≤3*V := by
    intro n hn
    have hN2 := (hJ n hn).2
    linarith
  have hAlpha : ∀m∈K,‖alpha m‖≤1 := by
    intro m hm
    have hPoint := hAlphaL prime a b hFineLow K m
    simpa only [alpha,restrictSequence,if_pos hm] using hPoint
  have hLowBound := hLowRest hL hFamily0 U V E hU hV hUV hUVhi
    hEscale hEone hVone band hBand slot a b Jbeta prime betaCoeff signed
    hFineLow hTwo hUpper hExp hDyad hJ hBeta
  have hHighBound := hHighRest U V hU hV hUVhi E signed band slot
    K Jbeta alpha betaCoeff hSelected hK hN hAlpha hBeta
  have hRm : 0≤R_M := by
    dsimp [R_M]
    exact div_nonneg (Real.rpow_nonneg hLp.le _) (by positivity)
  have hSource := parity_original_actual_capfree_single_slot_full_Psi_Mellin_from_low_high434
    d L E U V hLp rfl hU.le hV.le band slot hSelected K Jbeta hK hN
    alpha betaCoeff signed hAlpha hBeta Psi hPsiSmooth hPsiSupport
    L R_M Dlow Dhigh hRm
    (by simpa only [Dlow,M0,d,K,alpha,C1,Cmoment,Cphys,Csource,R_M]
        using hLowBound)
    (by simpa only [Dhigh,M_H,d,K,alpha,R_M]
        using hHighBound)
  dsimp only at hSource ⊢
  calc
    _ ≤ Dlow+Dhigh := by
      simpa only [d,K,alpha,R_M,M_H,C1,Cmoment,Cphys,Csource] using hSource
    _ = (Csource*M0+20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
      dsimp [Dlow,Dhigh]
      ring
    _ = _ := by rfl

/-- Common precision for the original source expression; all local source hypotheses are retained. -/
theorem parity_eventually_original_signed_quarter_b629_fine_one_slot_Psi_Mellin_source_anylog_common_precision434
    (jQ : ℕ) (goal target C0 betaP K0 Cbox A R : ℝ)
    (hbetaP : 0<betaP)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
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
    ∃ H : ℕ, ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
          E=U*L^(-K0) → 1≤E →
          E≤Real.exp ((1-betaP)*L) → 1≤V →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (a b : ℕ) (Jbeta : Finset ℕ) (prime : Bool)
          (betaCoeff : ℕ → ℂ) (signed : Bool),
          Real.exp (beta*L)≤(a:ℝ) → 2≤a →
          b≤2*a → (b:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
          (∀n∈Jbeta,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
          (∀n∈Jbeta,‖betaCoeff n‖≤1) →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma a b)
        let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
        let Csource := 1+6*Cbox*(2+Cphys+24*C1)
        let M_H := ∫s : ℝ, ‖s‖^H *
          ‖(𝓕 (parityOriginalLogCutoff434
            (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
        ‖parityOriginalShiftTwoSignedBilinearMellinSource434
            d L Psi K Jbeta alpha betaCoeff signed 0 ⌊2*Real.exp L⌋₊‖ ≤
          (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
           20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
  obtain ⟨H,J,B,S,hBS,hFull⟩ :=
    parity_eventually_original_actual_quarter_b629_single_slot_full_Psi_Mellin_Q_anylog_common_precision434
      jQ goal target C0 K0 Cbox A R
      hC0 hTarget hK0Target hPrecision hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube Psi hPsiSmooth hPsiSupport
  refine ⟨H,J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hFull := hFull beta gamma hbeta hgamma
  have hSpos : 0<S := by
    have hh : (0:ℝ)≤(B:ℝ) := Nat.cast_nonneg _
    linarith [hBS]
  filter_upwards [hFull,
      parity_eventually_original_signed_source_to_actual_capfree_Psi_Mellin_Bprime_quarter434
        betaP goal hbetaP jQ hBand,
      parity_eventually_original_actual_b629_K_fine_alpha_norm_one434
        S beta gamma hSpos hbeta hgamma,
      parity_eventually_original_cartesian_selected_e_odd_unit434,
      eventually_ge_atTop ((3:ℝ)^16)]
    with L hFullL hSourceL hAlphaL hOdd hBig
  rcases hFullL with ⟨hL32,hL6,hFam,hReserved,hFullRest⟩
  rcases hSourceL with ⟨hSourceBig,hSourceReserved,hSourceRest⟩
  refine ⟨hBig,hL32,hL6,hFam,hReserved,?_⟩
  intro hL hFamily U V E hU hV hUV hUVhi hEscale hEone hEupper hVone
    band hBandSlot slot a b Jbeta prime betaCoeff signed
    hFineLow hTwo hUpper hExp hDyad hJ hBeta
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma a b)
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+6*Cbox*(2+Cphys+24*C1)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let M0 := ∫s : ℝ,
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let X : ℂ := parityOriginalShiftTwoSignedBilinearMellinSource434
    d L Psi K Jbeta alpha betaCoeff signed 0 ⌊2*Real.exp L⌋₊
  let Z : ℂ := parityOriginalActualPsiMellinCapfreeBprimeQBox434
    d L E band slot Psi hPsiSmooth hPsiSupport K Jbeta alpha betaCoeff signed L
  have hLp : 0<L := by linarith
  have hSelected :
      ∀(delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool),
        ∀e∈parityOriginalHistoricalCauchyActiveESupport434
          d L E band slot delta,0<e := by
    intro delta e he
    exact (hOdd.2 band slot delta e (Finset.mem_filter.mp he).1).2.1
  have hK : ∀m∈K,(m:ℝ)≤2*U := by
    intro m hm
    exact (hDyad m hm).2.le
  have hN : ∀n∈Jbeta,(n:ℝ)≤3*V := by
    intro n hn
    have hh := (hJ n hn).2
    linarith
  have hAlpha : ∀m∈K,‖alpha m‖≤1 := by
    intro m hm
    have hPoint := hAlphaL prime a b hFineLow K m
    simpa only [alpha,restrictSequence,if_pos hm] using hPoint
  have hFullBound := hFullRest hL hFamily U V E hU hV hUV hUVhi
    hEscale hEone hVone band hBandSlot slot a b Jbeta prime betaCoeff signed
    hFineLow hTwo hUpper hExp hDyad hJ hBeta
  have hFubini := parity_original_actual_capfree_single_slot_full_Psi_Mellin_Q_swap434
    d L E U V hLp rfl hU.le hV.le band slot hSelected K Jbeta hK hN
    alpha betaCoeff signed hAlpha hBeta Psi hPsiSmooth hPsiSupport L
  have hZ : ‖Z‖≤ (Csource*M0+20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
    change ‖parityOriginalActualPsiMellinCapfreeBprimeQBox434
      d L E band slot Psi hPsiSmooth hPsiSupport K Jbeta alpha betaCoeff signed L‖ ≤
      (Csource*M0+20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
    rw [hFubini]
    simpa only [d,K,alpha,C1,Cmoment,Cphys,Csource,M_H,M0] using hFullBound
  have hCmp := hSourceRest band hBandSlot E U V hEone hEupper
    hU hV hUV Psi hPsiSet hPsiSmooth hPsiPos hPsiLe
    slot K Jbeta alpha betaCoeff 1 1
    (by norm_num) (by norm_num) hAlpha hBeta
    (by intro m hm; exact (hDyad m hm).2)
    (by intro n hn; exact (hJ n hn).2) signed
  have hXZ : ‖X-Z‖≤4*Real.exp L*L^(-goal) := by
    simpa only [X,Z,d,K,alpha,one_mul,mul_one] using hCmp
  have hTri : ‖X‖≤‖X-Z‖+‖Z‖ := by
    have hh := norm_add_le (X-Z) Z
    simpa only [sub_add_cancel] using hh
  calc
    _ ≤ ‖X-Z‖+‖Z‖ := hTri
    _ ≤ 4*Real.exp L*L^(-goal)+
       (Csource*M0+20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) :=
        add_le_add hXZ hZ
    _ = (4+Csource*M0+20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by ring

end Green64Analytic.Parity

end

end

/-! ## OriginalRectangleStages -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Literal original physical quarter dyads for a rectangle. The carrier is independent
of sharp tests, proxy values, factor orientations and parity signs. -/
def parityOriginalSourceRectangleDyads434 (L : ℝ) (a b c e Y : ℕ) : Finset (ℕ×ℕ) :=
  (parityOriginalActualTypeIIDyadicPairScales434
    (parityOriginalTypeIIPhysicalPairs434 (Finset.Icc a b) (Finset.Icc c e) Y)).filter
      (parityOriginalTypeIIQuarterProductGate434 L)

/-- A choice of an already defined full-cell coefficient; the normalization is never
recomputed on a bin or a dyadic cut. -/
def parityOriginalFullCellCoefficient434
    (proxy prime : Bool) (L S gamma : ℝ) (a b : ℕ) : ℕ → ℂ :=
  if proxy then parityOriginalActualFullCellProxyBeta434 prime L S gamma a b
    else parityOriginalActualFullCellSharpTest434 prime L gamma a b

/-- An actual stage of the original Parity source, including both factor orders. -/
def parityOriginalFullCellPairStage434
    (proxyM proxyN primeM primeN : Bool)
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (S gammaM gammaN : ℝ)
    (a b c e Y : ℕ) : ℂ :=
  parityOriginalParityBilinearSource434 d L rho Psi (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalFullCellCoefficient434 proxyM primeM L S gammaM a b)
    (parityOriginalFullCellCoefficient434 proxyN primeN L S gammaN c e) Y

theorem parity_original_parity_source_coeff_congr434
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (K J : Finset ℕ)
    (alpha beta alpha' beta' : ℕ → ℂ) (Y : ℕ)
    (hAlpha : ∀m∈K,alpha m=alpha' m) (hBeta : ∀n∈J,beta n=beta' n) :
    parityOriginalParityBilinearSource434 d L rho Psi K J alpha beta Y =
      parityOriginalParityBilinearSource434 d L rho Psi K J alpha' beta' Y := by
  unfold parityOriginalParityBilinearSource434
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  have hprod := (Finset.mem_filter.mp hz).1
  obtain ⟨hm,hn⟩ := Finset.mem_product.mp hprod
  rw [hAlpha z.1 hm,hBeta z.2 hn]

/-- Both genuine parity projections inherit the exact signed quarter-source identity. -/
theorem parity_original_parity_positive_Icc_eq_quarter_nested_sources434
    (d : ℕ) (L rho : ℝ) (hL : 0<L) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (a b c e Y : ℕ) (ha : 0<a) (hc : 0<c) (alpha beta : ℕ → ℂ) :
    parityOriginalParityBilinearSource434 d L rho Psi
      (Finset.Icc a b) (Finset.Icc c e) alpha beta Y =
    ∑ scale ∈ parityOriginalSourceRectangleDyads434 L a b c e Y,
      parityOriginalParityBilinearSource434 d L rho Psi
        (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
        (Finset.Icc (max c scale.2) (min e (2*scale.2-1))) alpha beta Y := by
  rw [parity_original_parity_bilinear_eq_signed_mellin_projection434 d L rho hL]
  rw [parity_original_signed_positive_Icc_eq_quarter_nested_sources434
    d L Psi hL.le hPsi a b c e Y ha hc alpha beta false 0,
    parity_original_signed_positive_Icc_eq_quarter_nested_sources434
    d L Psi hL.le hPsi a b c e Y ha hc alpha beta true 0]
  rw [Finset.mul_sum,←Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro scale hs
  exact (parity_original_parity_bilinear_eq_signed_mellin_projection434
    d L rho hL Psi _ _ alpha beta Y).symm

/-- On an actual nested interval the full-cell value stays the same. This proves
transport for sharp and nonsmooth proxy values separately from geometry. -/
theorem parity_original_fullcell_coefficient_nested_eq434
    (proxy prime : Bool) (L S gamma : ℝ) (a b a' b' n : ℕ)
    (ha : a≤a') (hb : b'≤b) (hn : n∈Finset.Icc a' b') :
    parityOriginalFullCellCoefficient434 proxy prime L S gamma a b n =
      parityOriginalFullCellCoefficient434 proxy prime L S gamma a' b' n := by
  have hOuter : n∈Finset.Icc a b :=
    Finset.mem_Icc.mpr ⟨ha.trans (Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans hb⟩
  cases proxy <;> simp [parityOriginalFullCellCoefficient434,parityOriginalActualFullCellProxyBeta434,
    parityOriginalActualFullCellSharpTest434,hn,hOuter]

/-- Every sharp/proxy stage is reconstructed over the SAME actual physical quarter
family, including terms introduced by a proxy where a sharp test vanishes. -/
theorem parity_original_fullcell_pair_stage_eq_quarter_cuts434
    (proxyM proxyN primeM primeN : Bool)
    (d : ℕ) (L rho : ℝ) (hL : 0<L) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (S gammaM gammaN : ℝ) (a b c e Y : ℕ) (ha : 0<a) (hc : 0<c) :
    parityOriginalFullCellPairStage434 proxyM proxyN primeM primeN
      d L rho Psi S gammaM gammaN a b c e Y =
    ∑ scale ∈ parityOriginalSourceRectangleDyads434 L a b c e Y,
      parityOriginalFullCellPairStage434 proxyM proxyN primeM primeN
        d L rho Psi S gammaM gammaN
        (max a scale.1) (min b (2*scale.1-1))
        (max c scale.2) (min e (2*scale.2-1)) Y := by
  unfold parityOriginalFullCellPairStage434
  rw [parity_original_parity_positive_Icc_eq_quarter_nested_sources434
    d L rho hL Psi hPsi a b c e Y ha hc]
  apply Finset.sum_congr rfl
  intro scale hs
  apply parity_original_parity_source_coeff_congr434
  · intro m hm
    exact parity_original_fullcell_coefficient_nested_eq434
      proxyM primeM L S gammaM a b _ _ m (le_max_left _ _) (min_le_left _ _) hm
  · intro n hn
    exact parity_original_fullcell_coefficient_nested_eq434
      proxyN primeN L S gammaN c e _ _ n (le_max_left _ _) (min_le_left _ _) hn

/-- Explicit number of distinct source dyads in every stage of one actual rectangle. -/
theorem parity_original_source_rectangle_dyads_card434
    (L : ℝ) (a b c e Y : ℕ) :
    (parityOriginalSourceRectangleDyads434 L a b c e Y).card ≤
      (Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1) := by
  exact parity_original_actual_quarter_Icc_dyadic_card_le_log_sq434 a b c e Y L

/-- Finite norm summation on actual source differences. The analytic premise here is
discharged by the common-precision theorem in the following production module. -/
theorem parity_original_fullcell_pair_difference_sum_bound434
    (proxyM proxyN proxyM' proxyN' primeM primeN : Bool)
    (d : ℕ) (L rho : ℝ) (hL : 0<L) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (S gammaM gammaN : ℝ) (a b c e Y : ℕ) (ha : 0<a) (hc : 0<c)
    (M : ℝ)
    (hEach : ∀ scale ∈ parityOriginalSourceRectangleDyads434 L a b c e Y,
      ‖parityOriginalFullCellPairStage434 proxyM proxyN primeM primeN
          d L rho Psi S gammaM gammaN
          (max a scale.1) (min b (2*scale.1-1)) (max c scale.2) (min e (2*scale.2-1)) Y -
        parityOriginalFullCellPairStage434 proxyM' proxyN' primeM primeN
          d L rho Psi S gammaM gammaN
          (max a scale.1) (min b (2*scale.1-1)) (max c scale.2) (min e (2*scale.2-1)) Y‖ ≤ M) :
    ‖parityOriginalFullCellPairStage434 proxyM proxyN primeM primeN
        d L rho Psi S gammaM gammaN a b c e Y -
      parityOriginalFullCellPairStage434 proxyM' proxyN' primeM primeN
        d L rho Psi S gammaM gammaN a b c e Y‖ ≤
      ((parityOriginalSourceRectangleDyads434 L a b c e Y).card:ℝ)*M := by
  rw [parity_original_fullcell_pair_stage_eq_quarter_cuts434
    proxyM proxyN primeM primeN d L rho hL Psi hPsi S gammaM gammaN a b c e Y ha hc,
    parity_original_fullcell_pair_stage_eq_quarter_cuts434
    proxyM' proxyN' primeM primeN d L rho hL Psi hPsi S gammaM gammaN a b c e Y ha hc,
    ←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ scale ∈ parityOriginalSourceRectangleDyads434 L a b c e Y,
      ‖parityOriginalFullCellPairStage434 proxyM proxyN primeM primeN
          d L rho Psi S gammaM gammaN
          (max a scale.1) (min b (2*scale.1-1)) (max c scale.2) (min e (2*scale.2-1)) Y -
        parityOriginalFullCellPairStage434 proxyM' proxyN' primeM primeN
          d L rho Psi S gammaM gammaN
          (max a scale.1) (min b (2*scale.1-1)) (max c scale.2) (min e (2*scale.2-1)) Y‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _scale ∈ parityOriginalSourceRectangleDyads434 L a b c e Y, M :=
      Finset.sum_le_sum hEach
    _ = _ := by simp
end Green64Analytic.Parity

end

end

/-! ## BothParityMass221 -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 6000000

theorem parity_original_actual_parity_XA_lower_221434 (parityFlag : Bool)
    (α β c : ℝ) (Ψ : ℝ → ℝ) (hΨzero : Ψ 0 = 0)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2) (hc : 0 < c)
    (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    0 < sourceOriginalXAFixedConstant 20 α β c ∧
    ∀ᶠ L : ℝ in atTop,
      sourceOriginalXAFixedConstant 20 α β c * Real.exp L / L ^ (221:ℝ) ≤
        parityOriginalParityXA434 parityFlag 20
          (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
          (sourceOriginalPAllActualBands 20 L) (Real.exp L) Ψ := by
  let K := sourceOriginalXAFixedConstant 20 α β c
  have hK : 0 < K := source_original_XA_fixed_constant_pos
    20 (by norm_num) α β c hα hαβ hc
  refine ⟨hK, ?_⟩
  filter_upwards [parity_original_XA_literal_depth_lower_eventually_parity434 parityFlag
      20 (by norm_num) α β c Ψ hΨzero hα hαβ hβ hc hΨnonneg hΨ,
    b635_parity_actual_HQ_lower_220434, b635_actual_HP_one_le434 20,
    eventually_gt_atTop (0:ℝ)] with L hXA hQ hP hL
  let HQ := sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L
  let HP := sourceLiteralHP (sourceOriginalPAllActualBands 20 L)
  have hHQ : 0 ≤ HQ := (Real.rpow_pos_of_pos hL (-220:ℝ)).le.trans hQ
  have hQHP : L ^ (-220:ℝ) ≤ HQ*HP := by
    calc
      L ^ (-220:ℝ) ≤ HQ := hQ
      _ = HQ*1 := by ring
      _ ≤ HQ*HP := mul_le_mul_of_nonneg_left hP hHQ
  have hEq : K * Real.exp L / L ^ (221:ℝ) =
      K * (Real.exp L/L) * L ^ (-220:ℝ) := by
    have hPow : L ^ (221:ℝ) = L * L ^ (220:ℝ) := by
      rw [show (221:ℝ) = 1+220 by norm_num, Real.rpow_add hL,
        Real.rpow_one]
    rw [hPow, Real.rpow_neg hL.le]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  calc
    K * Real.exp L / L ^ (221:ℝ) =
        K * (Real.exp L/L) * L ^ (-220:ℝ) := hEq
    _ ≤ K * (Real.exp L/L) * (HQ*HP) :=
      mul_le_mul_of_nonneg_left hQHP (by positivity)
    _ ≤ parityOriginalParityXA434 parityFlag 20
          (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
          (sourceOriginalPAllActualBands 20 L) (Real.exp L) Ψ := hXA
end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve

/-- The literal Parity X_rho for r0=20, with exact source depth, A_rho,
the original compact cutoff and the complete finite u<=floor(2 exp L) sum. -/
def localizedMass (Psi : ℝ → ℝ) (rho L : ℝ) : ℝ :=
  ∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
    parityWeight (sourceOriginalLiteralDepth 20 L) L rho u *
      Psi ((u:ℝ)/Real.exp L)

/-- Pointwise source definitions give an exact finite-sum identity.
No mass estimate or asserted aggregate equality is used. -/
theorem parity_original_parity_XA_eq_Xrho434
    (parityFlag : Bool) (Psi : ℝ → ℝ) (L : ℝ) :
    parityOriginalParityXA434 parityFlag 20
      (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
      (sourceOriginalPAllActualBands 20 L) (Real.exp L) Psi =
    localizedMass Psi (parityOriginalParitySign434 parityFlag) L := by
  rfl

theorem parity_original_minus_Xrho_eq_original_XA434
    (Psi : ℝ → ℝ) (L : ℝ) :
    localizedMass Psi (-1) L =
      sourceOriginalXA 20
        (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
        (sourceOriginalPAllActualBands 20 L) (Real.exp L) Psi := by
  unfold localizedMass sourceOriginalXA
  simp only [parity_original_minus_parity_A_eq_original_A434]

/-- Genuine original mass (Parity1.9) for BOTH Liouville parity projections.
The single positive constant and the eventual threshold are shared by rho=±1.
The proof retains the actual infinite W1 law and every original Q factorial.
No TypeII, assumed lower mass, sieve, or prime-extraction hypothesis occurs. -/
theorem localizedMass_lower_bound
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t)
    (hInterior : ∃ t : ℝ, 1 < t ∧ t < 2 ∧ 0 < Psi t) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ᶠ L : ℝ in atTop,
      ∀ rho : ℝ, (rho=1 ∨ rho=-1) →
        c0*Real.exp L*L^(-221:ℝ) ≤ localizedMass Psi rho L := by
  have hPsi0 : Psi 0 = 0 := by
    by_contra hz
    have h := hSupport (show (0:ℝ) ∈ Function.support Psi from hz)
    norm_num at h
  obtain ⟨α,β,c,hα,hαβ,hβ,hc,hPsi⟩ :=
    b635_original_cutoff_positive_interval434 Psi hCont hInterior
  have hFalse := parity_original_actual_parity_XA_lower_221434
    false α β c Psi hPsi0 hα hαβ hβ hc hNonneg hPsi
  have hTrue := parity_original_actual_parity_XA_lower_221434
    true α β c Psi hPsi0 hα hαβ hβ hc hNonneg hPsi
  refine ⟨sourceOriginalXAFixedConstant 20 α β c,hFalse.1,?_⟩
  filter_upwards [hFalse.2,hTrue.2,eventually_gt_atTop (0:ℝ)] with L hF hT hL
  intro rho hRho
  have hScale : sourceOriginalXAFixedConstant 20 α β c *
      Real.exp L * L^(-221:ℝ) =
      sourceOriginalXAFixedConstant 20 α β c * Real.exp L / L^(221:ℝ) := by
    rw [Real.rpow_neg hL.le]
    ring
  rw [hScale]
  rw [parity_original_parity_XA_eq_Xrho434] at hF hT
  rcases hRho with rfl | rfl
  · simpa only [parityOriginalParitySign434,ite_true] using hT
  · simpa only [parityOriginalParitySign434,Bool.false_eq_true,ite_false] using hF
end Green64Analytic.Parity

end

end

/-! ## BothParitySourceCandidates -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 6000000

/-- Positive original A_rho has exactly its asserted Liouville sign.
The source P exponent is the sum of prime-factor multiplicities; all
ordinary Q bands have twenty slots, including repeats. -/
theorem parity_original_positive_parity_source_liouville434
    (d : ℕ) (L rho : ℝ) (u : ℕ)
    (hRho : rho=1 ∨ rho=-1) (hu : u≠0)
    (hA : 0<parityWeight d L rho u) :
    (ArithmeticFunction.liouville u : ℝ) = rho := by
  let Q := sourceOriginalQActualBands 20 d L
  let P := sourceOriginalPAllActualBands 20 L
  have hCoeff : sourceOriginalOrdinaryCoefficient 20 Q
      (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u) ≠ 0 := by
    intro hz
    have hZero : parityWeight d L rho u = 0 := by
      unfold parityWeight sourceOriginalA0
      change _ * sourceOriginalOrdinaryCoefficient 20 Q
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u) * _ = 0
      rw [hz]
      ring
    linarith
  have hLiouville := b628_parity_liouville_equals_P_phase434
    Q P u hu (source_original_Q_actual_prime 20 d L) hCoeff
  have hPhase : (-1:ℝ)^sourceOriginalPParityExponent
      (Finset.univ.biUnion P) u = rho := by
    rcases Nat.even_or_odd (sourceOriginalPParityExponent
      (Finset.univ.biUnion P) u) with he | ho
    · rw [he.neg_one_pow]
      rcases hRho with rfl | rfl
      · rfl
      · have hZero : parityWeight d L (-1) u = 0 := by
          unfold parityWeight
          change _ * ((1+(-1:ℝ)*(-1:ℝ)^sourceOriginalPParityExponent
            (Finset.univ.biUnion P) u)/2) = 0
          rw [he.neg_one_pow]
          ring
        linarith
    · rw [ho.neg_one_pow]
      rcases hRho with rfl | rfl
      · have hZero : parityWeight d L 1 u = 0 := by
          unfold parityWeight
          change _ * ((1+(1:ℝ)*(-1:ℝ)^sourceOriginalPParityExponent
            (Finset.univ.biUnion P) u)/2) = 0
          rw [ho.neg_one_pow]
          ring
        linarith
      · rfl
  have hLiouvilleReal : (ArithmeticFunction.liouville u : ℝ) =
      (-1:ℝ)^sourceOriginalPParityExponent (Finset.univ.biUnion P) u := by
    exact_mod_cast hLiouville
  exact hLiouvilleReal.trans hPhase

/-- The proved positive mass populates BOTH original source classes at
every sufficiently large scale. This is a source candidate theorem;
primality of u+2 remains the separate original sieve obligation. -/
theorem parity_original_both_parity_positive_candidates434
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t) :
    ∀ᶠ L : ℝ in atTop, ∀ rho : ℝ, (rho=1 ∨ rho=-1) →
      ∃ u : ℕ,
        u ∈ Finset.range (⌊2*Real.exp L⌋₊+1) ∧
        0<parityWeight (sourceOriginalLiteralDepth 20 L) L rho u ∧
        0<Psi ((u:ℝ)/Real.exp L) ∧
        Real.exp L≤(u:ℝ) ∧ (u:ℝ)≤2*Real.exp L ∧
        0<u ∧ (ArithmeticFunction.liouville u : ℝ)=rho := by
  obtain ⟨c0,hc0,hMass⟩ :=
    localizedMass_lower_bound
      Psi hCont hSupport hNonneg hInterior
  filter_upwards [hMass,eventually_gt_atTop (0:ℝ)] with L hMassL hL
  intro rho hRho
  have hPositive : 0<localizedMass Psi rho L :=
    (by positivity : 0<c0*Real.exp L*L^(-221:ℝ)).trans_le (hMassL rho hRho)
  unfold localizedMass at hPositive
  have hSome : ∃ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
      0<parityWeight (sourceOriginalLiteralDepth 20 L) L rho u *
        Psi ((u:ℝ)/Real.exp L) := by
    by_contra hh
    push Not at hh
    exact (not_lt_of_ge (Finset.sum_nonpos hh)) hPositive
  obtain ⟨u,hu,hWeight⟩ := hSome
  have hA : 0<parityWeight (sourceOriginalLiteralDepth 20 L) L rho u := by
    by_contra hh
    have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh)
      (hNonneg ((u:ℝ)/Real.exp L))
    linarith
  have hPsi : 0<Psi ((u:ℝ)/Real.exp L) := (mul_pos_iff_of_pos_left hA).mp hWeight
  have hLoc := hSupport (show (u:ℝ)/Real.exp L ∈ Function.support Psi from ne_of_gt hPsi)
  have hLo : Real.exp L≤(u:ℝ) := by
    have hh := (le_div_iff₀ (Real.exp_pos L)).mp hLoc.1
    simpa only [one_mul] using hh
  have hHi : (u:ℝ)≤2*Real.exp L :=
    (div_le_iff₀ (Real.exp_pos L)).mp hLoc.2
  have huPos : 0<u := by
    exact_mod_cast (Real.exp_pos L).trans_le hLo
  exact ⟨u,hu,hA,hPsi,hLo,hHi,huPos,
    parity_original_positive_parity_source_liouville434
      (sourceOriginalLiteralDepth 20 L) L rho u hRho (Nat.ne_of_gt huPos) hA⟩
end Green64Analytic.Parity

end

end

/-! ## ParamTypeIICap -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Original Parity Type-II allocation budget E=U*L^(-K0) automatically
satisfies E<=exp((1-b_*)L), as soon as the actual dyadic bound
U<=exp((1-b_*)L) and the fixed Cauchy power K0>=0 hold. No special
value of b_*, no hidden large-L assumption except L>=1. -/
theorem parity_original_typeII_allocation_E_upper_from_U434
    (beta K0 U L : ℝ)
    (hL : 1 ≤ L) (hK0 : 0 ≤ K0) (hU : 0 ≤ U)
    (hUcap : U ≤ Real.exp ((1-beta)*L)) :
    U*L^(-K0) ≤ Real.exp ((1-beta)*L) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hPow : L^(-K0) ≤ 1 := by
    rw [Real.rpow_def_of_pos hLp]
    calc
      Real.exp (Real.log L * (-K0)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos
          (Real.log_nonneg hL) (by linarith))
      _ = 1 := Real.exp_zero
  have hE : U*L^(-K0) ≤ U := by
    calc
      _ ≤ U*1 := mul_le_mul_of_nonneg_left hPow hU
      _ = U := mul_one U
  exact hE.trans hUcap

/-- For every b_*>0, the fixed original Parity reserved band j** can be
chosen ONCE, before the physical data or Fourier allocation branches,
and stays in the true moving original Q depth for all large L. -/
theorem parity_original_beta_fixed_reserved_band_available434
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ jQ : ℕ,
      (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4 ∧
      ∀ᶠ L : ℝ in atTop, jQ ≤ sourceOriginalLiteralDepth 20 L := by
  obtain ⟨jQ,hSmall⟩ := parity_original_reserved_Q_band_exists_for_beta434 beta hbeta
  exact ⟨jQ,hSmall,parity_eventually_original_reserved_Q_band_in_moving_depth434 jQ⟩
end Green64Analytic.Parity

end

end

/-! ## ParamTypeIIELower -/

section

open Filter Real Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

/-- The ORIGINAL Type II lower dyadic U bound `U>=exp(beta L)` with
beta>0 and fixed Cauchy logarithmic exponent K0>=0 gives
E=U*L^-K0>=1 for ALL sufficiently large L. This is derived from the
true asymptotic `log L=o(L)`, not assumed as a separate E-range gate. -/
theorem parity_eventually_original_TypeII_E_one_le434
    (beta K0 : ℝ) (hbeta : 0 < beta) (hK0 : 0 ≤ K0) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ U : ℝ, Real.exp (beta*L) ≤ U → 1 ≤ U*L^(-K0) := by
  have hDen : 0 < K0+1 := by linarith
  have hSmall := (isLittleO_log_rpow_atTop
    (by norm_num : (0:ℝ) < 1)).bound (div_pos hbeta hDen)
  filter_upwards [hSmall,eventually_ge_atTop (1:ℝ)] with L hSmall hL
  refine ⟨hL,?_⟩
  intro U hU
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hLnonneg : 0 ≤ L := hLp.le
  simp only [Real.norm_eq_abs,abs_of_nonneg hLog,Real.rpow_one,
    abs_of_nonneg hLnonneg] at hSmall
  have hApprox : (K0+1)*Real.log L ≤ beta*L := by
    calc
      _ ≤ (K0+1)*((beta/(K0+1))*L) :=
        mul_le_mul_of_nonneg_left hSmall (by linarith)
      _ = beta*L := by
        field_simp [hDen.ne']
  have hLogBeta : K0*Real.log L ≤ beta*L := by
    nlinarith [hApprox]
  have hBase : (1:ℝ) ≤ Real.exp (beta*L)*L^(-K0) := by
    rw [Real.rpow_def_of_pos hLp]
    calc
      (1:ℝ) = Real.exp 0 := by norm_num
      _ ≤ Real.exp (beta*L + Real.log L * (-K0)) :=
        Real.exp_le_exp.mpr (by nlinarith [hLogBeta])
      _ = Real.exp (beta*L)*Real.exp (Real.log L * (-K0)) :=
        Real.exp_add _ _
  exact hBase.trans
    (mul_le_mul_of_nonneg_right hU (Real.rpow_nonneg hLp.le _))

/-- The original full Type II dyadic U window automatically establishes
BOTH allocation-capacity hypotheses 1<=E<=exp((1-beta)L) used in the
actual Parity(4.5) smooth e-range theorem, with E=U*L^-K0.
This removes E>=1 as a SOURCE side assumption for fixed beta>0. -/
theorem parity_eventually_original_TypeII_E_full_budget434
    (beta K0 : ℝ) (hbeta : 0 < beta) (hK0 : 0 ≤ K0) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ U : ℝ, Real.exp (beta*L) ≤ U →
        U ≤ Real.exp ((1-beta)*L) →
        1 ≤ U*L^(-K0) ∧ U*L^(-K0) ≤ Real.exp ((1-beta)*L) := by
  filter_upwards [parity_eventually_original_TypeII_E_one_le434 beta K0 hbeta hK0]
    with L hLower
  refine ⟨hLower.1,?_⟩
  intro U hUlower hUupper
  have hUnonneg : 0 ≤ U := (Real.exp_pos _).le.trans hUlower
  exact ⟨hLower.2 U hUlower,
    parity_original_typeII_allocation_E_upper_from_U434 beta K0 U L
      hLower.1 hK0 hUnonneg hUupper⟩
end Green64Analytic.Parity

end

end

/-! ## SourceOriginalTypeIIUVWindow -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Both actual original Parity TypeII lower dyadic restrictions
  U,V >= exp(bstar L) and UV <= Cbox exp L give the full
  physical source window 1 <= U L^(-K0) <= exp((1-betaP)L).
  All exponents and Cbox are fixed BEFORE the tending L;
  no separately assumed source E-window gate remains. -/
theorem parity_eventually_original_TypeII_source_UV_full_E_window434
    (Cbox betaP bstar K0 : ℝ)
    (hCbox : 1 ≤ Cbox) (hbetaP : 0 < betaP)
    (hbstar : 2*betaP ≤ bstar) (hK0 : 0 ≤ K0) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ (U V : ℝ),
        Real.exp (bstar*L) ≤ U →
        Real.exp (bstar*L) ≤ V →
        U*V ≤ Cbox*Real.exp L →
        1 ≤ U ∧ 1 ≤ V ∧
        1 ≤ U*L^(-K0) ∧
        U*L^(-K0) ≤ Real.exp ((1-betaP)*L) := by
  have hbstarpos : 0 < bstar := by linarith
  have hLower := parity_eventually_original_TypeII_E_one_le434
    bstar K0 hbstarpos hK0
  have hUpper := parity_eventually_original_actual_TypeII_E_upper_geometry434
    Cbox betaP bstar K0 hCbox hbetaP hbstar hK0
  filter_upwards [hLower, hUpper] with L hLlower hLupper
  refine ⟨hLlower.1, ?_⟩
  intro U V hU hV hUV
  have hLpos : 0 ≤ L := by linarith [hLlower.1]
  have hExpOne : (1:ℝ) ≤ Real.exp (bstar*L) := by
    calc
      (1:ℝ) = Real.exp 0 := by simp
      _ ≤ Real.exp (bstar*L) :=
        Real.exp_le_exp.mpr (mul_nonneg hbstarpos.le hLpos)
  have hUone : 1 ≤ U := hExpOne.trans hU
  have hVone : 1 ≤ V := hExpOne.trans hV
  have hUpos : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hU
  have hVpos : 0 < V := lt_of_lt_of_le (Real.exp_pos _) hV
  exact ⟨hUone, hVone, hLlower.2 U hU,
    hLupper.2 U V (U*L^(-K0)) hUpos hVpos hUV hV rfl⟩
end Green64Analytic.Parity

end

end

/-! ## TypeIISelectedBandFullEGeometry -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- In the ORIGINAL Parity §4.1/§4.2 order, choose one reserved
Q band and the upper E exponent before the asymptotic parameter L.
For every actual Type II slab x^b* <= U,V and UV <= Cbox*x,
E=U*L^-K0 then satisfies BOTH E-window gates 1 <= E <=
exp((1-betaP)*L), with betaP=bstar/4.  The chosen band is
actually present in the moving original source family for large L.
This proves genuine compatibility of the local source gates;
it does NOT sum external dyads, betas, allocations or assert (4.2). -/
theorem parity_eventually_original_TypeII_selected_band_full_E_geometry434
    (bstar K0 Cbox : ℝ)
    (hbstar : 0 < bstar) (hK0 : 0 ≤ K0) (hCbox : 1 ≤ Cbox) :
    ∃ betaP : ℝ, ∃ jQ : ℕ,
      0 < betaP ∧ 2*betaP ≤ bstar ∧
      (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4 ∧
      ∀ᶠ L : ℝ in atTop, 32 ≤ L ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (U V E : ℝ),
          Real.exp (bstar*L) ≤ U →
          Real.exp (bstar*L) ≤ V →
          U*V ≤ Cbox*Real.exp L →
          E = U*L^(-K0) →
          1 ≤ E ∧ E ≤ Real.exp ((1-betaP)*L) := by
  let betaP : ℝ := bstar/4
  have hbetaP : 0 < betaP := by dsimp [betaP]; linarith
  have hHalf : 2*betaP ≤ bstar := by dsimp [betaP]; linarith
  obtain ⟨jQ,hBand⟩ :=
    parity_original_reserved_Q_band_exists_for_beta434 betaP hbetaP
  refine ⟨betaP,jQ,hbetaP,hHalf,hBand,?_⟩
  have hLower := parity_eventually_original_TypeII_E_one_le434
    bstar K0 hbstar hK0
  have hUpper := parity_eventually_original_actual_TypeII_E_upper_geometry434
    Cbox betaP bstar K0 hCbox hbetaP hHalf hK0
  have hDepth := parity_eventually_original_reserved_Q_band_in_moving_depth434 jQ
  filter_upwards [hLower,hUpper,hDepth,eventually_ge_atTop (32:ℝ)]
    with L hLowerL hUpperL hDepthL hL
  refine ⟨hL,hDepthL,?_⟩
  intro U V E hUlo hVlo hUVhi hE
  have hUpos : 0 < U := (Real.exp_pos _).trans_le hUlo
  have hVpos : 0 < V := (Real.exp_pos _).trans_le hVlo
  have hEone : 1 ≤ E := by
    rw [hE]
    exact hLowerL.2 U hUlo
  have hEupper := hUpperL.2 U V E hUpos hVpos hUVhi hVlo hE
  exact ⟨hEone,hEupper⟩

/-- Select the original per-slot source precision and Cauchy logarithmic
cutoff BEFORE any Fourier truncation parameter J,B,S and BEFORE L.
This is the exact noncircular conjunction required by the current
full-real Mellin/slot SOURCE theorem, with no extra assumptions on
its fixed Fourier or W1 exponents. -/
theorem parity_original_TypeII_target_K0_precision_compatible434
    (goal : ℝ) :
    ∃ target K0 : ℝ,
      0 ≤ target ∧
      goal + parityOriginalSelectedECoefficientPolylogExponent434 +
        parityOriginalB590FixedFourierPolynomialExponent434 ≤ target ∧
      0 ≤ K0 ∧
      2*target+2*parityOriginalW1PolylogExponent434+344 ≤ K0 := by
  let target : ℝ := max 0
    (goal + parityOriginalSelectedECoefficientPolylogExponent434 +
      parityOriginalB590FixedFourierPolynomialExponent434)
  let K0 : ℝ := max 0
    (2*target + 2*parityOriginalW1PolylogExponent434 + 344)
  refine ⟨target,K0,?_,?_,?_,?_⟩
  · exact le_max_left _ _
  · exact le_max_right _ _
  · exact le_max_left _ _
  · exact le_max_right _ _
end Green64Analytic.Parity

end

end

/-! ## QuarterDyadicEWindowFromSource -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- Original lower factor source exponent 2*bstar has enough FIXED
slack to survive the actual binary dyadic rounding down. No invented
U>=x^bstar assumption at an attained dyadic pair. -/
theorem parity_original_actual_quarter_dyad_lower_scales_from_factors434
    (bstar L : ℝ) (hbstar : 0<bstar)
    (hExp : (2:ℝ)≤Real.exp (bstar*L))
    (m n : ℕ) (U V : ℕ)
    (hScaleM : parityOriginalHistoricalActualZDyadicScale434 m=U)
    (hScaleN : parityOriginalHistoricalActualZDyadicScale434 n=V)
    (hm : Real.exp (2*bstar*L)≤(m:ℝ))
    (hn : Real.exp (2*bstar*L)≤(n:ℝ)) :
    Real.exp (bstar*L)≤(U:ℝ) ∧
    Real.exp (bstar*L)≤(V:ℝ) := by
  have hExpPos : 0<Real.exp (bstar*L) := Real.exp_pos _
  have hSquare : Real.exp (2*bstar*L) =
      Real.exp (bstar*L)*Real.exp (bstar*L) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hmpos : 0 < m := by
    have hp : (0:ℝ)<(m:ℝ) := lt_of_lt_of_le (Real.exp_pos _) hm
    exact_mod_cast hp
  have hnpos : 0 < n := by
    have hp : (0:ℝ)<(n:ℝ) := lt_of_lt_of_le (Real.exp_pos _) hn
    exact_mod_cast hp
  have hM := parity_original_historical_actual_z_in_own_dyad434 m hmpos
  have hN := parity_original_historical_actual_z_in_own_dyad434 n hnpos
  have hMu : (m:ℝ)<2*(U:ℝ) := by
    have hNat : m<2*U := by simpa only [hScaleM] using hM.2.2
    exact_mod_cast hNat
  have hNv : (n:ℝ)<2*(V:ℝ) := by
    have hNat : n<2*V := by simpa only [hScaleN] using hN.2.2
    exact_mod_cast hNat
  have hExp2 : 2*Real.exp (bstar*L) ≤
      Real.exp (2*bstar*L) := by
    rw [hSquare]
    have hh := mul_le_mul_of_nonneg_right hExp hExpPos.le
    nlinarith [hh]
  constructor <;> nlinarith

/-- Original source lower physical factor endpoints imply the TRUE
scale lower gates for EVERY actually attained dyadic pair. The
factor-two rounding slack is paid at a fixed eventual L threshold. -/
theorem parity_eventually_original_actual_quarter_dyads_source_lower434
    (bstar : ℝ) (hbstar : 0<bstar) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (a b c e Y : ℕ)
        (ha : Real.exp (2*bstar*L)≤(a:ℝ))
        (hc : Real.exp (2*bstar*L)≤(c:ℝ))
        (scale : ℕ×ℕ),
        scale ∈ parityOriginalActualTypeIIDyadicPairScales434
          (parityOriginalTypeIIPhysicalPairs434
            (Finset.Icc a b) (Finset.Icc c e) Y) →
        Real.exp (bstar*L)≤(scale.1:ℝ) ∧
        Real.exp (bstar*L)≤(scale.2:ℝ) := by
  filter_upwards [eventually_ge_atTop (Real.log 2/bstar)] with L hLarge
  have hExp : (2:ℝ)≤Real.exp (bstar*L) := by
    have hLog := (div_le_iff₀ hbstar).mp hLarge
    have hE := Real.exp_le_exp.mpr hLog
    simpa [mul_comm,Real.exp_log (by norm_num : (0:ℝ)<2)] using hE
  intro a b c e Y ha hc scale hs
  obtain ⟨z,hz,hScale⟩ := Finset.mem_image.mp hs
  have hPhysical : z ∈ (Finset.Icc a b).product (Finset.Icc c e) := by
    have hh := hz
    simp only [parityOriginalTypeIIPhysicalPairs434,Finset.mem_filter] at hh
    exact hh.1
  have hm := (Finset.mem_product.mp hPhysical).1
  have hn := (Finset.mem_product.mp hPhysical).2
  have hmLow : Real.exp (2*bstar*L)≤(z.1:ℝ) := by
    have hh : a≤z.1 := (Finset.mem_Icc.mp hm).1
    exact ha.trans (by exact_mod_cast hh)
  have hnLow : Real.exp (2*bstar*L)≤(z.2:ℝ) := by
    have hh : c≤z.2 := (Finset.mem_Icc.mp hn).1
    exact hc.trans (by exact_mod_cast hh)
  have hFirst := congrArg Prod.fst hScale
  have hSecond := congrArg Prod.snd hScale
  exact parity_original_actual_quarter_dyad_lower_scales_from_factors434
    bstar L hbstar hExp z.1 z.2 scale.1 scale.2
    hFirst hSecond hmLow hnLow
end Green64Analytic.Parity

end

end

/-! ## QuarterDyadicEWindowEvery -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- For EVERY physically attained quarter dyadic pair cut of the
actual original positive factor support, the original source
E=U L^-K0 is simultaneously legal: U,V>=1 and
1<=E<=exp((1-betaP)L). This uses TRUE source factor lower slack
exp(2bstar L), true quarter product UV<=4exp L, and existing
native source geometry with fixed Cbox=4. No new E hypothesis. -/
theorem parity_eventually_original_actual_quarter_dyad_every_E_legal434
    (betaP bstar K0 : ℝ)
    (hbetaP : 0<betaP) (hbstar : 2*betaP≤bstar)
    (hK0 : 0≤K0) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (a b c e Y : ℕ)
        (ha : Real.exp (2*bstar*L)≤(a:ℝ))
        (hc : Real.exp (2*bstar*L)≤(c:ℝ))
        (scale : ℕ×ℕ),
        scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
          (parityOriginalTypeIIPhysicalPairs434
            (Finset.Icc a b) (Finset.Icc c e) Y)).filter
          (parityOriginalTypeIIQuarterProductGate434 L) →
        1≤(scale.1:ℝ) ∧ 1≤(scale.2:ℝ) ∧
        1≤(scale.1:ℝ)*L^(-K0) ∧
        (scale.1:ℝ)*L^(-K0)≤Real.exp ((1-betaP)*L) := by
  have hBstar : 0<bstar := by linarith
  have hLower := parity_eventually_original_actual_quarter_dyads_source_lower434
    bstar hBstar
  have hWindow := parity_eventually_original_TypeII_source_UV_full_E_window434
    4 betaP bstar K0 (by norm_num) hbetaP hbstar hK0
  filter_upwards [hLower,hWindow] with L hL hW
  refine ⟨hW.1,?_⟩
  intro a b c e Y ha hc scale hs
  have hAttained := (Finset.mem_filter.mp hs).1
  have hQuarter := (Finset.mem_filter.mp hs).2
  have hScales := hL a b c e Y ha hc scale hAttained
  exact hW.2 (scale.1:ℝ) (scale.2:ℝ)
    hScales.1 hScales.2 hQuarter.2
end Green64Analytic.Parity

end

end

/-! ## QuarterActualCutAllGates -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 4800000

/-- Every genuine interval cut [max a U,min b(2U-1)] is contained
in the numerical ORIGINAL U dyad, with the exact half-open upper
endpoint demanded by the native b629 TypeII source theorem. -/
theorem parity_original_actual_quarter_cut_m_dyad_bounds434
    (a b U : ℕ) (hU : 0<U) :
    ∀ m ∈ Finset.Icc (max a U) (min b (2*U-1)),
      (U:ℝ)≤(m:ℝ) ∧ (m:ℝ)<2*(U:ℝ) := by
  intro m hm
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hm
  have hmLo : U ≤ m := (le_max_right _ _).trans hlo
  have hmHi : m<2*U := by omega
  constructor
  · exact_mod_cast hmLo
  · exact_mod_cast hmHi

/-- Literal true beta interval on an attained binary dyad is inside
the ORIGINAL closed [V,2V] beta range (including its right edge). -/
theorem parity_original_actual_quarter_cut_n_dyad_bounds434
    (c e V : ℕ) :
    ∀ n ∈ Finset.Icc (max c V) (min e (2*V-1)),
      (V:ℝ)≤(n:ℝ) ∧ (n:ℝ)≤2*(V:ℝ) := by
  intro n hn
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hn
  have hnLo : V ≤ n := (le_max_right _ _).trans hlo
  have hnHi : n≤2*V := by omega
  constructor
  · exact_mod_cast hnLo
  · exact_mod_cast hnHi

/-- A positive source lower factor boundary exp(2 bstar L) also
pays the original b629 fine threshold exp(beta L) for beta≤2bstar.
This is fixed exponent slack, not a post-hoc choice of the b629
parameter from the individual dyad. -/
theorem parity_original_actual_quarter_cut_fine_lower434
    (L bstar beta : ℝ) (a U : ℕ)
    (hL : 0≤L) (hBeta : beta≤2*bstar)
    (ha : Real.exp (2*bstar*L)≤(a:ℝ)) :
    Real.exp (beta*L)≤((max a U:ℕ):ℝ) := by
  have hExp : Real.exp (beta*L)≤Real.exp (2*bstar*L) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hBeta hL
  exact hExp.trans (ha.trans (by exact_mod_cast (le_max_left a U)))

/-- All geometric, source E and legal fine interval conditions
needed by original one-fine, one-slot quarter-UV b629 TypeII are
TRUE for EACH attained physical dyadic pair, given fixed original
positive factor margin. No signed Fourier/Q or external family
estimate is claimed here. -/
theorem parity_eventually_original_actual_quarter_cut_all_numeric_gates434
    (beta betaP bstar K0 : ℝ)
    (hbetaP : 0<betaP) (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar) (hK0 : 0≤K0) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (a b c e Y : ℕ)
        (ha : Real.exp (2*bstar*L)≤(a:ℝ))
        (hc : Real.exp (2*bstar*L)≤(c:ℝ))
        (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
        (scale : ℕ×ℕ),
        scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
          (parityOriginalTypeIIPhysicalPairs434
            (Finset.Icc a b) (Finset.Icc c e) Y)).filter
          (parityOriginalTypeIIQuarterProductGate434 L) →
        let U : ℝ := scale.1
        let V : ℝ := scale.2
        let E : ℝ := U*L^(-K0)
        let ac : ℕ := max a scale.1
        let bc : ℕ := min b (2*scale.1-1)
        let Jcut : Finset ℕ := Finset.Icc (max c scale.2) (min e (2*scale.2-1))
        0<U ∧ 0<V ∧ Real.exp L≤4*U*V ∧ U*V≤4*Real.exp L ∧
        1≤E ∧ E≤Real.exp ((1-betaP)*L) ∧ 1≤V ∧
        Real.exp (beta*L)≤(ac:ℝ) ∧ 2≤ac ∧ bc≤2*ac ∧
        (bc:ℝ)≤Real.exp (2*L) ∧
        (∀m∈Finset.Icc ac bc,U≤(m:ℝ) ∧ (m:ℝ)<2*U) ∧
        (∀n∈Jcut,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) := by
  have hbstarPos : 0<bstar := by linarith
  have hTwoBstar : 0<2*bstar := by linarith
  have hWin := parity_eventually_original_actual_quarter_dyad_every_E_legal434
    betaP bstar K0 hbetaP hbstar hK0
  filter_upwards [hWin,eventually_ge_atTop (Real.log 2/(2*bstar))]
    with L hWindow hLarge
  have hExp2 : (2:ℝ)≤Real.exp (2*bstar*L) := by
    have hh := (div_le_iff₀ hTwoBstar).mp hLarge
    have hp := Real.exp_le_exp.mpr hh
    simpa [mul_comm,Real.exp_log (by norm_num : (0:ℝ)<2)] using hp
  intro a b c e Y ha hc hab hExpB scale hs
  have hProduct := (Finset.mem_filter.mp hs).2
  have hW := hWindow.2 a b c e Y ha hc scale hs
  have ha2 : 2≤a := by
    exact_mod_cast hExp2.trans ha
  have hLow : Real.exp (beta*L)≤((max a scale.1:ℕ):ℝ) :=
    parity_original_actual_quarter_cut_fine_lower434
      L bstar beta a scale.1 (by linarith [hWindow.1]) hBeta ha
  have hCut2 : 2 ≤ max a scale.1 := by omega
  have hCut2a : min b (2*scale.1-1)≤2*(max a scale.1) := by omega
  have hCutExp : ((min b (2*scale.1-1):ℕ):ℝ)≤Real.exp (2*L) := by
    have hh : min b (2*scale.1-1)≤b := min_le_left _ _
    have hCast : ((min b (2*scale.1-1):ℕ):ℝ)≤(b:ℝ) := by
      exact_mod_cast hh
    exact hCast.trans hExpB
  dsimp
  refine ⟨by linarith [hW.1],by linarith [hW.2.1],
    hProduct.1.le,hProduct.2,hW.2.2.1,hW.2.2.2,
    hW.2.1,hLow,hCut2,hCut2a,hCutExp,?_,?_⟩
  · have hScalePos : 0<scale.1 := by
      have hR : (0:ℝ)<(scale.1:ℝ) := by linarith [hW.1]
      exact_mod_cast hR
    exact parity_original_actual_quarter_cut_m_dyad_bounds434 a b scale.1 hScalePos
  · exact parity_original_actual_quarter_cut_n_dyad_bounds434 c e scale.2
end Green64Analytic.Parity

end

end

/-! ## QuarterEveryCutSignedAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- A SINGLE source-ordered choice of reserved band, H,J,B,S and
original fine proxy controls EACH truly attained quarter-product
binary Icc factor cut, with no unproved local E / b629 interval /
closed beta endpoint assumptions. The original input has a fixed
exponential slack exp(2bstar L); E=U L^-K0 is chosen by the
same global source prescription on every cut. This is per cut,
not yet the finite sum of all signed sources. -/
theorem parity_eventually_original_signed_b629_every_quarter_cut_anylog434
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
          (scale : ℕ×ℕ),
          scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
              (parityOriginalTypeIIPhysicalPairs434
                (Finset.Icc a b) (Finset.Icc c e) Y)).filter
              (parityOriginalTypeIIQuarterProductGate434 L) →
          ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
          ∀ (slot : Fin 20) (prime : Bool)
            (betaCoeff : ℕ → ℂ) (signed : Bool),
            (∀n∈Finset.Icc (max c scale.2) (min e (2*scale.2-1)),
              ‖betaCoeff n‖≤1) →
          let d := sourceOriginalLiteralDepth 20 L
          let K := Finset.Icc (max a scale.1) (min b (2*scale.1-1))
          let Jcut := Finset.Icc (max c scale.2) (min e (2*scale.2-1))
          let alpha := restrictSequence K
            (b629ActualFineAlpha434 prime L S gamma (max a scale.1) (min b (2*scale.1-1)))
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          ‖parityOriginalShiftTwoSignedBilinearMellinSource434
              d L Psi K Jcut alpha betaCoeff signed 0 ⌊2*Real.exp L⌋₊‖ ≤
            (4+Csource*(∫s : ℝ,
                ‖(𝓕 (parityOriginalLogCutoff434
                  (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
             20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
  have hSigned := parity_eventually_original_signed_quarter_b629_fine_one_slot_Psi_Mellin_source_anylog434
    jQ goal target C0 beta betaP gamma K0 4 A R
    hbetaP hBand hC0 hTarget hK0Target hPrecision hbeta hgamma hK0
    (by norm_num) hA hR buf hSmooth hSupport hOne4 hCube
    Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  have hGates := parity_eventually_original_actual_quarter_cut_all_numeric_gates434
    beta betaP bstar K0 hbetaP hbstar hBeta hK0
  obtain ⟨H,J,B,S,hBS,hSignedL⟩ := hSigned
  refine ⟨H,J,B,S,hBS,?_⟩
  filter_upwards [hSignedL,hGates] with L hSignedNow hGateNow
  rcases hSignedNow with ⟨hBig,h128,h24,hFam,hReserved,hRest⟩
  refine ⟨hBig,h128,(by norm_num at h24 ⊢; exact h24),hFam,hReserved,?_⟩
  intro hL hFamily a b c e Y ha hc hab hExpB scale hs
    band hBandSlot slot prime betaCoeff signed hBetaCoeff
  have hG := hGateNow a b c e Y ha hc hab hExpB scale hs
  rcases hG with ⟨hUpos,hVpos,hUVlower,hUVupper,hEone,hEupper,hVone,
    hFineLower,hFine2,hFineWidth,hFineExp,hKcut,hJcut⟩
  have hBound := hRest hL hFamily (scale.1:ℝ) (scale.2:ℝ)
    ((scale.1:ℝ)*L^(-K0)) hUpos hVpos hUVlower hUVupper
    rfl hEone hEupper hVone band hBandSlot slot
    (max a scale.1) (min b (2*scale.1-1))
    (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
    prime betaCoeff signed hFineLower hFine2 hFineWidth hFineExp
    hKcut hJcut hBetaCoeff
  dsimp only at hBound ⊢
  convert hBound using 1 <;> ring
end Green64Analytic.Parity

end

end

/-! ## QuarterSignedCutSumPaid -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The source selected-band and signed-branch quarter-cut family is
paid by its ACTUAL distinct physical dyadic cardinal, without a
fresh analytic parameter for each cut and without any hidden beta
subfamily cardinality. This is the finite sum of signed b629 source
cuts, not an asserted identification with the multi-slot total
unrestricted Parity TypeII source. -/
theorem parity_eventually_original_signed_quarter_actual_cut_sum_paid434
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
          ‖∑ scale ∈ T,
             parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
               (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
               (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
               (restrictSequence
                 (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
                 (b629ActualFineAlpha434 prime L S gamma
                   (max a scale.1) (min b (2*scale.1-1))))
               betaCoeff signed 0 ⌊2*Real.exp L⌋₊‖ ≤
            (T.card:ℝ)*Bound := by
  obtain ⟨H,J,B,S,hBS,hEvery⟩ :=
    parity_eventually_original_signed_b629_every_quarter_cut_anylog434
      jQ goal target C0 beta betaP bstar gamma K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hgamma hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  refine ⟨H,J,B,S,hBS,?_⟩
  filter_upwards [hEvery] with L hEveryNow
  rcases hEveryNow with ⟨hBig,h128,h24,hFam,hRes,hRest⟩
  refine ⟨hBig,h128,h24,hFam,hRes,?_⟩
  intro hL hFam0 a b c e Y ha hc hab hExpB band hBandNow
    slot prime betaCoeff signed hBetaWhole
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
  have hEach (scale : ℕ×ℕ) (hs : scale∈T) :
      ‖parityOriginalShiftTwoSignedBilinearMellinSource434
        (sourceOriginalLiteralDepth 20 L) L Psi
        (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
        (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
        (restrictSequence
          (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
          (b629ActualFineAlpha434 prime L S gamma
            (max a scale.1) (min b (2*scale.1-1))))
        betaCoeff signed 0 ⌊2*Real.exp L⌋₊‖ ≤ Bound := by
    have hBetaCut : ∀n∈Finset.Icc (max c scale.2) (min e (2*scale.2-1)),
        ‖betaCoeff n‖≤1 := by
      intro n hn
      obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hn
      have hJn : n∈Finset.Icc c e := Finset.mem_Icc.mpr
        ⟨(le_max_left _ _).trans hlo,hhi.trans (min_le_left _ _)⟩
      exact hBetaWhole n hJn
    have h := hRest hL hFam0 a b c e Y ha hc hab hExpB scale
      hs band hBandNow slot prime betaCoeff signed hBetaCut
    simpa only [Bound,C1,Cmoment,Cphys,Csource,M_H,T] using h
  dsimp only
  calc
    _ ≤ ∑ scale ∈ T,
        ‖parityOriginalShiftTwoSignedBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi
          (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
          (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
          (restrictSequence
            (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
            (b629ActualFineAlpha434 prime L S gamma
              (max a scale.1) (min b (2*scale.1-1))))
          betaCoeff signed 0 ⌊2*Real.exp L⌋₊‖ := norm_sum_le _ _
    _ ≤ ∑ scale ∈ T, Bound := by
      apply Finset.sum_le_sum
      intro scale hs
      exact hEach scale hs
    _ = (T.card:ℝ)*Bound := by simp
end Green64Analytic.Parity

end

end

/-! ## QuarterEveryCutSignedGlobalAudit -/

section



end

