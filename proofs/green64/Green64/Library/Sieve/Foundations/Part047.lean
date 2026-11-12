module

public import Green64.Library.Sieve.Foundations.Part046
public import Green64.Library.Sieve.Foundations.Part043
public import Green64.Library.Sieve.Foundations.Part039
public import Green64.Library.Sieve.Foundations.Part018
public import Green64.Library.Sieve.Foundations.Part044
public import Green64.Library.Sieve.Foundations.Part038
public import Green64.Library.Sieve.Foundations.Part012
public import Green64.Library.Sieve.Foundations.Part041
public import Green64.Library.Sieve.Foundations.Part042
public import Green64.Library.Sieve.Foundations.Part040
public import Green64.Library.Sieve.Foundations.Part007

@[expose] public section

/-!
# Sieve / Foundations / Part047

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## QuarterFineBprimeFullQPositive -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- TRUE ORIGINAL Parity(4.7) CAP-FREE Bprime full N-dimensional Q
Fourier positive variation, summed over *all* 2^N original Boolean
allocations. The selected-e Q Fourier gate is already inside the
original a_e(e): its single source supremum A_gate is integrated
ONCE, using the original B590 f0/f1 L1 variation. No duplicated
selected-Q phase, no fake L1 bound for a squared Q gate, and no
complex cancellation of signed subsums. Only one actual b629 fine
interval, original reserved Q-band and slot remain fixed; the full
original TypeII(4.2) is not asserted. The precision target pays the
fixed original selected-e exponent and full Fourier variation BEFORE
Parity's J,B,S are chosen, with K0 sufficiently large in advance. -/
theorem parity_eventually_original_actual_quarter_fine_Bprime_fullQ_positive_anylog434
    (jQ : ℕ) (goal target C0 beta gamma K0 Cbox A R : ℝ)
    (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
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
    parity_eventually_original_actual_quarter_fine_preCauchy_norm_anylog434
      jQ target C0 beta gamma K0 Cbox A R
      hTarget hK0Target hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube
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
  refine ⟨J,B,S,hBS,?_⟩
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
end Green64Analytic.Parity

end

end

/-! ## QuarterB629SingleSlotRestrictedPsiMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- The exact ORIGINAL full-interval [a,b] b629 prime/rough
full-cell proxy source, for ONE chosen reserved Q slot, with
complete original Boolean allocations and N-dimensional Q Fourier
cube, has arbitrary O_A(exp(L)L^-A) saving after integration over
|s|<=L^C0/(2π). The underlying Parity(4.17) per-slot Cauchy bound
is original; no 20-slot complex cancellation, no per-cell L^S,
selected Q factor counted once. This is the matching low-s source
result for the literal per-slot preCauchy comparison. -/
theorem parity_eventually_original_actual_quarter_b629_single_slot_restricted_Psi_Mellin_Q_anylog434
    (jQ : ℕ) (goal target C0 beta gamma K0 Cbox A R : ℝ)
    (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
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
    parity_eventually_original_actual_quarter_fine_Bprime_fullQ_positive_anylog434
      jQ goal target C0 beta gamma K0 Cbox A R
      hTarget hK0Target hPrecision hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube
  refine ⟨J,B,S,hBS,?_⟩
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
end Green64Analytic.Parity

end

end

/-! ## QuarterFineBprimeAllSlotsFullQPositive -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 10500000

/-- Complete true ORIGINAL twenty reserved Q-slot sum of the genuine
cap-free pre-Cauchy Bprime absolute Fourier integral. For each slot,
all original 2^N Boolean allocations and its own N-dimensional cube
are integrated exactly once; labelled Q prime tuples remain inside
native selected-e/skipped-Q coefficients and are not re-counted.
This is per original b629 fine interval and fixed reserved Q band,
not original whole TypeII(4.2). The numeric slot loss is exactly 20. -/
theorem parity_eventually_original_actual_quarter_fine_Bprime_all_reserved_slots_fullQ_positive_anylog434
    (jQ : ℕ) (goal target C0 beta gamma K0 Cbox A R : ℝ)
    (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
          E=U*L^(-K0) → 1≤E → 1≤V →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (rho : ℝ), |rho|≤L^C0 →
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
        let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
        let Csource := 1+6*Cbox*(2+Cphys+24*C1)
        (∑slot : Fin 20,
          ∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫freq in parityOriginalActualFullQFrequencyCube434 L,
            ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta freq rho K Jbeta alpha betaCoeff signed‖) ≤
          20*Csource*Real.exp L*L^(-goal) := by
  obtain ⟨J,B,S,hBS,hOne⟩ :=
    parity_eventually_original_actual_quarter_fine_Bprime_fullQ_positive_anylog434
      jQ goal target C0 beta gamma K0 Cbox A R
      hTarget hK0Target hPrecision hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hOne] with L hOneL
  rcases hOneL with ⟨hL32,hL6,hFamily,hReserved,hOneRest⟩
  refine ⟨hL32,hL6,hFamily,hReserved,?_⟩
  intro hL hFamily0 U V E hU hV hUV hUVhi hEscale hEone hVone
    band hBand rho hrho a b Jbeta prime lFine uFine betaCoeff signed
    hFineLow hl hu huExp hDyad hJ hBeta
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+6*Cbox*(2+Cphys+24*C1)
  have hSlot (slot : Fin 20) :
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫freq in parityOriginalActualFullQFrequencyCube434 L,
          ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
            d L E band slot delta freq rho K Jbeta alpha betaCoeff signed‖) ≤
        Csource*Real.exp L*L^(-goal) := by
    have h := hOneRest hL hFamily0 U V E hU hV hUV hUVhi
      hEscale hEone hVone band hBand slot rho hrho
      a b Jbeta prime lFine uFine betaCoeff signed
      hFineLow hl hu huExp hDyad hJ hBeta
    dsimp only at h
    simpa only [d,K,alpha,C1,Cmoment,Cphys,Csource] using h
  dsimp only at ⊢
  change (∑slot : Fin 20,
      ∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫freq in parityOriginalActualFullQFrequencyCube434 L,
          ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
            d L E band slot delta freq rho K Jbeta alpha betaCoeff signed‖) ≤
      20*Csource*Real.exp L*L^(-goal)
  calc
    _ ≤ ∑_slot : Fin 20,Csource*Real.exp L*L^(-goal) := by
      apply Finset.sum_le_sum
      intro slot hslot
      exact hSlot slot
    _ = 20*Csource*Real.exp L*L^(-goal) := by simp; ring
end Green64Analytic.Parity

end

end

/-! ## QuarterFineFamilyFullQPositive -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 10500000

/-- The actual ORIGINAL Bprime/Q-gated Fourier source, summed over an
explicitly quantified finite family of original b629 fine intervals.
Each family member has genuine original restricted fine alpha and
an independent bounded beta coefficient: no fake universal-alpha
E4.1 hypothesis. ALL 20 reserved slots, ALL Boolean allocations and
N-dimensional frequency cubes are preserved. A family cardinality
bound `#families <= L^Cfine` is an EXPLICIT additional input; its
mathematical derivation from the pinned original fine partition is
not asserted. To avoid retrospective choice, Cfine and its precision
are fixed BEFORE K0, J/B/S and L. This is a conditional aggregation
interface, NOT the original complete Parity TypeII(4.2). -/
theorem parity_eventually_original_actual_quarter_b629_fine_family_fullQ_positive_anylog434
    (jQ : ℕ) (goal target Cfine C0 beta gamma K0 Cbox A R : ℝ)
    (hTarget : 0≤target) (hCfine : 0≤Cfine)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+Cfine+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
          E=U*L^(-K0) → 1≤E → 1≤V →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (rho : ℝ), |rho|≤L^C0 →
        ∀ {ι : Type} [DecidableEq ι]
          (F : Finset ι)
          (a b lFine uFine : ι → ℕ)
          (Jbeta : ι → Finset ℕ)
          (prime : ι → Bool)
          (betaCoeff : ι → ℕ → ℂ)
          (signed : ι → Bool),
          (F.card:ℝ)≤L^Cfine →
          (∀i∈F, Real.exp (beta*L)≤(lFine i:ℝ) ∧
            2≤lFine i ∧ uFine i≤2*lFine i ∧
            (uFine i:ℝ)≤Real.exp (2*L) ∧
            (∀m∈Finset.Icc (a i) (b i),U≤(m:ℝ) ∧ (m:ℝ)<2*U) ∧
            (∀n∈Jbeta i,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) ∧
            (∀n∈Jbeta i,‖betaCoeff i n‖≤1)) →
        let d := sourceOriginalLiteralDepth 20 L
        let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
        let Csource := 1+6*Cbox*(2+Cphys+24*C1)
        (∑i∈F,∑slot : Fin 20,
          ∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → Bool,
            ∫freq in parityOriginalActualFullQFrequencyCube434 L,
              ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                d L E band slot delta freq rho
                (Finset.Icc (a i) (b i)) (Jbeta i)
                (restrictSequence (Finset.Icc (a i) (b i))
                  (b629ActualFineAlpha434 (prime i) L S gamma (lFine i) (uFine i)))
                (betaCoeff i) (signed i)‖) ≤
          20*Csource*Real.exp L*L^(-goal) := by
  obtain ⟨J,B,S,hBS,hOne⟩ :=
    parity_eventually_original_actual_quarter_fine_Bprime_all_reserved_slots_fullQ_positive_anylog434
      jQ (goal+Cfine) target C0 beta gamma K0 Cbox A R
      hTarget hK0Target hPrecision hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube
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
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hOne] with L hOneL
  rcases hOneL with ⟨hL32,hL6,hActualFamily,hReserved,hOneRest⟩
  refine ⟨hL32,hL6,hActualFamily,hReserved,?_⟩
  intro hL hFamily U V E hU hV hUV hUVhi hEscale hEone hVone
    band hBand rho hrho ι _ F a b lFine uFine Jbeta prime betaCoeff
    signed hCard hCells
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let Dcell : ℝ := goal+Cfine
  let CellBound : ℝ := 20*Csource*Real.exp L*L^(-Dcell)
  have hLp : 0<L := by linarith
  have hLone : (1:ℝ)≤L := by linarith
  have hCellBound : 0≤CellBound := by dsimp [CellBound]; positivity
  have hCell (i : ι) (hi : i∈F) :
      (∑slot : Fin 20,
          ∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → Bool,
            ∫freq in parityOriginalActualFullQFrequencyCube434 L,
              ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                d L E band slot delta freq rho
                (Finset.Icc (a i) (b i)) (Jbeta i)
                (restrictSequence (Finset.Icc (a i) (b i))
                  (b629ActualFineAlpha434 (prime i) L S gamma (lFine i) (uFine i)))
                (betaCoeff i) (signed i)‖) ≤ CellBound := by
    rcases hCells i hi with ⟨hFineLow,hl,hu,huExp,hDyad,hJ,hBeta⟩
    have h := hOneRest hL hFamily U V E hU hV hUV hUVhi
      hEscale hEone hVone band hBand rho hrho
      (a i) (b i) (Jbeta i) (prime i) (lFine i) (uFine i)
      (betaCoeff i) (signed i)
      hFineLow hl hu huExp hDyad hJ hBeta
    dsimp only at h
    simpa only [d,C1,Cmoment,Cphys,Csource,CellBound,Dcell] using h
  have hSum :
      (∑i∈F,∑slot : Fin 20,
          ∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → Bool,
            ∫freq in parityOriginalActualFullQFrequencyCube434 L,
              ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                d L E band slot delta freq rho
                (Finset.Icc (a i) (b i)) (Jbeta i)
                (restrictSequence (Finset.Icc (a i) (b i))
                  (b629ActualFineAlpha434 (prime i) L S gamma (lFine i) (uFine i)))
                (betaCoeff i) (signed i)‖) ≤
      (F.card:ℝ)*CellBound := by
    calc
      _ ≤ ∑i∈F,CellBound := by
        apply Finset.sum_le_sum
        intro i hi
        exact hCell i hi
      _ = (F.card:ℝ)*CellBound := by simp
  have hPower : L^Cfine*L^(-Dcell)=L^(-goal) := by
    rw [←Real.rpow_add hLp]
    congr 1
    dsimp [Dcell]
    ring
  have hCo : 0≤20*Csource*Real.exp L := by positivity
  dsimp only at ⊢
  calc
    _ ≤ (F.card:ℝ)*CellBound := hSum
    _ ≤ L^Cfine*CellBound := mul_le_mul_of_nonneg_right hCard hCellBound
    _ = (20*Csource*Real.exp L)*(L^Cfine*L^(-Dcell)) := by
      dsimp [CellBound]; ring
    _ = (20*Csource*Real.exp L)*L^(-goal) := by rw [hPower]
    _ = 20*Csource*Real.exp L*L^(-goal) := by ring
end Green64Analytic.Parity

end

end

/-! ## TruePhysicalYboxSupport -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 1100000

/-- True original shifted physical m*n=u+2 and genuine binary dyadic
m<2U,n<2V force u into the ORIGINAL cap-free Ybox=ceil(6UV),
WITHOUT the obsolete UV >= exp L lower bound. This is the correct
support-level bridge, not a false numeric containment of Y0 in Ybox. -/
theorem parity_original_TypeII_true_physical_u_le_Ybox434
    (U V : ℝ) (m n u : ℕ)
    (hU : 0 < U) (hV : 0 < V)
    (hm : (m:ℝ) < 2*U) (hn : (n:ℝ) < 2*V)
    (hEq : m*n=u+2) :
    u ≤ Nat.ceil (6*U*V) := by
  have hm0 : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hProd : (m:ℝ)*(n:ℝ) < (2*U)*(2*V) := by
    calc
      (m:ℝ)*(n:ℝ) ≤ (2*U)*(n:ℝ) :=
        mul_le_mul_of_nonneg_right hm.le hn0
      _ < (2*U)*(2*V) :=
        mul_lt_mul_of_pos_left hn (by positivity)
  have heq : (m:ℝ)*(n:ℝ) = (u:ℝ)+2 := by
    exact_mod_cast hEq
  have hCeil : 6*U*V≤((Nat.ceil (6*U*V)):ℝ) := Nat.le_ceil _
  have hu : (u:ℝ)≤((Nat.ceil (6*U*V)):ℝ) := by
    nlinarith [hProd,heq,hCeil,hU,hV]
  exact_mod_cast hu

/-- Source Ioc fibres at the same (m,n) have no admissible shifted
positive u outside original Ybox when both original factor supports
lie in their true U,V dyads. -/
theorem parity_original_TypeII_shifted_pair_in_true_Ybox434
    (U V : ℝ) (K J : Finset ℕ) (Y u m n : ℕ)
    (hU : 0 < U) (hV : 0 < V)
    (hK : ∀ m ∈ K, (m:ℝ) < 2*U)
    (hJ : ∀ n ∈ J, (n:ℝ) < 2*V)
    (hm : m∈K) (hn : n∈J)
    (hShift : m*n=u+2) :
    u ≤ Nat.ceil (6*U*V) :=
  parity_original_TypeII_true_physical_u_le_Ybox434 U V m n u
    hU hV (hK m hm) (hJ n hn) hShift
end Green64Analytic.Parity

end

end

/-! ## TruePhysicalYboxTripleCut -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- For the TRUE shifted m*n=u+2 source triple, original physical
dyadic bounds put every nonzero term into Ybox=ceil(6UV).
Therefore the exact source truncated at ANY Y equals the source
truncated at min(Y,Ybox). This does not use the FALSE global
numeric assertion floor(2exp L) <= Ybox. No cut of original
full-cell alpha, and no assumptions on beta or Psi are needed. -/
theorem parity_original_TypeII_triple_true_physical_Ybox_min434
    (d : ℕ) (L U V : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ)
    (hU : 0 < U) (hV : 0 < V)
    (hK : ∀ m ∈ K, (m:ℝ) < 2*U)
    (hJ : ∀ n ∈ J, (n:ℝ) < 2*V) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta Y =
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta (min Y (Nat.ceil (6*U*V))) := by
  classical
  unfold parityOriginalShiftTwoOriginalTypeIITripleSource434
  apply Finset.sum_congr rfl
  intro z hz
  have hm : z.1 ∈ K := (Finset.mem_product.mp hz).1
  have hn : z.2 ∈ J := (Finset.mem_product.mp hz).2
  let Ybox := Nat.ceil (6*U*V)
  have hsub : Finset.Ioc 0 (min Y Ybox) ⊆ Finset.Ioc 0 Y := by
    intro u hu
    have h := Finset.mem_Ioc.mp hu
    exact Finset.mem_Ioc.mpr ⟨h.1,h.2.trans (min_le_left _ _)⟩
  symm
  apply Finset.sum_subset hsub
  intro u hu huNot
  have huGreater : Ybox < u := by
    have huY := (Finset.mem_Ioc.mp hu).2
    have hbad : ¬u ≤ min Y Ybox := by
      intro h
      exact huNot (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hu).1,h⟩)
    omega
  have hExclude : ¬(0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2) := by
    rintro ⟨hmpos,hnpos,hprod⟩
    have hCap := parity_original_TypeII_true_physical_u_le_Ybox434
      U V z.1 z.2 u hU hV (hK z.1 hm) (hJ z.2 hn) hprod
    exact (not_le_of_gt huGreater) hCap
  simp [hExclude]
end Green64Analytic.Parity

end

end

/-! ## TruePhysicalYboxOldPsiExact -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- ORIGINAL Ψ supported on [1,2] gives u≤floor(2 exp L)
for any nonzero Ψ(u/exp L). Does not depend on the dyadic
U,V carrier and uses the original L and Q/P scales. -/
theorem parity_original_TypeII_psi_nonzero_u_le_old_Y0_434
    (L : ℝ) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (u : ℕ) (hNonzero : Psi ((u:ℝ)/Real.exp L) ≠ 0) :
    u ≤ ⌊2*Real.exp L⌋₊ := by
  have hp : 0<Real.exp L := Real.exp_pos _
  have hmem : (u:ℝ)/Real.exp L ∈ Set.Icc 1 2 :=
    hPsi (by simpa only [Function.mem_support] using hNonzero)
  have hle : (u:ℝ)≤2*Real.exp L :=
    (div_le_iff₀ hp).mp (Set.mem_Icc.mp hmem).2
  exact Nat.le_floor hle

/-- Exact physical source triple truncation at min(Y,Y0), with
Y0=floor(2exp L), from original compact Ψ support. -/
theorem parity_original_TypeII_triple_psi_old_Y0_min434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta Y =
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta (min Y ⌊2*Real.exp L⌋₊) := by
  classical
  unfold parityOriginalShiftTwoOriginalTypeIITripleSource434
  apply Finset.sum_congr rfl
  intro z hz
  have hsub : Finset.Ioc 0 (min Y ⌊2*Real.exp L⌋₊) ⊆ Finset.Ioc 0 Y := by
    intro u hu
    exact Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp hu).1,
        (Finset.mem_Ioc.mp hu).2.trans (min_le_left _ _)⟩
  symm
  apply Finset.sum_subset hsub
  intro u hu huNot
  have hOutside : ⌊2*Real.exp L⌋₊ < u := by
    have huY := (Finset.mem_Ioc.mp hu).2
    have hbad : ¬u ≤ min Y ⌊2*Real.exp L⌋₊ := by
      intro h
      exact huNot (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hu).1,h⟩)
    omega
  have hPsiZero : Psi ((u:ℝ)/Real.exp L)=0 := by
    by_contra hz
    have hBound := parity_original_TypeII_psi_nonzero_u_le_old_Y0_434
      L Psi hPsi u hz
    omega
  by_cases hCond : 0 < z.1 ∧ 0 < z.2 ∧ z.1*z.2=u+2
  · simp [hCond,hPsiZero]
  · simp [hCond]

/-- Actual original pre-Cauchy Y0 and true cap-free Ybox define
EXACTLY THE SAME fully weighted shifted Type II triple source
under genuine dyadic factor supports and genuine compact Ψ.
This eliminates the invalid Y0⊆Ybox assumption without changing
L, Q/P families, α or β. -/
theorem parity_original_TypeII_true_physical_Ybox_eq_old_Y0_Psi434
    (d : ℕ) (L U V : ℝ) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (hU : 0<U) (hV : 0<V)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)<2*V) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta ⌊2*Real.exp L⌋₊ =
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta (Nat.ceil (6*U*V)) := by
  calc
    _ = parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta (min ⌊2*Real.exp L⌋₊ (Nat.ceil (6*U*V))) :=
      parity_original_TypeII_triple_true_physical_Ybox_min434
        d L U V Psi K J alpha beta ⌊2*Real.exp L⌋₊ hU hV hK hJ
    _ = parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta (min (Nat.ceil (6*U*V)) ⌊2*Real.exp L⌋₊) := by
      rw [min_comm]
    _ = _ := (parity_original_TypeII_triple_psi_old_Y0_min434
      d L Psi hPsi K J alpha beta (Nat.ceil (6*U*V))).symm
end Green64Analytic.Parity

end

end

/-! ## TruePhysicalPsiWeightedCut -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 1700000

/-- Original positive shifted pair sum vanishes beyond the actual
Ybox when the K,J supports lie below their physical 2U,2V caps.
This holds for arbitrary complex alpha,beta and does not assume
UV>=exp L. -/
theorem parity_original_positive_pair_fibre_zero_beyond_true_Ybox434
    (U V : ℝ) (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (u : ℕ)
    (hU : 0<U) (hV : 0<V)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)<2*V)
    (hFar : Nat.ceil (6*U*V)<u) :
    (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
      alpha z.1*beta z.2)=0 := by
  apply Finset.sum_eq_zero
  intro z hz
  have h := Finset.mem_filter.mp hz
  have hmem := Finset.mem_product.mp h.1
  rcases h.2 with ⟨hm,hn,heq⟩
  have hY := parity_original_TypeII_true_physical_u_le_Ybox434
    U V z.1 z.2 u hU hV (hK z.1 hmem.1) (hJ z.2 hmem.2) heq
  omega

/-- General original Ψ-weighted physical bilinear sum, with any
extra complex weight H(u) (e.g., actual post-Mellin e-first source),
is EXACTLY invariant under Y0↔Ybox. Neither a fabricated Y0⊆Ybox
nor any assumption on the unphysical H source is inserted. -/
theorem parity_original_weighted_Psi_physical_Ybox_eq_Y0_434
    (L U V : ℝ) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (H : ℕ → ℂ)
    (hU : 0<U) (hV : 0<V)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)<2*V) :
    (∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
      (((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)*H u) *
        (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
          alpha z.1*beta z.2)) =
    (∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
      (((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)*H u) *
        (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
          alpha z.1*beta z.2)) := by
  classical
  let Y0 := ⌊2*Real.exp L⌋₊
  let Ybox := Nat.ceil (6*U*V)
  let W : ℕ → ℂ := fun u =>
    (((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)*H u) *
      (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        alpha z.1*beta z.2)
  have hY0 (u : ℕ) (hu : Y0<u) : W u=0 := by
    have hPsiZero : Psi ((u:ℝ)/Real.exp L)=0 := by
      by_contra hh
      have h := parity_original_TypeII_psi_nonzero_u_le_old_Y0_434
        L Psi hPsi u hh
      omega
    simp [W,hPsiZero]
  have hYbox (u : ℕ) (hu : Ybox<u) : W u=0 := by
    have hFibre := parity_original_positive_pair_fibre_zero_beyond_true_Ybox434
      U V K J alpha beta u hU hV hK hJ hu
    simp [W,hFibre]
  have hLeft : (∑u∈Finset.Ioc 0 Y0,W u) =
      ∑u∈Finset.Ioc 0 (min Y0 Ybox),W u := by
    symm
    apply Finset.sum_subset
    · intro u hu
      exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hu).1,
        (Finset.mem_Ioc.mp hu).2.trans (min_le_left _ _)⟩
    · intro u hu huNot
      have huBeyond : Ybox<u := by
        have huY0 := (Finset.mem_Ioc.mp hu).2
        have hNot : ¬u ≤ min Y0 Ybox := by
          intro h
          exact huNot (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hu).1,h⟩)
        omega
      exact hYbox u huBeyond
  have hRight : (∑u∈Finset.Ioc 0 Ybox,W u) =
      ∑u∈Finset.Ioc 0 (min Ybox Y0),W u := by
    symm
    apply Finset.sum_subset
    · intro u hu
      exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hu).1,
        (Finset.mem_Ioc.mp hu).2.trans (min_le_left _ _)⟩
    · intro u hu huNot
      have huBeyond : Y0<u := by
        have huYbox := (Finset.mem_Ioc.mp hu).2
        have hNot : ¬u ≤ min Ybox Y0 := by
          intro h
          exact huNot (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hu).1,h⟩)
        omega
      exact hY0 u huBeyond
  change (∑u∈Finset.Ioc 0 Y0,W u) =
    (∑u∈Finset.Ioc 0 Ybox,W u)
  calc
    _ = ∑u∈Finset.Ioc 0 (min Y0 Ybox),W u := hLeft
    _ = ∑u∈Finset.Ioc 0 (min Ybox Y0),W u := by rw [min_comm]
    _ = _ := hRight.symm
end Green64Analytic.Parity

end

end

/-! ## HistoricalMellinPhysicalCapExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The genuine historical e-first Mellin integral after the actual
m*n=u+2 physical bilinear fibre is invariant under Y0/Ybox without
numeric Y0≤Ybox, for the ORIGINAL source Psi and fixed L/Q/P bands.
This is an equality AFTER real Mellin integration, not at fixed s. -/
theorem parity_original_true_physical_e_first_Psi_Mellin_Ybox_eq_Y0_noUVlower434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0<U) (hV : 0<V)
    (signed : Bool) (band : Fin (d+1)) (slot : Fin 20)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)<2*V) :
    (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      (∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) xi *
        (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
          alpha z.1*beta z.2))) =
    (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      (∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) xi *
        (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
          alpha z.1*beta z.2))) := by
  let W : ℕ → ℂ := fun u =>
    ∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
      alpha z.1*beta z.2
  have hPos (Y : ℕ) : ∀u∈Finset.Ioc 0 Y,0<u := by
    intro u hu
    exact (Finset.mem_Ioc.mp hu).1
  have hFubini (Y : ℕ) :=
    parity_original_intrinsic_e_first_Psi_Mellin_finite_u_fubini434
      d L E hL hd (Finset.Ioc 0 Y) (hPos Y) signed band slot xi
      Psi hSmooth hSupport W
  rw [hFubini (Nat.ceil (6*U*V)),
      hFubini ⌊2*Real.exp L⌋₊]
  have hCut := parity_original_weighted_Psi_physical_Ybox_eq_Y0_434
    L U V Psi hPsiSource K J alpha beta
      (fun u => parityOriginalSignedIntrinsicEFirstFullAtU434
        d L E u signed band slot 0 xi)
    hU hV hK hJ
  dsimp only [W] at hCut ⊢
  calc
    _ = ∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
      (((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
       parityOriginalSignedIntrinsicEFirstFullAtU434 d L E u signed band slot 0 xi) *
      (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        alpha z.1*beta z.2) := hCut.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      ring

/-- Source-exact original whole real Q-box transport under genuine
K/J physical support, with no fake cutoff inclusion and no UV lower
bound. Same original Mellin, Q frequencies, selected e and epsilon. -/
theorem parity_original_true_physical_historical_Cauchy_QBox_Ybox_eq_Y0_noUVlower434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0<U) (hV : 0<V)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)<2*V)
    (signed : Bool) (T : ℝ) :
    parityOriginalActualHistoricalPsiMellinCauchyQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed
      (Nat.ceil (6*U*V)) T =
    parityOriginalActualHistoricalPsiMellinCauchyQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed
      ⌊2*Real.exp L⌋₊ T := by
  have hEq (Y : ℕ) :
      parityOriginalActualHistoricalPsiMellinCauchyQBox434
        d L E band slot Psi hSmooth hSupport K J alpha beta signed Y T =
      parityOriginalSignedIntrinsicPsiPostIntegrated434
        d L E band slot Psi hSmooth hSupport K J alpha beta signed Y T := by
    rw [←parity_original_actual_historical_Psi_Bprime_QBox_eq_Cauchy_Mellin434]
    rw [←parity_original_signed_cartesian_Bprime_eq_historical_AE434]
    exact (parity_original_signed_intrinsic_Psi_post_eq_cartesian434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed Y T).symm
  rw [hEq (Nat.ceil (6*U*V)),hEq ⌊2*Real.exp L⌋₊]
  unfold parityOriginalSignedIntrinsicPsiPostIntegrated434
  apply integral_congr_ae
  filter_upwards [] with xi
  unfold parityOriginalSignedIntrinsicPsiBprimeAtXi434
  exact parity_original_true_physical_e_first_Psi_Mellin_Ybox_eq_Y0_noUVlower434
    d L E U V hL hd hU hV signed band slot xi Psi hSmooth hSupport
    hPsiSource K J alpha beta hK hJ
end Green64Analytic.Parity

end

end

/-! ## ActualBprimeFullQPhysicalCap -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Genuine ORIGINAL pre-Cauchy full Q-box Bprime (4.7), not its
post-Cauchy finite-u surrogate, is precisely Ybox/Y0 invariant
AFTER full Ψ Mellin, under literal shifted K/J physical caps.
No Y0<=Ybox or exp(L)<=UV is needed; all Q gates, signed branches,
selected e and the two integral orders are unchanged. -/
theorem parity_original_true_physical_cartesian_Bprime_fullQ_Ybox_eq_Y0_noUVlower434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0<U) (hV : 0<V)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)<2*V)
    (signed : Bool) (T : ℝ) :
    parityOriginalSignedCartesianPsiBprime434 d L E band slot
      Psi hSmooth hSupport K J alpha beta signed
      (Nat.ceil (6*U*V)) T =
    parityOriginalSignedCartesianPsiBprime434 d L E band slot
      Psi hSmooth hSupport K J alpha beta signed
      ⌊2*Real.exp L⌋₊ T := by
  rw [parity_original_actual_cartesian_Psi_Bprime_QBox_eq_Cauchy_Mellin434,
      parity_original_actual_cartesian_Psi_Bprime_QBox_eq_Cauchy_Mellin434]
  exact parity_original_true_physical_historical_Cauchy_QBox_Ybox_eq_Y0_noUVlower434
    d L E U V hL hd hU hV band slot Psi hSmooth hSupport hPsiSource
    K J alpha beta hK hJ signed T

/-- The source original signed pre-Cauchy Ψ-Mellin physical model
has the exact Ybox/Y0 equality BEFORE low/high frequency splitting.
This uses the genuine same-kernel intrinsic-to-Cartesian identity,
not a newly assumed source comparison interface. -/
theorem parity_original_true_physical_signed_Psi_postintegrated_Ybox_eq_Y0_noUVlower434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0<U) (hV : 0<V)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)<2*V)
    (signed : Bool) (T : ℝ) :
    parityOriginalSignedWindowPsiPostIntegrated434 d L E band slot
      Psi hSmooth hSupport K J alpha beta signed
      (Nat.ceil (6*U*V)) T =
    parityOriginalSignedWindowPsiPostIntegrated434 d L E band slot
      Psi hSmooth hSupport K J alpha beta signed
      ⌊2*Real.exp L⌋₊ T := by
  rw [parity_original_signed_intrinsic_Psi_Bprime_eq_source_postintegrated434
        d L E hL hd,
      parity_original_signed_intrinsic_Psi_Bprime_eq_source_postintegrated434
        d L E hL hd]
  rw [parity_original_signed_intrinsic_Psi_post_eq_cartesian434,
      parity_original_signed_intrinsic_Psi_post_eq_cartesian434]
  exact parity_original_true_physical_cartesian_Bprime_fullQ_Ybox_eq_Y0_noUVlower434
    d L E U V hL hd hU hV band slot Psi hSmooth hSupport hPsiSource
    K J alpha beta hK hJ signed T
end Green64Analytic.Parity

end

end

/-! ## AllSlotsPhysicalMellinCap -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- For one original chosen reserved Q-band, the COMPLEX sum over
all 20 source slots of the genuine signed physical postintegrated
Bprime is exactly Ybox/Y0 invariant, with no |sum| vs sum |slot|
claim and no lower bound on UV. Both signed epsilon branches stay
independently quantified and the whole source Mellin integral remains. -/
theorem parity_original_true_physical_allslots_signed_Psi_Ybox_eq_Y0_noUVlower434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0<U) (hV : 0<V)
    (band : Fin (d+1))
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)<2*V)
    (signed : Bool) (T : ℝ) :
    (∑slot : Fin 20,
      parityOriginalSignedWindowPsiPostIntegrated434 d L E band slot
        Psi hSmooth hSupport K J alpha beta signed
        (Nat.ceil (6*U*V)) T) =
    (∑slot : Fin 20,
      parityOriginalSignedWindowPsiPostIntegrated434 d L E band slot
        Psi hSmooth hSupport K J alpha beta signed
        ⌊2*Real.exp L⌋₊ T) := by
  apply Finset.sum_congr rfl
  intro slot hslot
  exact parity_original_true_physical_signed_Psi_postintegrated_Ybox_eq_Y0_noUVlower434
    d L E U V hL hd hU hV band slot Psi hSmooth hSupport hPsiSource
    K J alpha beta hK hJ signed T

/-- The same equality separately for each original signed ε branch,
then summed over BOTH branches without cross-branch estimates. -/
theorem parity_original_true_physical_allsigned_allslots_Psi_Ybox_eq_Y0_noUVlower434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0<U) (hV : 0<V)
    (band : Fin (d+1))
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)<2*V)
    (T : ℝ) :
    (∑signed : Bool, ∑slot : Fin 20,
      parityOriginalSignedWindowPsiPostIntegrated434 d L E band slot
        Psi hSmooth hSupport K J alpha beta signed
        (Nat.ceil (6*U*V)) T) =
    (∑signed : Bool, ∑slot : Fin 20,
      parityOriginalSignedWindowPsiPostIntegrated434 d L E band slot
        Psi hSmooth hSupport K J alpha beta signed
        ⌊2*Real.exp L⌋₊ T) := by
  apply Finset.sum_congr rfl
  intro signed hsigned
  exact parity_original_true_physical_allslots_signed_Psi_Ybox_eq_Y0_noUVlower434
    d L E U V hL hd hU hV band Psi hSmooth hSupport hPsiSource
    K J alpha beta hK hJ signed T
end Green64Analytic.Parity

end

end

/-! ## QuarterPhysicalYboxNClosed -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 1900000

/-- Exact positive shifted m*n=u+2 physical u support for genuine
source beta dyads V≤n≤2V, including the right endpoint n=2V.
No lower UV bound, no strict upper beta assumption and no fake Y0≤Ybox. -/
theorem parity_original_TypeII_true_physical_u_le_Ybox_nclosed434
    (U V : ℝ) (m n u : ℕ)
    (hU : 0<U) (hV : 0<V)
    (hm : (m:ℝ)<2*U) (hn : (n:ℝ)≤2*V)
    (hEq : m*n=u+2) :
    u ≤ Nat.ceil (6*U*V) := by
  have hm0 : 0≤(m:ℝ) := Nat.cast_nonneg _
  have hn0 : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hProd : (m:ℝ)*(n:ℝ) ≤ (2*U)*(2*V) := by
    calc
      _ ≤ (2*U)*(n:ℝ) :=
        mul_le_mul_of_nonneg_right hm.le hn0
      _ ≤ (2*U)*(2*V) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
  have heq : (m:ℝ)*(n:ℝ)=(u:ℝ)+2 := by exact_mod_cast hEq
  have hCeil : 6*U*V≤((Nat.ceil (6*U*V)):ℝ) := Nat.le_ceil _
  have hUV : 0<U*V := mul_pos hU hV
  have hu : (u:ℝ)≤((Nat.ceil (6*U*V)):ℝ) := by
    nlinarith [hProd,heq,hCeil,hUV]
  exact_mod_cast hu

theorem parity_original_positive_pair_fibre_zero_beyond_true_Ybox_nclosed434
    (U V : ℝ) (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (u : ℕ)
    (hU : 0<U) (hV : 0<V)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)≤2*V)
    (hFar : Nat.ceil (6*U*V)<u) :
    (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
      alpha z.1*beta z.2)=0 := by
  apply Finset.sum_eq_zero
  intro z hz
  have h := Finset.mem_filter.mp hz
  have hmem := Finset.mem_product.mp h.1
  rcases h.2 with ⟨hm,hn,heq⟩
  have hY := parity_original_TypeII_true_physical_u_le_Ybox_nclosed434
    U V z.1 z.2 u hU hV (hK z.1 hmem.1) (hJ z.2 hmem.2) heq
  omega

/-- General original Ψ-weighted physical bilinear sum, with any
extra complex weight H(u) (e.g., actual post-Mellin e-first source),
is EXACTLY invariant under Y0↔Ybox. Neither a fabricated Y0⊆Ybox
nor any assumption on the unphysical H source is inserted. -/
theorem parity_original_weighted_Psi_physical_Ybox_eq_Y0_nclosed434
    (L U V : ℝ) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (H : ℕ → ℂ)
    (hU : 0<U) (hV : 0<V)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)≤2*V) :
    (∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
      (((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)*H u) *
        (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
          alpha z.1*beta z.2)) =
    (∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
      (((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)*H u) *
        (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
          alpha z.1*beta z.2)) := by
  classical
  let Y0 := ⌊2*Real.exp L⌋₊
  let Ybox := Nat.ceil (6*U*V)
  let W : ℕ → ℂ := fun u =>
    (((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)*H u) *
      (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        alpha z.1*beta z.2)
  have hY0 (u : ℕ) (hu : Y0<u) : W u=0 := by
    have hPsiZero : Psi ((u:ℝ)/Real.exp L)=0 := by
      by_contra hh
      have h := parity_original_TypeII_psi_nonzero_u_le_old_Y0_434
        L Psi hPsi u hh
      omega
    simp [W,hPsiZero]
  have hYbox (u : ℕ) (hu : Ybox<u) : W u=0 := by
    have hFibre := parity_original_positive_pair_fibre_zero_beyond_true_Ybox_nclosed434
      U V K J alpha beta u hU hV hK hJ hu
    simp [W,hFibre]
  have hLeft : (∑u∈Finset.Ioc 0 Y0,W u) =
      ∑u∈Finset.Ioc 0 (min Y0 Ybox),W u := by
    symm
    apply Finset.sum_subset
    · intro u hu
      exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hu).1,
        (Finset.mem_Ioc.mp hu).2.trans (min_le_left _ _)⟩
    · intro u hu huNot
      have huBeyond : Ybox<u := by
        have huY0 := (Finset.mem_Ioc.mp hu).2
        have hNot : ¬u ≤ min Y0 Ybox := by
          intro h
          exact huNot (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hu).1,h⟩)
        omega
      exact hYbox u huBeyond
  have hRight : (∑u∈Finset.Ioc 0 Ybox,W u) =
      ∑u∈Finset.Ioc 0 (min Ybox Y0),W u := by
    symm
    apply Finset.sum_subset
    · intro u hu
      exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hu).1,
        (Finset.mem_Ioc.mp hu).2.trans (min_le_left _ _)⟩
    · intro u hu huNot
      have huBeyond : Y0<u := by
        have huYbox := (Finset.mem_Ioc.mp hu).2
        have hNot : ¬u ≤ min Ybox Y0 := by
          intro h
          exact huNot (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hu).1,h⟩)
        omega
      exact hY0 u huBeyond
  change (∑u∈Finset.Ioc 0 Y0,W u) =
    (∑u∈Finset.Ioc 0 Ybox,W u)
  calc
    _ = ∑u∈Finset.Ioc 0 (min Y0 Ybox),W u := hLeft
    _ = ∑u∈Finset.Ioc 0 (min Ybox Y0),W u := by rw [min_comm]
    _ = _ := hRight.symm
end Green64Analytic.Parity

end

end

/-! ## QuarterHistoricalMellinNClosed -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2300000

/-- Exact original e-first Psi Mellin and full Q-box after the
physical n≤2V BETA endpoint, preserving same L and actual Ybox. -/
theorem parity_original_true_physical_e_first_Psi_Mellin_Ybox_eq_Y0_nclosed434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0<U) (hV : 0<V)
    (signed : Bool) (band : Fin (d+1)) (slot : Fin 20)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)≤2*V) :
    (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      (∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) xi *
        (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
          alpha z.1*beta z.2))) =
    (∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
      L Psi hSmooth hSupport s *
      (∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) xi *
        (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
          alpha z.1*beta z.2))) := by
  let W : ℕ → ℂ := fun u =>
    ∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
      alpha z.1*beta z.2
  have hPos (Y : ℕ) : ∀u∈Finset.Ioc 0 Y,0<u := by
    intro u hu
    exact (Finset.mem_Ioc.mp hu).1
  have hFubini (Y : ℕ) :=
    parity_original_intrinsic_e_first_Psi_Mellin_finite_u_fubini434
      d L E hL hd (Finset.Ioc 0 Y) (hPos Y) signed band slot xi
      Psi hSmooth hSupport W
  rw [hFubini (Nat.ceil (6*U*V)),
      hFubini ⌊2*Real.exp L⌋₊]
  have hCut := parity_original_weighted_Psi_physical_Ybox_eq_Y0_nclosed434
    L U V Psi hPsiSource K J alpha beta
      (fun u => parityOriginalSignedIntrinsicEFirstFullAtU434
        d L E u signed band slot 0 xi)
    hU hV hK hJ
  dsimp only [W] at hCut ⊢
  calc
    _ = ∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
      (((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
       parityOriginalSignedIntrinsicEFirstFullAtU434 d L E u signed band slot 0 xi) *
      (∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        alpha z.1*beta z.2) := hCut.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      ring

/-- Source-exact original whole real Q-box transport under genuine
K/J physical support, with no fake cutoff inclusion and no UV lower
bound. Same original Mellin, Q frequencies, selected e and epsilon. -/
theorem parity_original_true_physical_historical_Cauchy_QBox_Ybox_eq_Y0_nclosed434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0<U) (hV : 0<V)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSource : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (hK : ∀m∈K,(m:ℝ)<2*U)
    (hJ : ∀n∈J,(n:ℝ)≤2*V)
    (signed : Bool) (T : ℝ) :
    parityOriginalActualHistoricalPsiMellinCauchyQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed
      (Nat.ceil (6*U*V)) T =
    parityOriginalActualHistoricalPsiMellinCauchyQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed
      ⌊2*Real.exp L⌋₊ T := by
  have hEq (Y : ℕ) :
      parityOriginalActualHistoricalPsiMellinCauchyQBox434
        d L E band slot Psi hSmooth hSupport K J alpha beta signed Y T =
      parityOriginalSignedIntrinsicPsiPostIntegrated434
        d L E band slot Psi hSmooth hSupport K J alpha beta signed Y T := by
    rw [←parity_original_actual_historical_Psi_Bprime_QBox_eq_Cauchy_Mellin434]
    rw [←parity_original_signed_cartesian_Bprime_eq_historical_AE434]
    exact (parity_original_signed_intrinsic_Psi_post_eq_cartesian434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed Y T).symm
  rw [hEq (Nat.ceil (6*U*V)),hEq ⌊2*Real.exp L⌋₊]
  unfold parityOriginalSignedIntrinsicPsiPostIntegrated434
  apply integral_congr_ae
  filter_upwards [] with xi
  unfold parityOriginalSignedIntrinsicPsiBprimeAtXi434
  exact parity_original_true_physical_e_first_Psi_Mellin_Ybox_eq_Y0_nclosed434
    d L E U V hL hd hU hV signed band slot xi Psi hSmooth hSupport
    hPsiSource K J alpha beta hK hJ
end Green64Analytic.Parity

end

end

/-! ## QuarterSourceToCapfreePsiMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Original signed source pre-Cauchy real Psi plus Q-box comparison
with genuine full physical beta n≤2V endpoint and expL≤4UV,
using source exact Ybox↔Y0 after Mellin, no false numeric inclusion. -/
theorem parity_eventually_original_signed_source_to_actual_capfree_Psi_Mellin_Bprime_quarter434
    (betaP A : ℝ) (hbetaP : 0<betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E U V : ℝ), 1≤E → E≤Real.exp ((1-betaP)*L) →
        0<U → 0<V → Real.exp L≤4*U*V →
      ∀ (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
        (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ))),
        (∀t,0≤Psi t) → (∀t,Psi t≤1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0≤Acoef → 0≤Bcoef →
        (∀m∈K, ‖alpha m‖≤Acoef) → (∀n∈J, ‖beta n‖≤Bcoef) →
        (∀m∈K,(m:ℝ)<2*U) → (∀n∈J,(n:ℝ)≤2*V) →
      ∀ (signed : Bool),
      ‖parityOriginalShiftTwoSignedBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J alpha beta signed 0
          ⌊2*Real.exp L⌋₊ -
        parityOriginalActualPsiMellinCapfreeBprimeQBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi hSmooth (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
          K J alpha beta signed L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_source_to_historical_Psi_Mellin_Cauchy_QBox_all_log434
    betaP A hbetaP jQ hBand,
    parity_eventually_original_cartesian_selected_e_odd_unit434] with L hOld hOdd
  refine ⟨hOld.1,hOld.2.1,?_⟩
  intro band hb E U V hE hEhi hU hV hUV Psi hSupport hSmooth
    hPsiPos hPsiLe slot K J alpha beta Acoef Bcoef hAcoef hBcoef
    hAlpha hBeta hK hJ signed
  have hSelected :
      ∀ (δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ,0<e := by
    intro δ e he
    have he0 : e∈parityOriginalReservedCartesianESupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ :=
      (Finset.mem_filter.mp he).1
    exact (hOdd.2 band slot δ e he0).2.1
  have hL : 0<L := by nlinarith [hOld.1]
  have hCut := parity_original_true_physical_historical_Cauchy_QBox_Ybox_eq_Y0_nclosed434
    (sourceOriginalLiteralDepth 20 L) L E U V hL rfl hU hV
    band slot Psi hSmooth
    (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
    hSupport K J alpha beta hK hJ signed L
  have hEq := parity_original_actual_historical_Psi_Mellin_Ybox_eq_capfree434
    (sourceOriginalLiteralDepth 20 L) L E U V hL hU.le hV.le
    band slot hSelected K J
    (by intro m hm; exact (hK m hm).le)
    (by intro n hn; linarith [(hJ n hn)])
    Psi hSmooth (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
    alpha beta signed L
  have hBound := hOld.2.2 band hb E hE hEhi Psi hSupport hSmooth
    hPsiPos hPsiLe slot K J alpha beta Acoef Bcoef hAcoef hBcoef
    hAlpha hBeta signed
  rw [←hCut,hEq] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## TrueYboxShiftedTauNoUVLower -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The original shifted-divisor quadratic moment is uniformly
polynomial at the ACTUAL cap-free Parity(4.10) cutoff
Ybox=ceil(6UV), for all physical positive U,V with UV<=Cbox exp L, no lower bound on UV.
No extension by pointwise s cutoff: this is an independent
POSITIVE arithmetic estimate from the genuine fourth divisor moment.
Its exponent 16 is fixed before TypeII precision; Cbox affects only
the eventual lower threshold for L. -/
theorem parity_eventually_original_true_Ybox_shifted_tau_square_polylog_noUVlower434
    (Cbox : ℝ) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop,
      1≤L ∧ ∀ (U V : ℝ),
      0<U → 0<V → U*V≤Cbox*Real.exp L →
      let Y := Nat.ceil (6*U*V)
      (∑u∈Finset.Ioc 0 Y, (((u+2).divisors.card:ℝ)^2)) ≤
        Real.exp L*L^16 := by
  let D : ℝ := 6*Cbox+3
  have hD : 0<D := by dsimp [D]; linarith
  have hT : 1≤(3:ℝ)^15 := by norm_num
  filter_upwards [eventually_ge_atTop (max 1 (D*(3:ℝ)^15))]
    with L hL
  have hLone : 1≤L := (le_max_left _ _).trans hL
  have hLD : D≤L := by
    have hh := mul_le_mul_of_nonneg_left hT hD.le
    have hLpow := (le_max_right (1:ℝ) (D*(3:ℝ)^15)).trans hL
    nlinarith
  refine ⟨hLone,?_⟩
  intro U V hU hV hUVhi
  let Y := Nat.ceil (6*U*V)
  have hExp : 0<Real.exp L := Real.exp_pos _
  have hExpOne : 1≤Real.exp L := by
    have hh := Real.add_one_le_exp L
    linarith
  have hY0 : 0≤6*U*V := by positivity
  have hCeil : (Y:ℝ)<6*U*V+1 := Nat.ceil_lt_add_one hY0
  have hYhigh : ((Y+2:ℕ):ℝ)≤D*Real.exp L := by
    dsimp [D]
    push_cast
    nlinarith [hCeil,hUVhi,hExpOne]
  have hYpos : 0<((Y+2:ℕ):ℝ) := by
    exact_mod_cast (show 0<Y+2 by omega)
  have hYone : 1≤((Y+2:ℕ):ℝ) := by
    exact_mod_cast (show 1≤Y+2 by omega)
  have hLogUpper : Real.log ((Y+2:ℕ):ℝ) ≤ Real.log D+L := by
    have hh := Real.log_le_log hYpos hYhigh
    rw [Real.log_mul hD.ne' (Real.exp_ne_zero L),Real.log_exp] at hh
    exact hh
  have hLogD : Real.log D≤D-1 := Real.log_le_sub_one_of_pos hD
  have hLogLow : 0≤1+Real.log ((Y+2:ℕ):ℝ) := by
    have hh := Real.log_nonneg hYone
    linarith
  have hLogHigh : 1+Real.log ((Y+2:ℕ):ℝ)≤3*L := by
    linarith [hLogUpper,hLogD,hLD,hLone]
  have hDivMoment := parity_original_shift_two_divisor_square_moment434 Y
  have hPower : (3*L)^15=(3:ℝ)^15*L^15 := by ring
  calc
    (∑u∈Finset.Ioc 0 Y, (((u+2).divisors.card:ℝ)^2)) ≤
      ((Y+2:ℕ):ℝ)*(1+Real.log ((Y+2:ℕ):ℝ))^15 := hDivMoment
    _ ≤ (D*Real.exp L)*(3*L)^15 :=
      mul_le_mul hYhigh (pow_le_pow_left₀ hLogLow hLogHigh 15)
        (pow_nonneg (by positivity) _) (by positivity)
    _ = (D*(3:ℝ)^15)*Real.exp L*L^15 := by rw [hPower]; ring
    _ ≤ L*Real.exp L*L^15 := by
      have hDpow : D*(3:ℝ)^15≤L :=
        (le_max_right (1:ℝ) (D*(3:ℝ)^15)).trans hL
      have hPositive : 0≤Real.exp L*L^15 :=
        mul_nonneg hExp.le (pow_nonneg (by linarith : 0≤L) 15)
      convert (mul_le_mul_of_nonneg_right hDpow hPositive) using 1 <;> ring
    _ = Real.exp L*L^16 := by ring

/-- The entire ORIGINAL moving P-group W1(P,u) times shifted
τ(u+2) source factorization mass is uniformly polylog at the
ACTUAL cap-free Ybox=ceil(6UV), not only old Y0=floor(2x).
No bounded-u restriction is suppressed at fixed Mellin frequency.
The bound remains exp(L)L^(C_W1+16), for every FIXED Cbox≥1,
with exactly the original all-P group divisor weight. -/
theorem parity_eventually_original_true_Ybox_W1_shifted_tau_polylog_noUVlower434
    (Cbox : ℝ) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop,
      1≤L ∧ ∀ (U V : ℝ),
      0<U → 0<V → U*V≤Cbox*Real.exp L →
      let Y := Nat.ceil (6*U*V)
      (∑u∈Finset.Ioc 0 Y,
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) ≤
        Real.exp L*L^parityOriginalW1PolylogExponent434*L^16 := by
  filter_upwards [parity_eventually_original_true_Ybox_shifted_tau_square_polylog_noUVlower434
      Cbox hCbox,
    parity_eventually_original_actual_W1_pointwise_polylog434]
    with L hMoment hW1
  refine ⟨hMoment.1,?_⟩
  intro U V hU hV hUVhi
  let Y := Nat.ceil (6*U*V)
  have hL : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hMoment.1
  have hWpos : 0≤L^parityOriginalW1PolylogExponent434 := by positivity
  have hFirst := parity_original_shift_two_tau_first_le_second_moment434 Y
  have hSecond := hMoment.2 U V hU hV hUVhi
  calc
    (∑u∈Finset.Ioc 0 Y,
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        ((u+2).divisors.card:ℝ)) ≤
      (∑u∈Finset.Ioc 0 Y,
        L^parityOriginalW1PolylogExponent434 * ((u+2).divisors.card:ℝ)) := by
          apply Finset.sum_le_sum
          intro u hu
          exact mul_le_mul_of_nonneg_right (hW1 u) (Nat.cast_nonneg _)
    _ = L^parityOriginalW1PolylogExponent434 *
      (∑u∈Finset.Ioc 0 Y, ((u+2).divisors.card:ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ L^parityOriginalW1PolylogExponent434 *
      (∑u∈Finset.Ioc 0 Y, (((u+2).divisors.card:ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hFirst hWpos
    _ ≤ L^parityOriginalW1PolylogExponent434 * (Real.exp L*L^16) :=
      mul_le_mul_of_nonneg_left hSecond hWpos
    _ = Real.exp L*L^parityOriginalW1PolylogExponent434*L^16 := by ring
end Green64Analytic.Parity

end

end

/-! ## TrueYboxAllSlotsNoUVLower -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- TRUE expanded Parity(4.10) cap-free physical Ybox=ceil(6UV)
shifted-divisor τ(u+2) / B590 Fourier source mass, integrated over
ALL its original Q frequency cubes, Boolean allocations and all
20 reserved slots. This is an independent POSITIVE enlarged-carrier
estimate, valid already at fixed real Mellin rho, not a fabricated
pointwise equality of the Y0 and Ybox e/n source sums. The original
factorial and Q selected/skipped prime information stays INSIDE W1;
no extra Q Fourier gate or L^S fine-cell loss. Cbox>=1 fixed first;
precision-independent log exponent CW1+16+CF unchanged. -/
theorem parity_eventually_original_true_Ybox_signed_fullQ_tau_allslots_polylog_noUVlower434
    (Cbox : ℝ) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0<U → 0<V →
        U*V≤Cbox*Real.exp L →
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)),
      (∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 L,
            ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                (sourceOriginalLiteralDepth 20 L) L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) ≤
        20*Real.exp L*L^parityOriginalW1PolylogExponent434*L^16*
          L^parityOriginalB590FixedFourierPolynomialExponent434 := by
  filter_upwards [parity_eventually_original_true_Ybox_W1_shifted_tau_polylog_noUVlower434
      Cbox hCbox,
    parity_eventually_original_actual_post_cauchy_Q_gate_L1_polylog434]
    with L hTau hGate
  refine ⟨hTau.1,?_⟩
  intro U V hU hV hUVhi E signed band
  have hL : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hTau.1
  let d := sourceOriginalLiteralDepth 20 L
  let Y := Nat.ceil (6*U*V)
  let Mass := ∑u∈Finset.Ioc 0 Y,
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      ((u+2).divisors.card:ℝ)
  let B := Real.exp L*L^parityOriginalW1PolylogExponent434*L^16
  let C := L^parityOriginalB590FixedFourierPolynomialExponent434
  have hMass : 0≤Mass := by
    dsimp [Mass]
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (source_original_W1_nonneg _ _) (Nat.cast_nonneg _)
  have hMassB : Mass≤B := hTau.2 U V hU hV hUVhi
  have hB : 0≤B := by dsimp [B]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have hSlot (slot : Fin 20) :
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 L,
            ∑u∈Finset.Ioc 0 Y,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) ≤ B*C := by
    let n := (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length
    have hOne (delta : Fin n → Bool) :
        (∫xi in parityOriginalActualFullQFrequencyCube434 L,
            ∑u∈Finset.Ioc 0 Y,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) ≤
        Mass*(∫xi : Fin n → ℝ,
          ‖parityOriginalActualPostCauchyQGate434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) xi delta‖) :=
      parity_original_signed_fullQ_tau_Qcube_integral_le_W1_L1434
        d L E L hL signed band slot delta Y
    have hGateOne := hGate band slot E
    dsimp only at hGateOne
    calc
      _ ≤ ∑delta : Fin n → Bool,
        Mass*(∫xi : Fin n → ℝ,
          ‖parityOriginalActualPostCauchyQGate434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) xi delta‖) := by
          apply Finset.sum_le_sum
          intro delta hdelta
          exact hOne delta
      _ = Mass*(∑delta : Fin n → Bool,
          ∫xi : Fin n → ℝ,
            ‖parityOriginalActualPostCauchyQGate434 E
              (sourceActualSortedFrequencyScales 20 d L band slot) xi delta‖) := by
          rw [Finset.mul_sum]
      _ ≤ Mass*C := mul_le_mul_of_nonneg_left hGateOne hMass
      _ ≤ B*C := mul_le_mul_of_nonneg_right hMassB hC
  have hAll :
      (∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 L,
            ∑u∈Finset.Ioc 0 Y,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) ≤ 20*(B*C) := by
    calc
      _ ≤ ∑_slot : Fin 20, B*C := by
        apply Finset.sum_le_sum
        intro slot hslot
        exact hSlot slot
      _ = 20*(B*C) := by simp
  calc
    _ ≤ 20*(B*C) := by simpa only [d,Y] using hAll
    _ = 20*Real.exp L*L^parityOriginalW1PolylogExponent434*L^16*
        L^parityOriginalB590FixedFourierPolynomialExponent434 := by
          dsimp [B,C]
          ring

/-- The full physical one-slot Q-frequency arithmetic τ mass at
TRUE Ybox is O(exp L L^(CW1+16+CF)), with harmless constant 20.
Uniform in arbitrary original slot, reserved band, E and signed
ε, and physical U,V in one Cbox dyadic slab. This source bound is
strong enough to pay one-slot high-Ψ-Mellin tails without confusing
the original source (one reserved slot) with a COMPLEX sum of slots. -/
theorem parity_eventually_original_true_Ybox_single_slot_tau_polylog_noUVlower434
    (Cbox : ℝ) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0<U → 0<V →
        U*V≤Cbox*Real.exp L →
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1))
        (slot : Fin 20),
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 L,
          ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
            ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
              (sourceOriginalLiteralDepth 20 L) L E u signed band slot delta xi‖ *
            ((u+2).divisors.card:ℝ)) ≤
      20*Real.exp L*L^parityOriginalW1PolylogExponent434*L^16*
        L^parityOriginalB590FixedFourierPolynomialExponent434 := by
  filter_upwards [parity_eventually_original_true_Ybox_signed_fullQ_tau_allslots_polylog_noUVlower434
    Cbox hCbox] with L hTotal
  refine ⟨hTotal.1,?_⟩
  intro U V hU hV hUVhi E signed band slot
  exact (parity_original_true_Ybox_single_slot_tau_le_allslots434
    (sourceOriginalLiteralDepth 20 L) L E U V signed band slot L).trans
      (hTotal.2 U V hU hV hUVhi E signed band)
end Green64Analytic.Parity

end

end

/-! ## TrueYboxHighMellinNoUVLower -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The complete ACTUAL extended Parity(4.10) Ybox=ceil6UV
20-slot original Q-integrated B590 shifted tau(u+2) mass, times
the genuine source Psi-Schwartz high-s Mellin moment R^-H M_H,
has arbitrary O_A(exp L L^-A) saving uniformly in physical U,V.
The Schwarz order H depends on A and C0, and is fixed before L;
Cbox>=1 is fixed first. This is an arithmetic budget statement,
NOT an equality Y0=Ybox for each fixed Mellin s and NOT by itself
a complex high-tail norm bound. -/
theorem parity_eventually_original_true_Ybox_signed_tau_Schwartz_moment_paid_noUVlower434
    (Cbox A C0 : ℝ) (hCbox : 1≤Cbox) (hC0 : 0<C0)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ∃ H : ℕ, ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0<U → 0<V →
        U*V≤Cbox*Real.exp L →
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)),
      let M_H := ∫s : ℝ, ‖s‖^H *
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
      (((L^C0/(2*Real.pi))^H)⁻¹ * M_H) *
        (∑slot : Fin 20,
          ∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
              band slot).length → Bool,
            ∫xi in parityOriginalActualFullQFrequencyCube434 L,
              ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
                ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                  (sourceOriginalLiteralDepth 20 L) L E u signed band slot delta xi‖ *
                ((u+2).divisors.card:ℝ)) ≤
      (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-A) := by
  let Cmass : ℝ := parityOriginalW1PolylogExponent434+16+
    parityOriginalB590FixedFourierPolynomialExponent434
  obtain ⟨H,hPrecision⟩ :=
    parity_original_true_mellin_moment_order_exists434 A Cmass C0 hC0
  refine ⟨H,?_⟩
  filter_upwards [parity_eventually_original_true_Ybox_signed_fullQ_tau_allslots_polylog_noUVlower434
      Cbox hCbox] with L hSource
  refine ⟨hSource.1,?_⟩
  intro U V hU hV hUVhi E signed band
  have hL : 1≤L := hSource.1
  let M_H : ℝ := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
  have hM : 0≤M_H := by
    dsimp [M_H]
    apply integral_nonneg
    intro s
    positivity
  have hLp : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hL
  have hR : 0<L^C0/(2*Real.pi) :=
    div_pos (Real.rpow_pos_of_pos hLp _) (by positivity)
  have hCoeff : 0≤((L^C0/(2*Real.pi))^H)⁻¹*M_H := by positivity
  have hMass := hSource.2 U V hU hV hUVhi E signed band
  have hPrec : Cmass+A≤C0*(H:ℝ) := by linarith [hPrecision]
  have hPower := parity_original_true_mellin_tail_source_mass_absorption434
    L C0 A Cmass M_H H hL hM hPrec
  have hRPow :
      L^parityOriginalW1PolylogExponent434*L^16*
        L^parityOriginalB590FixedFourierPolynomialExponent434 = L^Cmass := by
    dsimp [Cmass]
    rw [Real.rpow_add hLp,Real.rpow_add hLp]
    rw [←Real.rpow_natCast]
    ring
  dsimp only at hMass ⊢
  calc
    _ ≤ (((L^C0/(2*Real.pi))^H)⁻¹*M_H) *
          (20*Real.exp L*L^Cmass) := by
          apply mul_le_mul_of_nonneg_left _ hCoeff
          calc
            _ ≤ 20*Real.exp L*L^parityOriginalW1PolylogExponent434*L^16*
                  L^parityOriginalB590FixedFourierPolynomialExponent434 := hMass
            _ = 20*Real.exp L*L^Cmass := by
              rw [←hRPow]
              ring
    _ ≤ (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-A) := hPower

/-- The complex original historical Parity(4.7) high-|s| Ψ-Mellin
integral has arbitrary O_A(exp(L)L^-A) saving even at the ACTUAL
capfree Ybox=ceil(6UV), uniformly for all U,V in the original
dyadic slab exp L<=UV<=Cbox exp L. All 20 reserved Q slots and
Boolean allocations, original h=-2 and epsilon source branches,
real 2πs Mellin and full Q-cube remain literal. True source
W1(P,u) tau(u+2) is paid uniformly up to Ybox; it is NOT asserted
that the Y0 and Ybox fixed-s integrands coincide.
H is selected once before L and the same log exponent pays both
Y0/Ybox expanded historical tails. Full TypeII still OPEN. -/
theorem parity_eventually_original_true_Ybox_historical_high_Psi_Mellin_Q_anylog_noUVlower434
    (Cbox goal C0 : ℝ) (hCbox : 1≤Cbox) (hC0 : 0<C0)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ∃ H : ℕ, ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0<U → 0<V →
        U*V≤Cbox*Real.exp L →
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1))
        (K J : Finset ℕ) (alpha beta : ℕ → ℂ),
        (∀m∈K,‖alpha m‖≤1) →
        (∀n∈J,‖beta n‖≤1) →
      let d := sourceOriginalLiteralDepth 20 L
      let Ybox := Nat.ceil (6*U*V)
      let R := L^C0/(2*Real.pi)
      let M_H := ∫s : ℝ, ‖s‖^H *
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
      ‖∫s in {s : ℝ | R≤‖s‖},
        parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
        (∑slot : Fin 20,
          ∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → Bool,
            ∫xi in parityOriginalActualFullQFrequencyCube434 L,
              parityOriginalHistoricalCauchyAtDelta434
                d L E band slot delta xi (2*Real.pi*s)
                  K J alpha beta signed Ybox)‖ ≤
        (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
  obtain ⟨H,hSource⟩ :=
    parity_eventually_original_true_Ybox_signed_tau_Schwartz_moment_paid_noUVlower434
      Cbox goal C0 hCbox hC0 Psi hSmooth hSupport
  refine ⟨H,?_⟩
  filter_upwards [hSource] with L hSourceL
  refine ⟨hSourceL.1,?_⟩
  intro U V hU hV hUVhi E signed band K J alpha beta hAlpha hBeta
  let d := sourceOriginalLiteralDepth 20 L
  let Ybox := Nat.ceil (6*U*V)
  let R := L^C0/(2*Real.pi)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
  let M : ℝ := ∑slot : Fin 20,
    ∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 L,
        ∑u∈Finset.Ioc 0 Ybox,
          ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
            d L E u signed band slot delta xi‖ *
          ((u+2).divisors.card:ℝ)
  have hLp : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hSourceL.1
  have hR : 0<R := by
    dsimp [R]
    exact div_pos (Real.rpow_pos_of_pos hLp _) (by positivity)
  have hHigh := parity_original_historical_allslots_high_Psi_Mellin_Q_tau_bound434
    d L E hLp rfl band K J alpha beta signed Ybox L 1 1
    (by norm_num) (by norm_num) hAlpha hBeta
    Psi hSmooth hSupport R hR H
  have hMass := hSourceL.2 U V hU hV hUVhi E signed band
  dsimp only at hMass hHigh ⊢
  calc
    _ ≤ ((1:ℝ)*1*M)*((R^H)⁻¹*M_H) := by
      simpa only [M,R,M_H,d,Ybox,mul_assoc] using hHigh
    _ = ((R^H)⁻¹*M_H)*M := by ring
    _ ≤ (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
      simpa only [M,R,M_H,d,Ybox] using hMass
end Green64Analytic.Parity

end

end

/-! ## TrueYboxCapfreeHighNoUVLower -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- TRUE original cap-free Bprime Q-Mellin **complex** high-|s|
Ψ tail, with the actual no-u-cap Parity(4.10) source expression,
retaining all 20 reserved Q slots and Boolean allocations.
Uniform inverse-log O_A(exp L L^-A) follows from independently
proved complete Ybox=ceil6UV shifted-τ mass and exact historical↔
capfree SOURCE equality at Ybox, NOT from false Y0=Ybox pointwise.
Actual selected-e positive source and dyadic K/J bounds are explicit
use-site hypotheses; the paper's original §4/§7 supplies these
before the final assembled TypeII result. -/
theorem parity_eventually_original_true_Ybox_capfree_high_Psi_Mellin_Q_anylog_noUVlower434
    (Cbox goal C0 : ℝ) (hCbox : 1≤Cbox) (hC0 : 0<C0)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ∃ H : ℕ, ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0<U → 0<V →
        U*V≤Cbox*Real.exp L →
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1))
        (K J : Finset ℕ) (alpha beta : ℕ → ℂ),
        (∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
              band slot).length → Bool),
          ∀e∈parityOriginalHistoricalCauchyActiveESupport434
            (sourceOriginalLiteralDepth 20 L) L E band slot delta,0<e) →
        (∀m∈K,(m:ℝ)≤2*U) →
        (∀n∈J,(n:ℝ)≤3*V) →
        (∀m∈K,‖alpha m‖≤1) →
        (∀n∈J,‖beta n‖≤1) →
      let d := sourceOriginalLiteralDepth 20 L
      let Ybox := Nat.ceil (6*U*V)
      let R := L^C0/(2*Real.pi)
      let M_H := ∫s : ℝ, ‖s‖^H *
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
      ‖∫s in {s : ℝ | R≤‖s‖},
        parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
        (∑slot : Fin 20,
          ∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → Bool,
            ∫xi in parityOriginalActualFullQFrequencyCube434 L,
              parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                d L E band slot delta xi (2*Real.pi*s)
                  K J alpha beta signed)‖ ≤
        (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
  obtain ⟨H,hOld⟩ :=
    parity_eventually_original_true_Ybox_historical_high_Psi_Mellin_Q_anylog_noUVlower434
      Cbox goal C0 hCbox hC0 Psi hSmooth hSupport
  refine ⟨H,?_⟩
  filter_upwards [hOld] with L hLold
  rcases hLold with ⟨hL1,hRest⟩
  refine ⟨hL1,?_⟩
  intro U V hU hV hUVhi E signed band K J alpha beta
    hSelected hK hJ hAlpha hBeta
  let d := sourceOriginalLiteralDepth 20 L
  let R := L^C0/(2*Real.pi)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
  have hLp : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hL1
  have hEq := parity_original_true_Ybox_allslots_high_Psi_Mellin_hist_eq_capfree434
    d L E U V hLp hU.le hV.le band hSelected K J hK hJ alpha beta signed
    Psi hSmooth hSupport R L
  have hBound := hRest U V hU hV hUVhi E signed band
    K J alpha beta hAlpha hBeta
  dsimp only at hBound ⊢
  rw [hEq] at hBound
  simpa only [d,R,M_H] using hBound

/-- The original Parity(4.7) **ONE reserved Q slot** cap-free Bprime
HIGH-Ψ-Mellin complex integral has arbitrary O_A(exp L L^-A) saving
uniformly in expL<=UV<=Cbox expL. Its own positive weighted τ source
mass is bounded using `single_le_sum` BEFORE multiplication by the
Schwartz moment. This does NOT use the invalid |one complex slot|≤
|sum of complex slots| comparison. It is SOURCE-correct for the
specific reserved slot used by the original pre-Cauchy approximation.
The true Ybox=ceil6UV, original 2πs, full Q allocations and
selected-e positivity/cofactor K,J supports are retained.
H is chosen before L. Not yet general TypeII(4.2). -/
theorem parity_eventually_original_true_Ybox_capfree_single_slot_high_anylog_noUVlower434
    (Cbox goal C0 : ℝ) (hCbox : 1≤Cbox) (hC0 : 0<C0)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ∃ H : ℕ, ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0<U → 0<V →
        U*V≤Cbox*Real.exp L →
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1))
        (slot : Fin 20)
        (K J : Finset ℕ) (alpha beta : ℕ → ℂ),
        (∀ (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
              band slot).length → Bool),
          ∀e∈parityOriginalHistoricalCauchyActiveESupport434
            (sourceOriginalLiteralDepth 20 L) L E band slot delta,0<e) →
        (∀m∈K,(m:ℝ)≤2*U) →
        (∀n∈J,(n:ℝ)≤3*V) →
        (∀m∈K,‖alpha m‖≤1) →
        (∀n∈J,‖beta n‖≤1) →
      let d := sourceOriginalLiteralDepth 20 L
      let R := L^C0/(2*Real.pi)
      let M_H := ∫s : ℝ, ‖s‖^H *
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
      ‖∫s in {s : ℝ | R≤‖s‖},
        parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
        (∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 L,
            parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed)‖ ≤
        (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
  obtain ⟨H,hSource⟩ :=
    parity_eventually_original_true_Ybox_signed_tau_Schwartz_moment_paid_noUVlower434
      Cbox goal C0 hCbox hC0 Psi hSmooth hSupport
  refine ⟨H,?_⟩
  filter_upwards [hSource] with L hSourceL
  refine ⟨hSourceL.1,?_⟩
  intro U V hU hV hUVhi E signed band slot K J alpha beta
    hSelected hK hJ hAlpha hBeta
  let d := sourceOriginalLiteralDepth 20 L
  let Ybox := Nat.ceil (6*U*V)
  let R := L^C0/(2*Real.pi)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
  let SlotMass : ℝ := ∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
    ∫xi in parityOriginalActualFullQFrequencyCube434 L,
      ∑u∈Finset.Ioc 0 Ybox,
        ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
          d L E u signed band slot delta xi‖ *
        ((u+2).divisors.card:ℝ)
  let AllMass : ℝ := ∑slot0 : Fin 20,
    ∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot0).length → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 L,
        ∑u∈Finset.Ioc 0 Ybox,
          ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
            d L E u signed band slot0 delta xi‖ *
          ((u+2).divisors.card:ℝ)
  have hLp : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hSourceL.1
  have hR : 0<R := by
    dsimp [R]
    exact div_pos (Real.rpow_pos_of_pos hLp _) (by positivity)
  have hM : 0≤M_H := by
    dsimp [M_H]
    apply integral_nonneg
    intro s
    positivity
  have hCoefficient : 0≤(R^H)⁻¹*M_H := by positivity
  have hSingle := parity_original_true_Ybox_single_slot_tau_le_allslots434
    d L E U V signed band slot L
  have hMassLe : SlotMass≤AllMass := by
    simpa only [SlotMass,AllMass,d,Ybox] using hSingle
  have hBudget := hSourceL.2 U V hU hV hUVhi E signed band
  have hHistory := parity_original_historical_single_slot_high_Psi_Mellin_Q_tau_bound434
    d L E hLp rfl band slot K J alpha beta signed Ybox 1 1
    (by norm_num) (by norm_num) hAlpha hBeta Psi hSmooth hSupport
    R hR H L
  have hEq := parity_original_true_Ybox_single_slot_high_hist_eq_capfree434
    d L E U V hLp hU.le hV.le band slot hSelected K J hK hJ
    alpha beta signed Psi hSmooth hSupport R L
  rw [hEq] at hHistory
  dsimp only at hHistory ⊢
  calc
    _ ≤ ((1:ℝ)*1*SlotMass)*((R^H)⁻¹*M_H) := by
      simpa only [SlotMass,R,M_H,d,Ybox,mul_assoc] using hHistory
    _ = ((R^H)⁻¹*M_H)*SlotMass := by ring
    _ ≤ ((R^H)⁻¹*M_H)*AllMass :=
      mul_le_mul_of_nonneg_left hMassLe hCoefficient
    _ ≤ (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
      simpa only [AllMass,R,M_H,d,Ybox] using hBudget
end Green64Analytic.Parity

end

end

/-! ## QuarterB629SingleSlotFullPsiMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4200000

/-- Source-true ORIGINAL real full Psi Mellin and full Q-frequency cube
for one b629 prime/rough fine alpha under exp L≤4UV. Low-s follows
actual pre-Cauchy Gram, high-s from full positive original Ybox
shifted-tau. All source selected-e phases are counted once. -/
theorem parity_eventually_original_actual_quarter_b629_single_slot_full_Psi_Mellin_Q_anylog434
    (jQ : ℕ) (goal target C0 beta gamma K0 Cbox A R : ℝ)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ∃ H : ℕ, ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
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
    parity_eventually_original_actual_quarter_b629_single_slot_restricted_Psi_Mellin_Q_anylog434
      jQ goal target C0 beta gamma K0 Cbox A R
      hTarget hK0Target hPrecision hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube Psi hPsiSmooth hPsiSupport
  have hSpos : 0<S := by
    have hh : (0:ℝ)≤(B:ℝ) := Nat.cast_nonneg _
    linarith [hBS]
  refine ⟨H,J,B,S,hBS,?_⟩
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
end Green64Analytic.Parity

end

end

/-! ## QuarterSignedB629FineSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4900000

/-- Original literal signed r20, h=-2 source bilinear real-Psi sum
with one actual prime/rough fine b629 cofactor interval has O_A
saving on every true quarter-UV dyad, after all Q Fourier/
Boolean allocations and real Mellin. Reserved Q band once,
source original E≤exp((1-betaP)L), e-first comparison, Ybox/Y0
boundary n≤2V and all original high-s τ errors paid. -/
theorem parity_eventually_original_signed_quarter_b629_fine_one_slot_Psi_Mellin_source_anylog434
    (jQ : ℕ) (goal target C0 beta betaP gamma K0 Cbox A R : ℝ)
    (hbetaP : 0<betaP)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
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
    parity_eventually_original_actual_quarter_b629_single_slot_full_Psi_Mellin_Q_anylog434
      jQ goal target C0 beta gamma K0 Cbox A R
      hC0 hTarget hK0Target hPrecision hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube Psi hPsiSmooth hPsiSupport
  have hSpos : 0<S := by
    have hh : (0:ℝ)≤(B:ℝ) := Nat.cast_nonneg _
    linarith [hBS]
  refine ⟨H,J,B,S,hBS,?_⟩
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

/-! ## TrueYboxNoUVLowerFinalAudit -/

section



end

