module

public import Green64.Library.Sieve.Foundations.Part043
public import Green64.Library.Sieve.Foundations.Part039
public import Green64.Library.Sieve.Foundations.Part018
public import Green64.Library.Sieve.Foundations.Part042
public import Green64.Library.Sieve.Foundations.Part036
public import Green64.Library.Sieve.Foundations.Part016
public import Green64.Library.Sieve.Foundations.Part038
public import Green64.Library.Sieve.Foundations.Part021
public import Green64.Library.Sieve.Foundations.Part022
public import Green64.Library.Sieve.Foundations.Part031
public import Green64.Library.Sieve.Foundations.Part032

@[expose] public section

/-!
# Sieve / Foundations / Part044

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## FullDyadProxySingleSlotRestrictedPsiMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1550000

/-- The exact ORIGINAL full-interval [a,b] b629 prime/rough
full-cell proxy source, for ONE chosen reserved Q slot, with
complete original Boolean allocations and N-dimensional Q Fourier
cube, has arbitrary O_A(exp(L)L^-A) saving after integration over
|s|<=L^C0/(2π). The underlying Parity(4.17) per-slot Cauchy bound
is original; no 20-slot complex cancellation, no per-cell L^S,
selected Q factor counted once. This is the matching low-s source
result for the literal per-slot preCauchy comparison. -/
theorem parity_eventually_original_actual_full_dyad_proxy_single_slot_restricted_Psi_Mellin_Q_anylog434
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
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 32≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
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
          (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
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
    parity_eventually_original_actual_fine_Bprime_fullQ_positive_anylog434
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
    (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
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
    have hAlpha :
        parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b =
          b629ActualFineAlpha434 prime L S gamma a b := by
      funext n
      exact parity_original_actual_full_dyad_proxy_eq_b629434 prime L S gamma a b n
    rw [←hAlpha] at h
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

/-! ## FullDyadProxySingleSlotCompleteMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2300000

/-- TRUE original Parity(4.7)/(7.3) FULL-INTERVAL prime/rough
full-cell proxy discrepancy after the COMPLETE real Ψ-Mellin line
and all 20 reserved original Q slots, Boolean allocations and
native N-dimensional Q Fourier cubes. Its cap-free physical Bprime
has O_A(exp(L)L^-A) saving for ONE fixed original reserved band,
with exact 2πs and BOTH low/high source Fourier tails accounted for.
The original b629 alpha is on the WHOLE [a,b] K, and its norm<=1
and rough support are native SOURCE results. The low-|s| original
Parity(4.17) + paid Cauchy saving chooses J,B,S; the genuine high-s
Schwartz moment order H is fixed BEFORE L and also before J/B/S.
A single original selected-Q phase appears inside native a_e(e).
This result does not claim full Parity TypeII(4.2) for arbitrary alpha,
remaining reserved bands/remaining dyadic external families,
Parity §§5–9 or Green64.green_64. -/
theorem parity_eventually_original_actual_full_dyad_proxy_single_slot_full_Psi_Mellin_Q_anylog434
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
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 32≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
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
          (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
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
    parity_eventually_original_true_Ybox_capfree_single_slot_high_anylog434
      Cbox goal C0 hCbox hC0 Psi hPsiSmooth hPsiSupport
  obtain ⟨J,B,S,hBS,hLow⟩ :=
    parity_eventually_original_actual_full_dyad_proxy_single_slot_restricted_Psi_Mellin_Q_anylog434
      jQ goal target C0 beta gamma K0 Cbox A R
      hTarget hK0Target hPrecision hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube Psi hPsiSmooth hPsiSupport
  have hSpos : 0<S := by
    have hh : (0:ℝ)≤(B:ℝ) := Nat.cast_nonneg _
    linarith [hBS]
  refine ⟨H,J,B,S,hBS,?_⟩
  filter_upwards [hLow,hHigh,
      parity_eventually_original_full_dyad_proxy_norm_rough434
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
    (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
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
    have hPoint := (hAlphaL prime a b hFineLow m).1
    simpa only [alpha,restrictSequence,if_pos hm] using hPoint
  have hLowBound := hLowRest hL hFamily0 U V E hU hV hUV hUVhi
    hEscale hEone hVone band hBand slot a b Jbeta prime betaCoeff signed
    hFineLow hTwo hUpper hExp hDyad hJ hBeta
  have hHighBound := hHighRest U V hU hV hUV hUVhi E signed band slot
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

/-! ## OriginalSignedProxySingleSlotSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- ORIGINAL signed h=-2 r0=20 SOURCE pre-Cauchy `u=m*n-2`
with REAL source Ψ(u/exp L), actual moving P/Q groups, labelled
20! factorial, epsilon branches and true whole-interval b629
prime/rough full-cell proxy α_K has arbitrary O_A(exp L L^-A)
for one fixed original reserved Q band jQ and one actual slot.

Proof: native original pre-Cauchy source-to-single-slot Bprime
comparison (not a complex sum over 20 slots), actual one-slot
Parity(4.17) Cauchy low Q Fourier/Mellin estimate, true Ybox high
|s| Schwarz×shifted-τ saving, exact FULL unbounded original
Q-OUTER ↔ Mellin-OUTER Fubini and literal source alpha normalization.

The original E<=exp((1-betaP)L) and reserved Q band inequality are
EXPLICIT input hypotheses, as is the original dyadic geometry and
E=U L^-K0. They must be satisfied for a later global TypeII use.
Still only one b629 prime/rough proxy special α, one jQ/one dyadic
external family and smooth Ψ, NOT general Parity TypeII(4.2) or final
Green64.green_64. -/
theorem parity_eventually_original_signed_full_dyad_proxy_one_slot_Psi_Mellin_source_anylog434
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
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 32≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
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
          (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
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
    parity_eventually_original_actual_full_dyad_proxy_single_slot_full_Psi_Mellin_Q_anylog434
      jQ goal target C0 beta gamma K0 Cbox A R
      hC0 hTarget hK0Target hPrecision hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube Psi hPsiSmooth hPsiSupport
  have hSpos : 0<S := by
    have hh : (0:ℝ)≤(B:ℝ) := Nat.cast_nonneg _
    linarith [hBS]
  refine ⟨H,J,B,S,hBS,?_⟩
  filter_upwards [hFull,
      parity_eventually_original_signed_source_to_actual_capfree_Psi_Mellin_Bprime_all_log434
        betaP goal hbetaP jQ hBand,
      parity_eventually_original_full_dyad_proxy_norm_rough434
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
    (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
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
    have hPoint := (hAlphaL prime a b hFineLow m).1
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
    hU.le hV.le hUV Psi hPsiSet hPsiSmooth hPsiPos hPsiLe
    slot K Jbeta alpha betaCoeff 1 1
    (by norm_num) (by norm_num) hAlpha hBeta hK hN signed
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

/-! ## OriginalTypeIIEUpperGeometry -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1150000

/-- The ORIGINAL Parity TypeII V≥x^b_* lower bound pays the genuine
reserved-prime pre-Cauchy source requirement E≤x^(1−βP), for every
actual E=U L^(-K0) with K0≥0, UV≤Cbox exp L and b_*≥2βP.
The constant dyadic Cbox≥1 is absorbed before L by choosing L≥
log(Cbox)/βP. No posthoc choice of precision or unproved source
E-window assumption is inserted. -/
theorem parity_original_actual_TypeII_E_upper_geometry434
    (Cbox betaP bstar K0 L U V E : ℝ)
    (hCbox : 1≤Cbox) (hbetaP : 0<betaP)
    (hbstar : 2*betaP≤bstar) (hK0 : 0≤K0)
    (hL : 1≤L) (hLog : Real.log Cbox≤betaP*L)
    (hU : 0<U) (hV : 0<V)
    (hUVhi : U*V≤Cbox*Real.exp L)
    (hVlower : Real.exp (bstar*L)≤V)
    (hE : E=U*L^(-K0)) :
    E≤Real.exp ((1-betaP)*L) := by
  have hLpos : 0<L := by linarith
  have hCLpos : 0<Cbox := by linarith
  have hCexp : Cbox≤Real.exp (betaP*L) := by
    calc
      Cbox = Real.exp (Real.log Cbox) := (Real.exp_log hCLpos).symm
      _ ≤ Real.exp (betaP*L) := Real.exp_le_exp.mpr hLog
  have hKpower : L^(-K0)≤1 := by
    calc
      _ ≤ L^(0:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL (by linarith)
      _ = 1 := by simp
  have hE_U : E≤U := by
    rw [hE]
    nlinarith [hKpower,hU]
  have hLnonneg : 0≤L := by linarith
  have hExpV : Real.exp (2*betaP*L)≤V := by
    calc
      _ ≤ Real.exp (bstar*L) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hbstar,hLnonneg]
      _ ≤ V := hVlower
  let X : ℝ := Real.exp ((1-betaP)*L)
  have hXpos : 0≤X := (Real.exp_pos _).le
  have hProduct : X*V ≥ Cbox*Real.exp L := by
    calc
      Cbox*Real.exp L ≤ Real.exp (betaP*L)*Real.exp L :=
        mul_le_mul_of_nonneg_right hCexp (Real.exp_pos _).le
      _ = X*Real.exp (2*betaP*L) := by
        dsimp [X]
        rw [←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      _ ≤ X*V := mul_le_mul_of_nonneg_left hExpV hXpos
  have hU_X : U≤X := by
    by_contra hh
    have hx : X<U := lt_of_not_ge hh
    have hp : 0 < (U-X)*V := mul_pos (sub_pos.mpr hx) hV
    nlinarith [hUVhi,hProduct]
  exact hE_U.trans hU_X

/-- Eventual form with all original bstar, Cbox, βP, K0 fixed
before the true large parameter L. This is the exact missing
SOURCE pre-Cauchy E-upper link for the original TypeII slab. -/
theorem parity_eventually_original_actual_TypeII_E_upper_geometry434
    (Cbox betaP bstar K0 : ℝ)
    (hCbox : 1≤Cbox) (hbetaP : 0<betaP)
    (hbstar : 2*betaP≤bstar) (hK0 : 0≤K0) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V E : ℝ), 0<U → 0<V →
        U*V≤Cbox*Real.exp L → Real.exp (bstar*L)≤V →
        E=U*L^(-K0) → E≤Real.exp ((1-betaP)*L) := by
  filter_upwards [eventually_ge_atTop (max 1 (Real.log Cbox/betaP))]
    with L hL
  have hLone : 1≤L := (le_max_left _ _).trans hL
  have hLog : Real.log Cbox≤betaP*L := by
    have hh := (le_max_right (1:ℝ) (Real.log Cbox/betaP)).trans hL
    simpa only [mul_comm] using (div_le_iff₀ hbetaP).mp hh
  refine ⟨hLone,?_⟩
  intro U V E hU hV hUVhi hVlower hE
  exact parity_original_actual_TypeII_E_upper_geometry434
    Cbox betaP bstar K0 L U V E
    hCbox hbetaP hbstar hK0 hLone hLog hU hV hUVhi hVlower hE
end Green64Analytic.Parity

end

end

/-! ## SourceFixedReservedQBand -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 600000

/-- For EVERY fixed positive source slack betaP, the genuine
  Parity r0=20 Q-band exponent q0/2^j has a FINITE reserved band
  jQ satisfying the (6/5)-enlarged band support pre-Cauchy gate.
  The band is chosen before L, not by selecting jQ(L) afterwards. -/
theorem parity_original_exists_fixed_reserved_Q_band434
    (betaP : ℝ) (hbetaP : 0 < betaP) :
    ∃ jQ : ℕ,
      (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4 := by
  let q0 : ℝ := sourceOriginalQ0Scale 20
  have hPow : Tendsto (fun j : ℕ => (2:ℝ)^j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hLarge : ∀ᶠ j : ℕ in atTop,
      ((24/5:ℝ)*|q0|)/betaP ≤ (2:ℝ)^j :=
    hPow.eventually (eventually_ge_atTop _)
  obtain ⟨jQ,hBound⟩ := hLarge.exists
  refine ⟨jQ,?_⟩
  have hPowPos : 0 < (2:ℝ)^jQ := pow_pos (by norm_num) _
  have hAbs : q0 ≤ |q0| := le_abs_self _
  have hMon : (6/5:ℝ)*q0 ≤ (6/5:ℝ)*|q0| :=
    mul_le_mul_of_nonneg_left hAbs (by norm_num)
  have hGain : (24/5:ℝ)*|q0| ≤ (2:ℝ)^jQ*betaP :=
    (div_le_iff₀ hbetaP).mp hBound
  change (6/5:ℝ)*(q0/(2:ℝ)^jQ) ≤ betaP/4
  have hAssoc : (6/5:ℝ)*(q0/(2:ℝ)^jQ) =
      ((6/5:ℝ)*q0)/(2:ℝ)^jQ := by ring
  rw [hAssoc]
  apply (div_le_iff₀ hPowPos).2
  nlinarith [hGain,hMon]
end Green64Analytic.Parity

end

end

/-! ## ActualFullCellNestedDyadicRestriction -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false

/-- A nested interval cut does NOT recompute the normalized B_I
full-cell proxy: the actual b629 prime/rough test-minus-proxy is
pointwise the same whole-cell expression, merely zeroed outside
its new interval. The restriction is valid for both test kinds. -/
theorem parity_original_actual_fullcell_proxy_nested_interval_eq434
    (prime : Bool) (L S gamma : ℝ)
    (a b a' b' n : ℕ)
    (ha : a≤a') (hb : b'≤b) :
    parityOriginalActualFullDyadProxyDifference434 prime L S gamma a' b' n =
    restrictSequence (Finset.Icc a' b')
      (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b) n := by
  classical
  by_cases hn : n∈Finset.Icc a' b'
  · have hnBig : n∈Finset.Icc a b := by
      have h := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨ha.trans h.1,h.2.trans hb⟩
    cases prime <;>
      simp [parityOriginalActualFullDyadProxyDifference434,
        restrictSequence,hn,hnBig]
  · cases prime <;>
      simp [parityOriginalActualFullDyadProxyDifference434,
        restrictSequence,hn]
end Green64Analytic.Parity

end

end

/-! ## ActualTypeIIDyadicPairCard -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false

/-- Actual binary dyadic pair scales generated by a physical original
TypeII finite (m,n) support. Each scale is exactly the inherited
historical 2^(Nat.log 2 m), not a hypothetical dyadic label. -/
def parityOriginalActualTypeIIDyadicPairScales434 (S : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  S.image (fun z =>
    (parityOriginalHistoricalActualZDyadicScale434 z.1,
     parityOriginalHistoricalActualZDyadicScale434 z.2))

/-- Genuine logarithmic-square bound for the DISTINCT actual TypeII
binary dyadic pair scales. Neither the count of original physical pairs
nor the count of arbitrary labelled e/beta/Q allocations is used.
This is deliberately weaker than the Parity §7.3 O(L) correlated-pair
count; it is however sufficient for a polynomial-loss aggregation. -/
theorem parity_original_actual_TypeII_dyadic_pair_image_card_le_log_sq434
    (S : Finset (ℕ × ℕ)) (Y : ℕ)
    (hY : ∀ z∈S, z.1≤Y ∧ z.2≤Y) :
    (parityOriginalActualTypeIIDyadicPairScales434 S).card ≤
      (Nat.log 2 Y + 1) * (Nat.log 2 Y + 1) := by
  classical
  let T : Finset (ℕ × ℕ) :=
    (Finset.range (Nat.log 2 Y+1)).product
      (Finset.range (Nat.log 2 Y+1))
  let f : (ℕ × ℕ) → (ℕ × ℕ) := fun z => (2^z.1,2^z.2)
  have hsub : parityOriginalActualTypeIIDyadicPairScales434 S ⊆ T.image f := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    have hm : Nat.log 2 z.1 ≤ Nat.log 2 Y := Nat.log_mono_right (hY z hz).1
    have hn : Nat.log 2 z.2 ≤ Nat.log 2 Y := Nat.log_mono_right (hY z hz).2
    apply Finset.mem_image.mpr
    refine ⟨(Nat.log 2 z.1,Nat.log 2 z.2), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hm),
         Finset.mem_range.mpr (Nat.lt_succ_of_le hn)⟩
    · rfl
  calc
    _ ≤ (T.image f).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le
    _ = (Nat.log 2 Y+1)*(Nat.log 2 Y+1) := by
      simp [T, Finset.card_product]
end Green64Analytic.Parity

end

end

/-! ## BothParityOriginalSource -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- Parity (1.2), defined from the original A0, not from the analytic
signed decomposition. The P exponent counts prime multiplicities. -/
def parityWeight
    (d : ℕ) (L rho : ℝ) (u : ℕ) : ℝ :=
  sourceOriginalA0 20 (sourceOriginalQActualBands 20 d L)
    (sourceOriginalPAllActualBands 20 L) u *
    ((1+rho*(-1:ℝ)^sourceOriginalPParityExponent
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)/2)

/-- The full labelled signed source is exactly A0 times its true P
epsilon. This uses the genuine original Q coefficient, all its labels
and the actual factorial, including repeated primes. -/
theorem parity_original_signed_source_eq_A0_epsilon434
    (d : ℕ) (L : ℝ) (hL : 0<L) (signed : Bool) (u : ℕ) :
    parityOriginalSignedSourceA434 d L signed u =
    sourceOriginalA0 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u *
      parityOriginalPSignedEpsilon434
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) signed u := by
  classical
  have hSigned : parityOriginalSignedSourceA434 d L signed u =
      parityOriginalSignedSourceA434 d L false u *
      parityOriginalPSignedEpsilon434
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) signed u := by
    unfold parityOriginalSignedSourceA434
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro f hf
    exact parity_original_signed_full_tuple_weight_eq_false_mul_sign434 d L u signed f
  rw [hSigned, parity_original_signed_false_source_eq_A0434 d L hL u]

theorem parity_original_parity_A_eq_full_signed_projection434
    (d : ℕ) (L rho : ℝ) (hL : 0<L) (u : ℕ) :
    parityWeight d L rho u =
      (parityOriginalSignedSourceA434 d L false u +
        rho*parityOriginalSignedSourceA434 d L true u)/2 := by
  rw [parity_original_signed_source_eq_A0_epsilon434 d L hL false u,
    parity_original_signed_source_eq_A0_epsilon434 d L hL true u]
  simp only [parityWeight, parityOriginalPSignedEpsilon434,
    Bool.false_eq_true, ite_false, ite_true]
  ring

/-- The rho=-1 definition agrees with the existing original odd
source, without a new weight normalization. -/
theorem parity_original_minus_parity_A_eq_original_A434
    (d : ℕ) (L : ℝ) (u : ℕ) :
    parityWeight d L (-1) u =
    sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u := by
  unfold parityWeight sourceOriginalA
  ring

/-- The actual u-first factor sum for Parity's independently defined
parity projection. Both factor coefficients and the true shifted
equation mn=u+2 are unchanged. -/
def parityOriginalParityBilinearSource434
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    (((parityWeight d L rho u *
      Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)) *
    (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
      alpha z.1*beta z.2)

/-- Exact source identity, before any norm or squaring: the two
signed sources reconstruct every real parity projection. Neither
reserved band nor reserved slot is an extra source sum. -/
theorem parity_original_parity_bilinear_eq_signed_mellin_projection434
    (d : ℕ) (L rho : ℝ) (hL : 0<L) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalParityBilinearSource434 d L rho Psi K J alpha beta Y =
    (parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J alpha beta false 0 Y +
     (rho:ℂ)*parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J alpha beta true 0 Y)/2 := by
  unfold parityOriginalParityBilinearSource434
    parityOriginalShiftTwoSignedBilinearMellinSource434
  rw [Finset.mul_sum, ←Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_original_parity_A_eq_full_signed_projection434 d L rho hL u]
  simp [sourceOriginalPureMellinPhase434]
  push_cast
  ring

theorem parity_original_minus_parity_bilinear_eq_original434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalParityBilinearSource434 d L (-1) Psi K J alpha beta Y =
    parityOriginalShiftTwoBilinearSource434 d L Psi K J alpha beta Y := by
  unfold parityOriginalParityBilinearSource434 parityOriginalShiftTwoBilinearSource434
  simp only [parity_original_minus_parity_A_eq_original_A434]

/-- The odd projection is also exactly the already defined original
m,n,u triple with compact Psi. This links the analytic source to the
existing physical carrier, rather than naming two distinct sums alike. -/
theorem parity_original_minus_parity_bilinear_eq_original_triple434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalParityBilinearSource434 d L (-1) Psi K J alpha beta Y =
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta Y := by
  rw [parity_original_minus_parity_bilinear_eq_original434]
  exact parity_original_shift_two_actual_source_eq_TypeII_triple434
    d L Psi hPsi K J alpha beta Y

/-- Two simultaneous signed replacement bounds imply the actual
projection bound with NO factor two loss, for |rho|<=1. In particular
both Parity parity signs are covered with the same analytic parameters. -/
theorem parity_original_parity_replacement_norm_le434
    (d : ℕ) (L rho : ℝ) (hL : 0<L) (hRho : |rho|≤1)
    (Psi : ℝ → ℝ) (K J : Finset ℕ)
    (alpha beta alpha' beta' : ℕ → ℂ) (Y : ℕ) (M : ℝ)
    (hFalse : ‖parityOriginalShiftTwoSignedBilinearMellinSource434
        d L Psi K J alpha beta false 0 Y -
      parityOriginalShiftTwoSignedBilinearMellinSource434
        d L Psi K J alpha' beta' false 0 Y‖≤M)
    (hTrue : ‖parityOriginalShiftTwoSignedBilinearMellinSource434
        d L Psi K J alpha beta true 0 Y -
      parityOriginalShiftTwoSignedBilinearMellinSource434
        d L Psi K J alpha' beta' true 0 Y‖≤M) :
    ‖parityOriginalParityBilinearSource434 d L rho Psi K J alpha beta Y -
      parityOriginalParityBilinearSource434 d L rho Psi K J alpha' beta' Y‖≤M := by
  rw [parity_original_parity_bilinear_eq_signed_mellin_projection434 d L rho hL,
    parity_original_parity_bilinear_eq_signed_mellin_projection434 d L rho hL]
  let f := parityOriginalShiftTwoSignedBilinearMellinSource434
    d L Psi K J alpha beta false 0 Y
  let f' := parityOriginalShiftTwoSignedBilinearMellinSource434
    d L Psi K J alpha' beta' false 0 Y
  let t := parityOriginalShiftTwoSignedBilinearMellinSource434
    d L Psi K J alpha beta true 0 Y
  let t' := parityOriginalShiftTwoSignedBilinearMellinSource434
    d L Psi K J alpha' beta' true 0 Y
  change ‖(f+(rho:ℂ)*t)/2-(f'+(rho:ℂ)*t')/2‖≤M
  have hId : (f+(rho:ℂ)*t)/2-(f'+(rho:ℂ)*t')/2 =
      ((f-f')+(rho:ℂ)*(t-t'))/2 := by ring
  rw [hId,norm_div]
  rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num [Complex.norm_def]]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  calc
    ‖(f-f')+(rho:ℂ)*(t-t')‖ ≤ ‖f-f'‖+‖(rho:ℂ)*(t-t')‖ :=
      norm_add_le _ _
    _ = ‖f-f'‖+|rho| * ‖t-t'‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ M+M := add_le_add hFalse
      ((mul_le_of_le_one_left (norm_nonneg _) hRho).trans hTrue)
    _ = M*2 := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalTypeIIPhysicalDyadicSupport -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- Literal true positive shifted m*n=u+2 support for the exact
original Parity Type II triple source, no alpha/beta or artificial
factor bound. -/
def parityOriginalTypeIIPhysicalPairs434 (K J : Finset ℕ) (Y : ℕ) :
    Finset (ℕ × ℕ) :=
  (K.product J).filter (fun z =>
    ∃ u ∈ Finset.Ioc 0 Y,
      0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2)

/-- Every factor in a genuinely supported original shifted Type II
pair is at most Y+2, by the exact m*n=u+2 arithmetic. -/
theorem parity_original_TypeII_physical_pair_factor_bounds434
    (K J : Finset ℕ) (Y : ℕ) :
    ∀ z ∈ parityOriginalTypeIIPhysicalPairs434 K J Y,
      z.1≤Y+2 ∧ z.2≤Y+2 := by
  intro z hz
  simp only [parityOriginalTypeIIPhysicalPairs434, Finset.mem_filter] at hz
  obtain ⟨u,hu,hmp,hn,hprod⟩ := hz.2
  have huY : u≤Y := (Finset.mem_Ioc.mp hu).2
  have hm1 : 1≤z.1 := hmp
  have hn1 : 1≤z.2 := hn
  have hmprod : z.1≤z.1*z.2 := by
    nlinarith [Nat.mul_le_mul_left z.1 hn1]
  have hnprod : z.2≤z.1*z.2 := by
    nlinarith [Nat.mul_le_mul_right z.2 hm1]
  omega

/-- The exact shifted physical support has only logarithmically
many different dyadic PAIRS (quadratic log upper bound), regardless
of its number of physical m,n,u triples. -/
theorem parity_original_TypeII_physical_pair_dyadic_card_le_log_sq434
    (K J : Finset ℕ) (Y : ℕ) :
    (parityOriginalActualTypeIIDyadicPairScales434
      (parityOriginalTypeIIPhysicalPairs434 K J Y)).card ≤
      (Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1) := by
  exact parity_original_actual_TypeII_dyadic_pair_image_card_le_log_sq434
    _ (Y+2) (parity_original_TypeII_physical_pair_factor_bounds434 K J Y)

/-- In the original physical Type II triple, restricting K×J to
true shifted-positive physical pairs is an EXACT equality. It
removes no nonzero terms and imposes no multiplicativity or
smoothing on beta. -/
theorem parity_original_TypeII_triple_eq_physical_pair_restriction434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta Y =
    ∑ z ∈ parityOriginalTypeIIPhysicalPairs434 K J Y,
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
          (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
            (sourceOriginalPAllActualBands 20 L) u *
            Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
            (alpha z.1*beta z.2))
        else 0 := by
  classical
  unfold parityOriginalShiftTwoOriginalTypeIITripleSource434
    parityOriginalTypeIIPhysicalPairs434
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : ∃ u ∈ Finset.Ioc 0 Y,
      0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2
  · rw [if_pos h]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro u hu
    have hh : ¬(0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2) := by
      intro hs
      exact h ⟨u,hu,hs⟩
    simp [hh]

/-- Exact SOURCE-preserving finite regrouping of the original shifted
Type II triple into the *distinct physically attained* binary dyadic
(m,n) fibres. This does not change the full-cell proxy coefficients or
replace a physical fibre by an independently re-normalized interval. -/
theorem parity_original_TypeII_triple_eq_physical_dyadic_fibres434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta Y =
    ∑ scale ∈ parityOriginalActualTypeIIDyadicPairScales434
        (parityOriginalTypeIIPhysicalPairs434 K J Y),
      ∑ z ∈ (parityOriginalTypeIIPhysicalPairs434 K J Y).filter
        (fun z => (parityOriginalHistoricalActualZDyadicScale434 z.1,
          parityOriginalHistoricalActualZDyadicScale434 z.2) = scale),
        ∑ u ∈ Finset.Ioc 0 Y,
          if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
            (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
              (sourceOriginalPAllActualBands 20 L) u *
              Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
              (alpha z.1*beta z.2))
          else 0 := by
  classical
  rw [parity_original_TypeII_triple_eq_physical_pair_restriction434]
  let S := parityOriginalTypeIIPhysicalPairs434 K J Y
  let f : (ℕ×ℕ) → (ℕ×ℕ) := fun z =>
    (parityOriginalHistoricalActualZDyadicScale434 z.1,
     parityOriginalHistoricalActualZDyadicScale434 z.2)
  have hMaps : ∀ z ∈ S, f z ∈ S.image f :=
    fun z hz => Finset.mem_image_of_mem f hz
  exact (Finset.sum_fiberwise_of_maps_to hMaps
    (fun z => ∑ u ∈ Finset.Ioc 0 Y,
      if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
        (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
          (sourceOriginalPAllActualBands 20 L) u *
          Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
          (alpha z.1*beta z.2))
      else 0)).symm

/-- Explicit source-derived quadratic-log cardinality loss when
summing bounds for the actual dyadic physical fibres. The per-fibre
bound is an EXPLICIT premise, not a statement that local full-cell
TypeII automatically applies to a cut dyadic fibre. -/
theorem parity_original_TypeII_triple_physical_dyadic_loss_ledger434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ)
    (M : ℝ) (hM : 0≤M)
    (hEach : ∀ scale ∈ parityOriginalActualTypeIIDyadicPairScales434
          (parityOriginalTypeIIPhysicalPairs434 K J Y),
       ‖∑ z ∈ (parityOriginalTypeIIPhysicalPairs434 K J Y).filter
          (fun z => (parityOriginalHistoricalActualZDyadicScale434 z.1,
            parityOriginalHistoricalActualZDyadicScale434 z.2) = scale),
          ∑ u ∈ Finset.Ioc 0 Y,
            if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
              (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
                (sourceOriginalPAllActualBands 20 L) u *
                Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
                (alpha z.1*beta z.2))
            else 0‖≤M) :
    ‖parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta Y‖ ≤
      (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ)*M := by
  classical
  rw [parity_original_TypeII_triple_eq_physical_dyadic_fibres434]
  let S := parityOriginalActualTypeIIDyadicPairScales434
    (parityOriginalTypeIIPhysicalPairs434 K J Y)
  let F : (ℕ×ℕ) → ℂ := fun scale =>
    ∑ z ∈ (parityOriginalTypeIIPhysicalPairs434 K J Y).filter
      (fun z => (parityOriginalHistoricalActualZDyadicScale434 z.1,
        parityOriginalHistoricalActualZDyadicScale434 z.2) = scale),
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
          (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
            (sourceOriginalPAllActualBands 20 L) u *
            Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
            (alpha z.1*beta z.2))
        else 0
  have hCard := parity_original_TypeII_physical_pair_dyadic_card_le_log_sq434 K J Y
  change ‖∑ scale ∈ S, F scale‖ ≤ _
  calc
    _ ≤ ∑ scale ∈ S, ‖F scale‖ := norm_sum_le _ _
    _ ≤ ∑ scale ∈ S, M := Finset.sum_le_sum (by
      intro scale hs
      exact hEach scale hs)
    _ = (S.card:ℝ)*M := by simp
    _ ≤ (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ)*M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact_mod_cast hCard
end Green64Analytic.Parity

end

end

/-! ## ActualBinaryDyadicInterval -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The historical 2^(floor log2 m) dyadic scale is EXACTLY the
interval [2 ^ k,2^(k+1)) for every positive m. -/
theorem parity_original_actual_binary_dyadic_scale_iff434
    (m k : ℕ) (hm : 0 < m) :
    parityOriginalHistoricalActualZDyadicScale434 m = 2 ^ k ↔
      2 ^ k ≤ m ∧ m < 2 ^ (k+1) := by
  constructor
  · intro h
    have hh := parity_original_historical_actual_z_in_own_dyad434 m hm
    rw [h] at hh
    constructor
    · exact hh.2.1
    · simpa only [pow_succ, mul_comm] using hh.2.2
  · rintro ⟨hlo,hhi⟩
    unfold parityOriginalHistoricalActualZDyadicScale434
    rw [Nat.log_eq_of_pow_le_of_lt_pow hlo hhi]

/-- The TRUE source binary dyadic cut at one log-scale is an
intersection of an original finite support K and a literal interval;
this statement does not change proxy values. -/
def parityOriginalTypeIIBinaryDyadCut434 (K : Finset ℕ) (k : ℕ) : Finset ℕ :=
  K.filter (fun m => 2 ^ k ≤ m ∧ m < 2 ^ (k+1))

theorem parity_original_positive_scale_fibre_eq_binary_cut434
    (K : Finset ℕ) (k : ℕ) (hK : ∀m∈K,0 < m) :
    K.filter (fun m => parityOriginalHistoricalActualZDyadicScale434 m = 2 ^ k) =
      parityOriginalTypeIIBinaryDyadCut434 K k := by
  classical
  ext m
  simp only [parityOriginalTypeIIBinaryDyadCut434,Finset.mem_filter]
  constructor
  · rintro ⟨hm,hs⟩
    exact ⟨hm,(parity_original_actual_binary_dyadic_scale_iff434 m k (hK m hm)).mp hs⟩
  · rintro ⟨hm,hs⟩
    exact ⟨hm,(parity_original_actual_binary_dyadic_scale_iff434 m k (hK m hm)).mpr hs⟩

/-- For any positive original K,J support, physical pairs whose
historical dyadic scales are (2 ^ km,2 ^ kn) equal the EXACT
intersection of the original Cartesian K×J with the two numerical
binary dyads, followed by the original shifted positive fibre gate. -/
theorem parity_original_TypeII_physical_pair_dyadic_fibre_eq_cuts434
    (K J : Finset ℕ) (Y km kn : ℕ) :
    (parityOriginalTypeIIPhysicalPairs434 K J Y).filter
      (fun z =>
        (parityOriginalHistoricalActualZDyadicScale434 z.1,
          parityOriginalHistoricalActualZDyadicScale434 z.2) =
          (2 ^ km,2 ^ kn)) =
    ((parityOriginalTypeIIBinaryDyadCut434 K km).product
      (parityOriginalTypeIIBinaryDyadCut434 J kn)).filter
        (fun z => ∃ u∈Finset.Ioc 0 Y,
          0 < z.1 ∧ 0 < z.2 ∧ z.1 * z.2 = u+2) := by
  classical
  ext z
  constructor
  · intro hz
    have hOuter := Finset.mem_filter.mp hz
    have hPhys : z ∈ K.product J ∧
        (∃ u ∈ Finset.Ioc 0 Y,
          0 < z.1 ∧ 0 < z.2 ∧ z.1 * z.2 = u+2) := by
      have hh := hOuter.1
      simp only [parityOriginalTypeIIPhysicalPairs434, Finset.mem_filter] at hh
      exact hh
    have hKJ := Finset.mem_product.mp hPhys.1
    have hs1 := congrArg Prod.fst hOuter.2
    have hs2 := congrArg Prod.snd hOuter.2
    obtain ⟨u,hu,hm,hn,hprod⟩ := hPhys.2
    have hmcut : z.1 ∈ parityOriginalTypeIIBinaryDyadCut434 K km :=
      Finset.mem_filter.mpr
        ⟨hKJ.1, (parity_original_actual_binary_dyadic_scale_iff434 z.1 km hm).mp hs1⟩
    have hncut : z.2 ∈ parityOriginalTypeIIBinaryDyadCut434 J kn :=
      Finset.mem_filter.mpr
        ⟨hKJ.2, (parity_original_actual_binary_dyadic_scale_iff434 z.2 kn hn).mp hs2⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmcut,hncut⟩,⟨u,hu,hm,hn,hprod⟩⟩
  · intro hz
    have hOuter := Finset.mem_filter.mp hz
    have hCuts := Finset.mem_product.mp hOuter.1
    have hmcut := Finset.mem_filter.mp hCuts.1
    have hncut := Finset.mem_filter.mp hCuts.2
    obtain ⟨u,hu,hm,hn,hprod⟩ := hOuter.2
    have hScale :
        (parityOriginalHistoricalActualZDyadicScale434 z.1,
          parityOriginalHistoricalActualZDyadicScale434 z.2) =
          (2 ^ km, 2 ^ kn) := by
      apply Prod.ext
      · exact (parity_original_actual_binary_dyadic_scale_iff434 z.1 km hm).mpr hmcut.2
      · exact (parity_original_actual_binary_dyadic_scale_iff434 z.2 kn hn).mpr hncut.2
    have hPhys : z ∈ parityOriginalTypeIIPhysicalPairs434 K J Y := by
      simp only [parityOriginalTypeIIPhysicalPairs434, Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨hmcut.1,hncut.1⟩,
         ⟨u,hu,hm,hn,hprod⟩⟩
    exact Finset.mem_filter.mpr ⟨hPhys,hScale⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalBinaryDyadicExactInterval -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Actual binary dyadic cut of a full original interval K=[a,b]
is EXACTLY its (possibly empty) interval intersection, with no extra
artificial endpoint and no change in the full-cell proxy. -/
theorem parity_original_actual_binary_dyad_cut_Icc_eq434
    (a b k : ℕ) :
    parityOriginalTypeIIBinaryDyadCut434 (Finset.Icc a b) k =
      Finset.Icc (max a (2 ^ k)) (min b (2 ^ (k+1)-1)) := by
  classical
  ext m
  simp only [parityOriginalTypeIIBinaryDyadCut434, Finset.mem_filter,
    Finset.mem_Icc]
  have hpow : 0 < 2 ^ (k+1) := pow_pos (by omega) _
  constructor
  · rintro ⟨⟨ha,hb⟩,hlo,hhi⟩
    constructor
    · exact max_le ha hlo
    · apply le_min hb
      omega
  · rintro ⟨hlo,hhi⟩
    have ha : a ≤ m := le_trans (le_max_left _ _) hlo
    have hpowlo : 2 ^ k ≤ m := le_trans (le_max_right _ _) hlo
    have hb : m ≤ b := le_trans hhi (min_le_left _ _)
    have hp : m ≤ 2 ^ (k+1)-1 := le_trans hhi (min_le_right _ _)
    exact ⟨⟨ha,hb⟩,hpowlo,by omega⟩

/-- The literal physical dyadic fibre of an original pair of interval
supports is the positive-shifted physical set for the precise
INTERSECTED original intervals. This is an equality of carriers,
not a claimed analytic bound. -/
theorem parity_original_TypeII_physical_dyadic_fibre_eq_Icc_pairs434
    (a b c d Y km kn : ℕ) :
    (parityOriginalTypeIIPhysicalPairs434
      (Finset.Icc a b) (Finset.Icc c d) Y).filter
      (fun z =>
        (parityOriginalHistoricalActualZDyadicScale434 z.1,
          parityOriginalHistoricalActualZDyadicScale434 z.2) =
          (2 ^ km,2 ^ kn)) =
    parityOriginalTypeIIPhysicalPairs434
      (Finset.Icc (max a (2 ^ km)) (min b (2 ^ (km+1)-1)))
      (Finset.Icc (max c (2 ^ kn)) (min d (2 ^ (kn+1)-1))) Y := by
  rw [parity_original_TypeII_physical_pair_dyadic_fibre_eq_cuts434]
  rw [parity_original_actual_binary_dyad_cut_Icc_eq434,
      parity_original_actual_binary_dyad_cut_Icc_eq434]
  ext z
  simp only [parityOriginalTypeIIPhysicalPairs434, Finset.mem_filter]

/-- Exact reconstruction of each physical source dyadic fibre by a
standard source TypeII triple with a cut original K,J support and the
SAME coefficient function alpha (not a fresh cell normalization). -/
theorem parity_original_TypeII_triple_dyadic_fibre_eq_cut_triple434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (a b c e Y km kn : ℕ) (alpha beta : ℕ → ℂ) :
    (∑ z ∈ (parityOriginalTypeIIPhysicalPairs434
        (Finset.Icc a b) (Finset.Icc c e) Y).filter
          (fun z =>
            (parityOriginalHistoricalActualZDyadicScale434 z.1,
              parityOriginalHistoricalActualZDyadicScale434 z.2) =
              (2 ^ km, 2 ^ kn)),
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0 < z.1 ∧ 0 < z.2 ∧ z.1*z.2=u+2 then
          (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
            (sourceOriginalPAllActualBands 20 L) u *
            Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
            (alpha z.1*beta z.2))
        else 0) =
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
      (Finset.Icc (max a (2 ^ km)) (min b (2 ^ (km+1)-1)))
      (Finset.Icc (max c (2 ^ kn)) (min e (2 ^ (kn+1)-1)))
      alpha beta Y := by
  rw [parity_original_TypeII_physical_dyadic_fibre_eq_Icc_pairs434]
  exact (parity_original_TypeII_triple_eq_physical_pair_restriction434
    d L Psi _ _ alpha beta Y).symm
end Green64Analytic.Parity

end

end

/-! ## PhysicalDyadicOriginalProxyTransport -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Exact original finite TypeII triple invariance under coefficient
replacement that agrees at every m of the ACTUAL K support. No
analytic assumption is introduced. -/
theorem parity_original_TypeII_triple_alpha_congr_on_K434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha alpha' beta : ℕ → ℂ) (Y : ℕ)
    (hAlpha : ∀m∈K,alpha m=alpha' m) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta Y =
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha' beta Y := by
  classical
  unfold parityOriginalShiftTwoOriginalTypeIITripleSource434
  apply Finset.sum_congr rfl
  intro z hz
  have hm := (Finset.mem_product.mp hz).1
  apply Finset.sum_congr rfl
  intro u hu
  rw [hAlpha z.1 hm]

/-- The original full-cell prime/rough coefficient restricted to the
actual outer [a,b] interval already is supported there. Cutting the
support to a smaller dyadic interval produces exactly the native
proxy discrepancy with the new bounds, without renormalizing B_I. -/
theorem parity_original_actual_fullcell_proxy_dyadic_cut_coeff_eq434
    (prime : Bool) (L S gamma : ℝ) (a b k n : ℕ) :
    let a' := max a (2 ^ k)
    let b' := min b (2 ^ (k+1)-1)
    parityOriginalActualFullDyadProxyDifference434 prime L S gamma a' b' n =
      restrictSequence (Finset.Icc a' b')
        (restrictSequence (Finset.Icc a b)
          (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)) n := by
  classical
  dsimp
  have ha : a ≤ max a (2 ^ k) := le_max_left _ _
  have hb : min b (2 ^ (k+1)-1) ≤ b := min_le_left _ _
  rw [parity_original_actual_fullcell_proxy_nested_interval_eq434 prime L S gamma
    a b (max a (2 ^ k)) (min b (2 ^ (k+1)-1)) n ha hb]
  by_cases h : n ∈ Finset.Icc (max a (2 ^ k)) (min b (2 ^ (k+1)-1))
  · have hbig : n ∈ Finset.Icc a b := by
      obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp h
      exact Finset.mem_Icc.mpr
        ⟨(le_max_left _ _).trans hlo,hhi.trans (min_le_left _ _)⟩
    simp [restrictSequence,h,hbig]
  · simp [restrictSequence,h]

/-- Exact SOURCE triple equality: local source interval K is the
actual binary cut of an original full-cell interval, and the cut
coefficient is literally the whole-cell discrepancy restricted to that
K. The companion beta and all 20 Q/P source weights are unchanged. -/
theorem parity_original_TypeII_dyadic_cut_fullcell_proxy_triple_eq434
    (d : ℕ) (L S gamma : ℝ) (Psi : ℝ → ℝ)
    (a b c e Y km kn : ℕ) (prime : Bool) (beta : ℕ → ℂ) :
    let Kcut := Finset.Icc (max a (2 ^ km)) (min b (2 ^ (km+1)-1))
    let Jcut := Finset.Icc (max c (2 ^ kn)) (min e (2 ^ (kn+1)-1))
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi Kcut Jcut
      (restrictSequence (Finset.Icc a b)
        (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b))
      beta Y =
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi Kcut Jcut
      (parityOriginalActualFullDyadProxyDifference434 prime L S gamma
        (max a (2 ^ km)) (min b (2 ^ (km+1)-1))) beta Y := by
  dsimp
  apply parity_original_TypeII_triple_alpha_congr_on_K434
  intro m hm
  have hh := parity_original_actual_fullcell_proxy_dyadic_cut_coeff_eq434
    prime L S gamma a b km m
  simp [restrictSequence,hm] at hh
  simpa only [restrictSequence, Finset.mem_Icc] using hh.symm
end Green64Analytic.Parity

end

end

/-! ## OriginalTypeIIPhysicalDyadGeometry -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- The genuine source smooth Psi support forces every actual
shifted physical m * n=u + 2 pair in a binary U,V dyad to have
EXP(L)/4 < UV ≤ 4 EXP(L), not necessarily EXP(L) ≤ UV.
This is the exact geometry to demand when globally applying local
Type II to literal dyadic intersections; changing L would change
the original Q/P families and is NOT a permissible workaround. -/
theorem parity_original_TypeII_psi_physical_dyad_UV_true_bounds434
    (L U V : ℝ) (Psi : ℝ → ℝ)
    (hL : 0 ≤ L)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (m n u : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hEq : m * n=u + 2)
    (hPsi : Psi ((u:ℝ)/Real.exp L) ≠ 0)
    (hUm : U ≤ (m:ℝ)) (hmU : (m:ℝ) < 2 * U)
    (hVn : V ≤ (n:ℝ)) (hnV : (n:ℝ) < 2 * V) :
    Real.exp L < 4 * U*V ∧ U*V ≤ 4 * Real.exp L := by
  have he : 0 < Real.exp L := Real.exp_pos _
  have he1 : 1 ≤ Real.exp L := by
    calc
      (1:ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hL
  have hsupp : (u:ℝ)/Real.exp L ∈ Set.Icc 1 2 :=
    hPsiSet (by simpa only [Function.mem_support] using hPsi)
  have huLow : Real.exp L ≤ (u:ℝ) := by
    have hh := (Set.mem_Icc.mp hsupp).1
    have hi := (le_div_iff₀ he).mp hh
    nlinarith
  have huUpper : (u:ℝ) ≤ 2 * Real.exp L := by
    have hh := (Set.mem_Icc.mp hsupp).2
    exact (div_le_iff₀ he).mp hh
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have heq : (m:ℝ)*(n:ℝ)=(u:ℝ)+2 := by
    exact_mod_cast hEq
  have hUmPos : 0 < U := by linarith
  have hVnPos : 0 < V := by linarith
  have hProductUpper : (m:ℝ)*(n:ℝ) < (2 * U)*(2 * V) := by
    calc
      (m:ℝ)*(n:ℝ) < (2 * U)*(n:ℝ) :=
        mul_lt_mul_of_pos_right hmU hnpos
      _ ≤ (2 * U)*(2 * V) :=
        mul_le_mul_of_nonneg_left hnV.le (by positivity)
  have hProductLower : U*V ≤ (m:ℝ)*(n:ℝ) := by
    calc
      U*V ≤ (m:ℝ)*V := mul_le_mul_of_nonneg_right hUm hVnPos.le
      _ ≤ (m:ℝ)*(n:ℝ) := mul_le_mul_of_nonneg_left hVn hmpos.le
  constructor
  · nlinarith [hProductUpper,huLow,heq]
  · nlinarith [hProductLower,huUpper,he1,heq]
end Green64Analytic.Parity

end

end

/-! ## OriginalTypeIIPhysicalCutIntegratedAudit -/

section



end

/-! ## OutsideQuarterDyadPsiVanish -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The actual original signed/complex TypeII source vanishes on a
binary m/n dyad outside the *TRUE* product window: the smooth source
Psi(u/exp L) and exact m*n=u+2 already imply exp L < 4UV and
UV <= 4 exp L. No coefficient bound and no zero-proxy assumption. -/
theorem parity_original_TypeII_binary_cut_triple_zero_outside_quarter434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (hL : 0 ≤ L)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (km kn Y : ℕ) (alpha beta : ℕ → ℂ)
    (hOutside : ¬(Real.exp L < 4*(2^km:ℝ)*(2^kn:ℝ) ∧
      (2^km:ℝ)*(2^kn:ℝ) ≤ 4*Real.exp L)) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
      (parityOriginalTypeIIBinaryDyadCut434 K km)
      (parityOriginalTypeIIBinaryDyadCut434 J kn)
      alpha beta Y = 0 := by
  classical
  unfold parityOriginalShiftTwoOriginalTypeIITripleSource434
  apply Finset.sum_eq_zero
  intro z hz
  have hzMem := Finset.mem_product.mp hz
  have hm := (Finset.mem_filter.mp hzMem.1).2
  have hn := (Finset.mem_filter.mp hzMem.2).2
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hEq : 0 < z.1 ∧ 0 < z.2 ∧ z.1*z.2=u+2
  · have hmU : (2^km:ℝ) ≤ (z.1:ℝ) := by exact_mod_cast hm.1
    have hUm : (z.1:ℝ) < 2*(2^km:ℝ) := by
      have hh : z.1 < 2^(km+1) := hm.2
      have hh' : (z.1:ℝ) < (2^(km+1):ℕ) := by exact_mod_cast hh
      simpa [pow_succ, mul_comm] using hh'
    have hnV : (2^kn:ℝ) ≤ (z.2:ℝ) := by exact_mod_cast hn.1
    have hVn : (z.2:ℝ) < 2*(2^kn:ℝ) := by
      have hh : z.2 < 2^(kn+1) := hn.2
      have hh' : (z.2:ℝ) < (2^(kn+1):ℕ) := by exact_mod_cast hh
      simpa [pow_succ, mul_comm] using hh'
    have hPsiZero : Psi ((u:ℝ)/Real.exp L) = 0 := by
      by_contra hNonzero
      exact hOutside (parity_original_TypeII_psi_physical_dyad_UV_true_bounds434
        L (2^km:ℝ) (2^kn:ℝ) Psi hL hPsi z.1 z.2 u
        hEq.1 hEq.2.1 hEq.2.2 hNonzero hmU hUm hnV hVn)
    simp [hEq,hPsiZero]
  · simp [hEq]

/-- The SAME zero statement on the source's literal nested interval
cuts. Their full-cell prime/rough proxy is never recomputed. -/
theorem parity_original_TypeII_Icc_cut_triple_zero_outside_quarter434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (hL : 0 ≤ L)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (a b c e km kn Y : ℕ) (alpha beta : ℕ → ℂ)
    (hOutside : ¬(Real.exp L < 4*(2^km:ℝ)*(2^kn:ℝ) ∧
      (2^km:ℝ)*(2^kn:ℝ) ≤ 4*Real.exp L)) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
      (Finset.Icc (max a (2^km)) (min b (2^(km+1)-1)))
      (Finset.Icc (max c (2^kn)) (min e (2^(kn+1)-1)))
      alpha beta Y = 0 := by
  rw [←parity_original_actual_binary_dyad_cut_Icc_eq434,
    ←parity_original_actual_binary_dyad_cut_Icc_eq434]
  exact parity_original_TypeII_binary_cut_triple_zero_outside_quarter434
    d L Psi hL hPsi _ _ km kn Y alpha beta hOutside
end Green64Analytic.Parity

end

end

/-! ## QuarterEtaNCoefficients -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false

/-- True original h=-2 Fourier pullback Z/(kUV) under exp L ≤ 4UV. -/
theorem parity_original_historical_eta_n_parameter_polylog_quarter434
    (L U V Z K0 : ℝ) (k : ℤ)
    (hL : 0<L) (hU : 0<U) (hV : 0<V) (hk : k≠0)
    (hUV : Real.exp L≤4*U*V)
    (hZpos : 0≤Z) (hZ : Z≤4*Real.exp L*L^(K0+88)) :
    |Z/((k:ℝ)*U*V)| ≤ 16*L^(K0+88) := by
  have hkpos : (0:ℝ) < |(k:ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have hkone := parity_original_nonzero_integer_k_abs_ge_one434 k hk
  have hp := Real.rpow_pos_of_pos hL (K0+88)
  have hUVpos : 0<U*V := mul_pos hU hV
  have hdenpos : (0:ℝ) < |(k:ℝ)| *U*V := by positivity
  have hden : Real.exp L ≤ 4*(|(k:ℝ)| *U*V) := by
    have hh : U*V ≤ |(k:ℝ)| *(U*V) := by
      have hmul := mul_le_mul_of_nonneg_right hkone hUVpos.le
      nlinarith [hmul]
    nlinarith [hUV,hh]
  rw [abs_div,abs_mul,abs_mul,abs_of_nonneg hZpos,
    abs_of_pos hU,abs_of_pos hV]
  apply (div_le_iff₀ hdenpos).mpr
  calc
    _ ≤ 4*Real.exp L*L^(K0+88) := hZ
    _ ≤ 16*L^(K0+88)*(|(k:ℝ)| *U*V) := by
      have hh := mul_le_mul_of_nonneg_left hden (by positivity : 0≤4*L^(K0+88))
      nlinarith [hh]
    _ = (16*L^(K0+88))*(|(k:ℝ)| *U*V) := rfl

/-- Shift 2/(UV) stays at most one in the true quarter-scale dyad. -/
theorem parity_original_historical_eta_n_shift_parameter_le_one_quarter434
    (L U V : ℝ) (hL : 8≤L) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤4*U*V) :
    0≤2/(U*V) ∧ 2/(U*V)≤1 := by
  have hUVpos : 0<U*V := mul_pos hU hV
  have hExpLo : (8:ℝ)≤Real.exp L := by
    have hh := Real.add_one_le_exp L
    linarith
  constructor
  · exact div_nonneg (by norm_num) hUVpos.le
  · apply (div_le_iff₀ hUVpos).mpr
    nlinarith [hUV,hExpLo]
end Green64Analytic.Parity

end

end

/-! ## QuarterEtaNLogArgDerivative -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- LITERAL ORIGINAL Parity(4.14) h=-2 η_n logarithmic argument:
using source U*V≥exp L, E and Z polynomial geometry and k≠0,
the true 3D order-j derivative is at most
  32*L^(K0+88)*j!*A²*2^j + j!*A.
The 2/(UV)*exp(-t1) correction is present and paid; this is
not the incorrect h=0 two-exponential formula. -/
theorem parity_original_historical_eta_n_log_arg_3d_polylog_quarter434
    (L U V Z K0 A : ℝ) (k : ℤ)
    (hL : 8≤L) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤4*U*V) (hk : k≠0)
    (hZ : 0≤Z) (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A) (j : ℕ)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ‖iteratedFDeriv ℝ j
      (fun t : EuclideanSpace ℝ (Fin 3) =>
        parityOriginalHistoricalEtaNLogArg434 U V Z k
          (EuclideanSpace.equiv (Fin 3) ℝ t)) t‖ ≤
    32*L^(K0+88)*(j.factorial:ℝ)*A^2*(2:ℝ)^j+(j.factorial:ℝ)*A := by
  have hLp : 0<L := by linarith
  let a := Z/((k:ℝ)*U*V)
  let b := 2/(U*V)
  have ha := parity_original_historical_eta_n_parameter_polylog_quarter434
    L U V Z K0 k hLp hU hV hk hUV hZ hZupper
  have hb := (parity_original_historical_eta_n_shift_parameter_le_one_quarter434
    L U V hL hU hV hUV)
  have hbase := parity_original_historical_eta_n_real_3d_fderiv_log_box434
    A hA a b j t h0 h1 h2
  have hFun : (fun t : EuclideanSpace ℝ (Fin 3) =>
        parityOriginalHistoricalEtaNLogArg434 U V Z k
          (EuclideanSpace.equiv (Fin 3) ℝ t)) =
      (fun t => a*(Real.exp (t 2-t 0)-Real.exp (t 2-t 1)) +
        b*Real.exp (-(t 0))) := by
    funext x
    exact parity_original_historical_eta_n_log_arg_exp_difference434 U V Z k x
  rw [hFun]
  have hleft : 0≤2*(j.factorial:ℝ)*A^2*(2:ℝ)^j := by positivity
  have hright : 0≤(j.factorial:ℝ)*A := by positivity
  have haBound : 2*|a| *(j.factorial:ℝ)*A^2*(2:ℝ)^j ≤
      32*L^(K0+88)*(j.factorial:ℝ)*A^2*(2:ℝ)^j := by
    have hm := mul_le_mul_of_nonneg_right ha hleft
    nlinarith [hm]
  have hbAbs : |b|≤1 := by
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hbBound : |b| *(j.factorial:ℝ)*A≤(j.factorial:ℝ)*A := by
    nlinarith [mul_le_mul_of_nonneg_right hbAbs hright]
  exact hbase.trans (add_le_add haBound hbBound)
end Green64Analytic.Parity

end

end

/-! ## QuarterEtaNAllDerivatives -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The FULL original Parity(4.14) h=-2 n-argument has genuine
all-positive-order Euclidean derivative bound with ONE source
polylog base:
  ||D^i g_n(t)|| ≤ (L^(K0+89))^i   for 1≤ i≤J
on fixed |t_r|≤log A, from the original physical Z upper range,
UV≥exp L, nonzero k, and no missing 2/(UV) correction.
The lower threshold on L depends only on fixed J and fixed A. -/
theorem parity_original_historical_eta_n_log_arg_all_derivatives_uniform_quarter434
    (L U V Z K0 A : ℝ) (k : ℤ)
    (hL : 8≤L) (hK0 : 0≤K0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤4*U*V)
    (hk : k≠0) (hZ : 0≤Z)
    (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A) (J : ℕ)
    (hLarge : 32*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
      (J.factorial:ℝ)*A ≤ L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ∀ (i : ℕ), 1 ≤ i → i ≤ J →
      ‖iteratedFDeriv ℝ i
        (fun t : EuclideanSpace ℝ (Fin 3) =>
          parityOriginalHistoricalEtaNLogArg434 U V Z k
            (EuclideanSpace.equiv (Fin 3) ℝ t)) t‖ ≤
      (L^(K0+89))^i := by
  have hLp : 0<L := by linarith
  have hL1 : (1:ℝ)≤L := by linarith
  have hBpos : 0<L^(K0+88) := Real.rpow_pos_of_pos hLp _
  have hB1 : (1:ℝ)≤L^(K0+88) := Real.one_le_rpow hL1 (by linarith)
  have hbase1 : (1:ℝ)≤L^(K0+89) := Real.one_le_rpow hL1 (by linarith)
  intro i hi hJ
  have hfactNat : i.factorial≤J.factorial := Nat.factorial_le hJ
  have hfact : (i.factorial:ℝ)≤(J.factorial:ℝ) := by exact_mod_cast hfactNat
  have h2pow : (2:ℝ)^i≤(2:ℝ)^J := pow_le_pow_right₀ (by norm_num) hJ
  have hBase := parity_original_historical_eta_n_log_arg_3d_polylog_quarter434
    L U V Z K0 A k hL hU hV hUV hk hZ hZupper hA i t h0 h1 h2
  have hFactPow : (i.factorial:ℝ)*(2:ℝ)^i ≤ (J.factorial:ℝ)*(2:ℝ)^J :=
    mul_le_mul hfact h2pow (by positivity) (by positivity)
  have hTerm1 : 32*L^(K0+88)*(i.factorial:ℝ)*A^2*(2:ℝ)^i ≤
      32*L^(K0+88)*(J.factorial:ℝ)*A^2*(2:ℝ)^J := by
    have hh := mul_le_mul_of_nonneg_left hFactPow (by positivity : 0≤32*L^(K0+88)*A^2)
    nlinarith [hh]
  have hTerm2 : (i.factorial:ℝ)*A≤(J.factorial:ℝ)*A :=
    mul_le_mul_of_nonneg_right hfact hA.le
  have hTerm : 32*L^(K0+88)*(i.factorial:ℝ)*A^2*(2:ℝ)^i+
      (i.factorial:ℝ)*A ≤
      32*L^(K0+88)*(J.factorial:ℝ)*A^2*(2:ℝ)^J+
      (J.factorial:ℝ)*A := add_le_add hTerm1 hTerm2
  have hD :
      32*L^(K0+88)*(J.factorial:ℝ)*A^2*(2:ℝ)^J+
        (J.factorial:ℝ)*A ≤ L^(K0+89) := by
    have hm := mul_le_mul_of_nonneg_right hLarge hBpos.le
    have hpow : L^(K0+89)=L^(K0+88)*L := by
      have hEq : K0+89=(K0+88)+1 := by ring
      rw [hEq,Real.rpow_add hLp,Real.rpow_one]
    have hlast : (J.factorial:ℝ)*A ≤ (J.factorial:ℝ)*A*L^(K0+88) := by
      have hC : (0:ℝ)≤(J.factorial:ℝ)*A := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hB1 hC]
    rw [hpow]
    nlinarith [hm,hlast]
  have hPow : L^(K0+89)≤(L^(K0+89))^i := by
    have hh := pow_le_pow_right₀ hbase1 hi
    simpa only [pow_one] using hh
  exact hBase.trans (hTerm.trans (hD.trans hPow))

/-- The ACTUAL historical original h=-2 η_n pulledback
THREE-DIMENSIONAL cutoff now has uniform pointwise order-J
Fréchet derivative bound
  J! K^n_J L^((K0+89)(J+1))
for every physical Euclidean log point in the fixed buffer box,
with the actual source Z/(kUV) and 2/(UV) correction. No missing
source Fourier factor or analytic hypothesis; remaining original
3D Schwartz seminorm proof is a finite product with η_e and buffers. -/
theorem parity_original_historical_actual_eta_n_3d_composed_polylog_quarter434
    (L U V Z K0 A : ℝ) (k : ℤ)
    (hL : 8≤L) (hK0 : 0≤K0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤4*U*V)
    (hk : k≠0) (hZ : 0≤Z)
    (hZupper : Z≤4*Real.exp L*L^(K0+88))
    (hA : 0<A) (J : ℕ)
    (hLarge : 32*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
      (J.factorial:ℝ)*A ≤ L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ‖iteratedFDeriv ℝ J
      (parityOriginalHistoricalActualEtaN434 ∘
        (fun t : EuclideanSpace ℝ (Fin 3) =>
          parityOriginalHistoricalEtaNLogArg434 U V Z k
            (EuclideanSpace.equiv (Fin 3) ℝ t))) t‖ ≤
    (J.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 J *
      L^((K0+89)*((J:ℝ)+1)) := by
  let g : EuclideanSpace ℝ (Fin 3) → ℝ := fun t =>
    parityOriginalHistoricalEtaNLogArg434 U V Z k
      (EuclideanSpace.equiv (Fin 3) ℝ t)
  have hg : ContDiff ℝ ∞ g :=
    (parity_original_historical_eta_n_log_arg_smooth434 U V Z k).comp
      (EuclideanSpace.equiv (Fin 3) ℝ).contDiff
  have hd := parity_original_historical_eta_n_log_arg_all_derivatives_uniform_quarter434
    L U V Z K0 A k hL hK0 hU hV hUV hk hZ hZupper
    hA J hLarge t h0 h1 h2
  exact parity_original_historical_eta_n_3d_composition_polylog434
    L hL J (K0+89) (by linarith) g hg t hd
end Green64Analytic.Parity

end

end

/-! ## QuarterBoxEtaN3D -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- REAL original PARITY (4.14) all-order η_n 3D smoothness on
the CORRECTED cap-free source box Z≤24Cbox expL L^(K0+88):
‖D^J η_n(g_n)‖ ≤ J! K_J^ηn L^((K0+90)(J+1)).
This re-proves the uniform derivative budget for arbitrary
fixed UV≤Cbox expL instead of incorrectly applying a previous
source theorem whose Z hypothesis depended on artificial Y0.
All constants K_J remain truly SOURCE-fixed. -/
theorem parity_original_historical_box_eta_n_3d_composed_polylog_quarter434
    (L U V Z K0 Cbox A : ℝ) (k : ℤ)
    (hL : 8≤L) (hK0 : 0≤K0) (hCbox : 0≤Cbox)
    (hLargeC : 6*Cbox≤L)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤4*U*V)
    (hk : k≠0) (hZ : 0≤Z)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88))
    (hA : 0<A) (J : ℕ)
    (hLarge : 32*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
      (J.factorial:ℝ)*A≤L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ‖iteratedFDeriv ℝ J
      (parityOriginalHistoricalActualEtaN434 ∘
        (fun t : EuclideanSpace ℝ (Fin 3) =>
          parityOriginalHistoricalEtaNLogArg434 U V Z k
            (EuclideanSpace.equiv (Fin 3) ℝ t))) t‖ ≤
    (J.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 J *
      L^((K0+90)*((J:ℝ)+1)) := by
  have hZold := parity_original_historical_box_Z_upper_to_eta_n_polylog434
    L Z K0 Cbox hL hCbox hLargeC hZupper
  have hOld := parity_original_historical_actual_eta_n_3d_composed_polylog_quarter434
    L U V Z (K0+1) A k hL (by linarith) hU hV hUV hk
    hZ hZold hA J hLarge t h0 h1 h2
  simpa only [show (K0+1)+89=K0+90 by ring] using hOld
end Green64Analytic.Parity

end

end

/-! ## QuarterFiveFactor3D -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 24500000

/-- All FIVE corrected original Parity(4.14) physical 3D factors
(including H0-independent η_e and η_n source windows) have
fixed order-J derivative ≤ M_J L^((K0+90)(J+1)) on the REAL
full cap-free B' z-height ≤24 Cbox expL L^(K0+88), assuming
Cbox fixed and L≥6Cbox. The exact original h=-2 nonlinear
term 2/(UV), 3 log buffers and true ηe,ηn are unchanged.
This replaces rather than reuses an invalid old Y0 upper bound. -/
theorem parity_original_historical_box_five_factors_all_order_polylog_quarter434
    (L U E V Z K0 Cbox A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤4*U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 → -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J : ℕ)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 32*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
       (J.factorial:ℝ)*A≤L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ∀ (i : Fin 5) (r : ℕ), r≤J →
      ‖iteratedFDeriv ℝ r
        (parityOriginalHistoricalActualFive3DFactors434 L U E V Z hL k buf i) t‖ ≤
      parityOriginalHistoricalFiveFactorFixedBudget434 A buf hBufSmooth hBufSupport J *
        L^((K0+90)*((J:ℝ)+1)) := by
  let M := parityOriginalHistoricalFiveFactorFixedBudget434
    A buf hBufSmooth hBufSupport J
  let R := L^((K0+90)*((J:ℝ)+1))
  have hM : 1≤M := parity_original_historical_five_factor_fixed_budget_ge_one434
    A buf hBufSmooth hBufSupport J
  have hR : 1≤R := by
    have hh := parity_original_3d_source_log_power_ge_one434 L (K0+1)
      hL (by linarith : 0≤K0+1) J
    simpa only [show (K0+1)+89=K0+90 by ring] using hh
  have hMR : 0≤M := by linarith
  have hRR : 0≤R := by linarith
  have hB (r : ℕ) (hr : r≤J) :
      (r.factorial:ℝ)*parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434
        A buf hBufSmooth hBufSupport r ≤ M :=
    (parity_original_historical_five_factor_individual_constant_le434
      A buf hBufSmooth hBufSupport J r hr).2.2
  have hEE (r : ℕ) (hr : r≤J) :
      (r.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 r ≤ M :=
    (parity_original_historical_five_factor_individual_constant_le434
      A buf hBufSmooth hBufSupport J r hr).1
  have hNN (r : ℕ) (hr : r≤J) :
      (r.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 r ≤ M :=
    (parity_original_historical_five_factor_individual_constant_le434
      A buf hBufSmooth hBufSupport J r hr).2.1
  have hPower (r : ℕ) (hr : r≤J) :
      L^((K0+90)*((r:ℝ)+1)) ≤ R := by
    have hh := parity_original_3d_source_log_power_mono434 L (K0+1) hL
      (by linarith : 0≤K0+1) J r hr
    simpa only [show (K0+1)+89=K0+90 by ring] using hh
  have hBase (i : Fin 3) (r : ℕ) (hr : r≤J) :
      ‖iteratedFDeriv ℝ r
        (fun x : EuclideanSpace ℝ (Fin 3) => buf (x i)) t‖ ≤ M*R := by
    have hh := parity_original_historical_fixed_log_buffer_3d_fderiv_le434
      A buf hBufSmooth hBufSupport i r t
    calc
      _ ≤ (r.factorial:ℝ)*parityOriginalHistoricalFixedLogBufferDerivativeEnvelope434
          A buf hBufSmooth hBufSupport r := hh
      _ ≤ M := hB r hr
      _ = M*1 := by ring
      _ ≤ M*R := mul_le_mul_of_nonneg_left hR hMR
  intro i r hr
  fin_cases i
  · exact hBase 0 r hr
  · exact hBase 1 r hr
  · exact hBase 2 r hr
  · have hThreshold := parity_original_eta_e_threshold_mono434
      A hA.le J r hr L hLargeE
    have hh := parity_original_historical_actual_eta_e_3d_composed_polylog434
      L U E K0 A k hL hK0 hU hE hk hA r hThreshold t h0 h1
    change ‖iteratedFDeriv ℝ r
      ((parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL) ∘
       (fun x : EuclideanSpace ℝ (Fin 3) =>
         parityOriginalHistoricalEtaELogArg434 U E k
           (EuclideanSpace.equiv (Fin 3) ℝ x))) t‖ ≤ M*R
    calc
      _ ≤ (r.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 r *
          L^((K0+89)*((r:ℝ)+1)) := hh
      _ ≤ (r.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 r *
          L^((K0+90)*((r:ℝ)+1)) := by
            have hExp : (K0+89)*((r:ℝ)+1)≤(K0+90)*((r:ℝ)+1) := by
              have hRp : (0:ℝ)≤(r:ℝ)+1 := by positivity
              nlinarith
            have hPow' := Real.rpow_le_rpow_of_exponent_le
              (by linarith : (1:ℝ)≤L) hExp
            have hCoef : 0≤(r.factorial:ℝ)*parityOriginalEtaEDerivativeFixedEnvelope434 r := by
              have hh := (parity_original_historical_five_factor_fixed_envelopes_nonneg434
                A buf hBufSmooth hBufSupport r).1
              exact mul_nonneg (Nat.cast_nonneg _) hh
            exact mul_le_mul_of_nonneg_left hPow' hCoef
      _ ≤ M*L^((K0+90)*((r:ℝ)+1)) := by
        exact mul_le_mul_of_nonneg_right (hEE r hr) (Real.rpow_nonneg (by linarith : 0≤L) _)
      _ ≤ M*R := mul_le_mul_of_nonneg_left (hPower r hr) hMR
  · have hThreshold :
        32*A^2*(r.factorial:ℝ)*(2:ℝ)^r+(r.factorial:ℝ)*A≤L := by
      have hFac : (r.factorial:ℝ)≤(J.factorial:ℝ) := by
        exact_mod_cast Nat.factorial_le hr
      have hPow : (2:ℝ)^r≤(2:ℝ)^J := pow_le_pow_right₀ (by norm_num) hr
      have hProd : (r.factorial:ℝ)*(2:ℝ)^r≤(J.factorial:ℝ)*(2:ℝ)^J :=
        mul_le_mul hFac hPow (by positivity) (by positivity)
      have h1 := mul_le_mul_of_nonneg_left hProd (by positivity : 0≤32*A^2)
      have h2 := mul_le_mul_of_nonneg_right hFac hA.le
      nlinarith [h1,h2,hLargeN]
    have hh := parity_original_historical_box_eta_n_3d_composed_polylog_quarter434
      L U V Z K0 Cbox A k hL hK0 hCbox hLargeC hU hV hUV hk hZ hZupper
      hA r hThreshold t h0 h1 h2
    change ‖iteratedFDeriv ℝ r
      (parityOriginalHistoricalActualEtaN434 ∘
       (fun x : EuclideanSpace ℝ (Fin 3) =>
         parityOriginalHistoricalEtaNLogArg434 U V Z k
           (EuclideanSpace.equiv (Fin 3) ℝ x))) t‖ ≤ M*R
    calc
      _ ≤ (r.factorial:ℝ)*parityOriginalEtaNDerivativeFixedEnvelope434 r *
          L^((K0+90)*((r:ℝ)+1)) := hh
      _ ≤ M*L^((K0+90)*((r:ℝ)+1)) := by
        exact mul_le_mul_of_nonneg_right (hNN r hr) (Real.rpow_nonneg (by linarith : 0≤L) _)
      _ ≤ M*R := mul_le_mul_of_nonneg_left (hPower r hr) hMR
end Green64Analytic.Parity

end

end

/-! ## QuarterPhysicalDyadicSum -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Source support quarter-product gate on the *literal distinct*
actual binary dyadic pair scales, using the original fixed L. -/
def parityOriginalTypeIIQuarterProductGate434 (L : ℝ) (scale : ℕ×ℕ) : Prop :=
  Real.exp L < 4*(scale.1:ℝ)*(scale.2:ℝ) ∧
    (scale.1:ℝ)*(scale.2:ℝ) ≤ 4*Real.exp L

/-- If one actual physical pair has the given binary dyad scale,
then its two factors are in [U,2U), [V,2V), respectively. -/
theorem parity_original_actual_pair_scale_real_bounds434
    (z scale : ℕ×ℕ)
    (hScale : (parityOriginalHistoricalActualZDyadicScale434 z.1,
      parityOriginalHistoricalActualZDyadicScale434 z.2) = scale)
    (hm : 0<z.1) (hn : 0<z.2) :
    (scale.1:ℝ) ≤ (z.1:ℝ) ∧ (z.1:ℝ) < 2*(scale.1:ℝ) ∧
      (scale.2:ℝ) ≤ (z.2:ℝ) ∧ (z.2:ℝ) < 2*(scale.2:ℝ) := by
  have h1 := parity_original_historical_actual_z_in_own_dyad434 z.1 hm
  have h2 := parity_original_historical_actual_z_in_own_dyad434 z.2 hn
  have hmNat : scale.1 ≤ z.1 ∧ z.1 < 2*scale.1 := by
    simpa only [←(congrArg Prod.fst hScale)] using h1.2
  have hnNat : scale.2 ≤ z.2 ∧ z.2 < 2*scale.2 := by
    simpa only [←(congrArg Prod.snd hScale)] using h2.2
  constructor
  · exact_mod_cast hmNat.1
  constructor
  · exact_mod_cast hmNat.2
  constructor
  · exact_mod_cast hnNat.1
  · exact_mod_cast hnNat.2

/-- On a distinct actually attained binary dyadic pair which lies
outside the true quarter-UV geometry, EVERY source weighted summand
is identically zero. This is a physical support statement, NOT a
complex-subsums cancellation or a per-dyad analytic bound. -/
theorem parity_original_TypeII_nonquarter_physical_fibre_sum_zero434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (hL : 0≤L)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (Y : ℕ) (alpha beta : ℕ → ℂ)
    (scale : ℕ×ℕ) (hOutside : ¬parityOriginalTypeIIQuarterProductGate434 L scale) :
    (∑ z ∈ (parityOriginalTypeIIPhysicalPairs434 K J Y).filter
      (fun z => (parityOriginalHistoricalActualZDyadicScale434 z.1,
        parityOriginalHistoricalActualZDyadicScale434 z.2) = scale),
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
          (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
            (sourceOriginalPAllActualBands 20 L) u *
            Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
            (alpha z.1*beta z.2))
        else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro z hz
  have hs := (Finset.mem_filter.mp hz).2
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hEq : 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2
  · have hBounds := parity_original_actual_pair_scale_real_bounds434
      z scale hs hEq.1 hEq.2.1
    have hPsiZero : Psi ((u:ℝ)/Real.exp L) = 0 := by
      by_contra hNonzero
      have hGood := parity_original_TypeII_psi_physical_dyad_UV_true_bounds434
        L (scale.1:ℝ) (scale.2:ℝ) Psi hL hPsi z.1 z.2 u
        hEq.1 hEq.2.1 hEq.2.2 hNonzero
        hBounds.1 hBounds.2.1 hBounds.2.2.1 hBounds.2.2.2
      exact hOutside hGood
    simp [hEq,hPsiZero]
  · simp [hEq]

/-- ORIGINAL full finite Parity source triple is EXACTLY its sum over
only physically attained, product-admissible quarter-UV dyadic
pairs. All out-of-quarter contributions vanish termwise due to the
actual shifted smooth support, so this removes no signed source
mass, changes no full-cell normalization, and pays no cardinality. -/
theorem parity_original_TypeII_triple_eq_quarter_physical_dyadic_sum434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (hL : 0≤L)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (Y : ℕ) (alpha beta : ℕ → ℂ) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta Y =
    ∑ scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
        (parityOriginalTypeIIPhysicalPairs434 K J Y)).filter
          (parityOriginalTypeIIQuarterProductGate434 L),
      ∑ z ∈ (parityOriginalTypeIIPhysicalPairs434 K J Y).filter
        (fun z => (parityOriginalHistoricalActualZDyadicScale434 z.1,
          parityOriginalHistoricalActualZDyadicScale434 z.2) = scale),
        ∑ u ∈ Finset.Ioc 0 Y,
          if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
            (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
              (sourceOriginalPAllActualBands 20 L) u *
              Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
              (alpha z.1*beta z.2))
          else 0 := by
  classical
  rw [parity_original_TypeII_triple_eq_physical_dyadic_fibres434]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro scale hs
  by_cases hQuarter : parityOriginalTypeIIQuarterProductGate434 L scale
  · simp [hQuarter]
  · simp only [if_neg hQuarter]
    exact parity_original_TypeII_nonquarter_physical_fibre_sum_zero434
      d L Psi hL hPsi K J Y alpha beta scale hQuarter
end Green64Analytic.Parity

end

end

/-! ## QuarterDyadicCutTripleExact -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- Original finite physical pair source filtered to one actual
binary scale pair is *exactly* the positive shifted m*n=u+2 source
on the corresponding factor scale-filtered K/J carrier. No need
to postulate that scale is a dyadic power or to alter alpha/beta. -/
theorem parity_original_TypeII_fibre_eq_scale_filtered_pair_carrier434
    (K J : Finset ℕ) (Y : ℕ) (scale : ℕ×ℕ) :
    (parityOriginalTypeIIPhysicalPairs434 K J Y).filter
      (fun z => (parityOriginalHistoricalActualZDyadicScale434 z.1,
        parityOriginalHistoricalActualZDyadicScale434 z.2) = scale) =
    parityOriginalTypeIIPhysicalPairs434
      (K.filter (fun m => parityOriginalHistoricalActualZDyadicScale434 m = scale.1))
      (J.filter (fun n => parityOriginalHistoricalActualZDyadicScale434 n = scale.2))
      Y := by
  classical
  ext z
  constructor
  · intro hz
    have hF := Finset.mem_filter.mp hz
    have hP : z ∈ K.product J ∧
        (∃ u ∈ Finset.Ioc 0 Y,
          0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2) := by
      simpa only [parityOriginalTypeIIPhysicalPairs434,Finset.mem_filter] using hF.1
    have hKJ := Finset.mem_product.mp hP.1
    have hFirst := congrArg Prod.fst hF.2
    have hSecond := congrArg Prod.snd hF.2
    have hm : z.1 ∈ K.filter
        (fun m => parityOriginalHistoricalActualZDyadicScale434 m = scale.1) :=
      Finset.mem_filter.mpr ⟨hKJ.1,hFirst⟩
    have hn : z.2 ∈ J.filter
        (fun n => parityOriginalHistoricalActualZDyadicScale434 n = scale.2) :=
      Finset.mem_filter.mpr ⟨hKJ.2,hSecond⟩
    change z ∈ parityOriginalTypeIIPhysicalPairs434 _ _ _
    simp only [parityOriginalTypeIIPhysicalPairs434,Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨hm,hn⟩,hP.2⟩
  · intro hz
    have hP : z ∈ (K.filter
          (fun m => parityOriginalHistoricalActualZDyadicScale434 m = scale.1)).product
        (J.filter
          (fun n => parityOriginalHistoricalActualZDyadicScale434 n = scale.2)) ∧
        (∃ u ∈ Finset.Ioc 0 Y,
          0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2) := by
      simpa only [parityOriginalTypeIIPhysicalPairs434,Finset.mem_filter] using hz
    have hKJ := Finset.mem_product.mp hP.1
    have hm := Finset.mem_filter.mp hKJ.1
    have hn := Finset.mem_filter.mp hKJ.2
    have hScale : (parityOriginalHistoricalActualZDyadicScale434 z.1,
        parityOriginalHistoricalActualZDyadicScale434 z.2) = scale := by
      apply Prod.ext
      · exact hm.2
      · exact hn.2
    have hPhysical : z ∈ parityOriginalTypeIIPhysicalPairs434 K J Y := by
      simp only [parityOriginalTypeIIPhysicalPairs434,Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨hm.1,hn.1⟩,hP.2⟩
    exact Finset.mem_filter.mpr ⟨hPhysical,hScale⟩

/-- A physical scale-fibre sum equals the ORIGINAL full weighted
TypeII triple on its actual scale-filtered original factor sets.
No independent E, beta, Q or proxy renormalization is introduced. -/
theorem parity_original_TypeII_physical_fibre_eq_scale_cut_triple434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (Y : ℕ) (alpha beta : ℕ → ℂ)
    (scale : ℕ×ℕ) :
    (∑ z ∈ (parityOriginalTypeIIPhysicalPairs434 K J Y).filter
        (fun z => (parityOriginalHistoricalActualZDyadicScale434 z.1,
          parityOriginalHistoricalActualZDyadicScale434 z.2) = scale),
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
          (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
            (sourceOriginalPAllActualBands 20 L) u *
            Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
            (alpha z.1*beta z.2))
        else 0) =
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
      (K.filter (fun m => parityOriginalHistoricalActualZDyadicScale434 m = scale.1))
      (J.filter (fun n => parityOriginalHistoricalActualZDyadicScale434 n = scale.2))
      alpha beta Y := by
  rw [parity_original_TypeII_fibre_eq_scale_filtered_pair_carrier434]
  exact (parity_original_TypeII_triple_eq_physical_pair_restriction434
    d L Psi _ _ alpha beta Y).symm

/-- The complete original TypeII triple is exactly the finite sum
of source Bprime triples on ACTUAL scale-filtered factor supports
restricted to physically admissible quarter-product pairs. No
unknown conditionally cancelled other dyads or hidden family cost. -/
theorem parity_original_TypeII_full_triple_eq_quarter_scale_cut_triples434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (hL : 0≤L)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (Y : ℕ) (alpha beta : ℕ → ℂ) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
      K J alpha beta Y =
    ∑ scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
        (parityOriginalTypeIIPhysicalPairs434 K J Y)).filter
        (parityOriginalTypeIIQuarterProductGate434 L),
      parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
        (K.filter (fun m => parityOriginalHistoricalActualZDyadicScale434 m = scale.1))
        (J.filter (fun n => parityOriginalHistoricalActualZDyadicScale434 n = scale.2))
        alpha beta Y := by
  rw [parity_original_TypeII_triple_eq_quarter_physical_dyadic_sum434
    d L Psi hL hPsi K J Y alpha beta]
  apply Finset.sum_congr rfl
  intro scale hs
  exact parity_original_TypeII_physical_fibre_eq_scale_cut_triple434
    d L Psi K J Y alpha beta scale
end Green64Analytic.Parity

end

end

/-! ## QuarterPhysicalIntervalSourceSum -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 2100000

/-- If original source K and J are genuine positive integer intervals,
then each attained binary scale fibre is its EXACT nested Icc cut.
The original b629 full-cell coefficient remains unchanged. -/
theorem parity_original_TypeII_positive_Icc_scale_fibre_eq_nested434
    (a b c e Y : ℕ) (ha : 0<a) (hc : 0<c)
    (scale : ℕ×ℕ)
    (hAttained : scale ∈ parityOriginalActualTypeIIDyadicPairScales434
      (parityOriginalTypeIIPhysicalPairs434
        (Finset.Icc a b) (Finset.Icc c e) Y)) :
    ((Finset.Icc a b).filter
      (fun m => parityOriginalHistoricalActualZDyadicScale434 m = scale.1)) =
      Finset.Icc (max a scale.1) (min b (2*scale.1-1)) ∧
    ((Finset.Icc c e).filter
      (fun n => parityOriginalHistoricalActualZDyadicScale434 n = scale.2)) =
      Finset.Icc (max c scale.2) (min e (2*scale.2-1)) := by
  classical
  obtain ⟨z,hz,hscale⟩ := Finset.mem_image.mp hAttained
  let km : ℕ := Nat.log 2 z.1
  let kn : ℕ := Nat.log 2 z.2
  have hScaleM : scale.1 = 2^km := by
    have hh := congrArg Prod.fst hscale
    simpa only [parityOriginalHistoricalActualZDyadicScale434,km] using hh.symm
  have hScaleN : scale.2 = 2^kn := by
    have hh := congrArg Prod.snd hscale
    simpa only [parityOriginalHistoricalActualZDyadicScale434,kn] using hh.symm
  have hK : ∀m∈Finset.Icc a b, 0 < m := by
    intro m hm
    exact lt_of_lt_of_le ha (Finset.mem_Icc.mp hm).1
  have hJ : ∀n∈Finset.Icc c e, 0 < n := by
    intro n hn
    exact lt_of_lt_of_le hc (Finset.mem_Icc.mp hn).1
  constructor
  · rw [hScaleM]
    rw [parity_original_positive_scale_fibre_eq_binary_cut434 _ km hK]
    rw [parity_original_actual_binary_dyad_cut_Icc_eq434]
    simp [pow_succ,mul_comm]
  · rw [hScaleN]
    rw [parity_original_positive_scale_fibre_eq_binary_cut434 _ kn hJ]
    rw [parity_original_actual_binary_dyad_cut_Icc_eq434]
    simp [pow_succ,mul_comm]

/-- Literal original Parity positive-interval source triple = the
quarter-product finite sum of source TypeII triples over true nested
binary Icc × Icc cuts. No replacement at an unproved per-dyad price:
this is a COMPLETE exact finite source equality, independently of
alpha/beta, and all unused quarter-product pairs have zero source.
-/
theorem parity_original_TypeII_positive_Icc_triple_eq_quarter_nested_cuts434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (hL : 0≤L)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (a b c e Y : ℕ) (ha : 0<a) (hc : 0<c)
    (alpha beta : ℕ → ℂ) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
      (Finset.Icc a b) (Finset.Icc c e) alpha beta Y =
    ∑ scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
        (parityOriginalTypeIIPhysicalPairs434
          (Finset.Icc a b) (Finset.Icc c e) Y)).filter
          (parityOriginalTypeIIQuarterProductGate434 L),
      parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
        (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
        (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
        alpha beta Y := by
  rw [parity_original_TypeII_full_triple_eq_quarter_scale_cut_triples434
    d L Psi hL hPsi (Finset.Icc a b) (Finset.Icc c e) Y alpha beta]
  apply Finset.sum_congr rfl
  intro scale hs
  obtain ⟨hM,hN⟩ := parity_original_TypeII_positive_Icc_scale_fibre_eq_nested434
    a b c e Y ha hc scale (Finset.mem_filter.mp hs).1
  rw [hM,hN]
end Green64Analytic.Parity

end

end

/-! ## QuarterFullCellB629CutLegal -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false

/-- Every literal intersection of an original source full interval
[a,b] with a binary dyad has the SAME fine interval legality
`2≤a'`, `b'≤2a'`, and `b'≤exp(2L)` needed by the actual b629
source theorem, whenever those original full-interval source bounds
were fixed beforehand. This is numerical, not an analytic claim. -/
theorem parity_original_actual_quarter_nested_fine_interval_legal434
    (a b km : ℕ) (L : ℝ)
    (ha : 2≤a) (hb : b≤2*a) (hExp : (b:ℝ)≤Real.exp (2*L)) :
    let a' := max a (2^km)
    let b' := min b (2^(km+1)-1)
    2≤a' ∧ b'≤2*a' ∧ (b':ℝ)≤Real.exp (2*L) := by
  dsimp
  have ha' : a ≤ max a (2^km) := le_max_left _ _
  have hb' : min b (2^(km+1)-1)≤b := min_le_left _ _
  constructor
  · omega
  constructor
  · omega
  · exact (show ((min b (2^(km+1)-1):ℕ):ℝ) ≤ (b:ℝ) from by exact_mod_cast hb').trans hExp

/-- Crucial original Parity(7.1)/(7.3) source fidelity: on a literal
nested binary interval Kcut, the ORIGINAL full-cell proxy alpha
restricted to Kcut is pointwise EXACTLY the genuine b629 actual fine
prime/rough alpha built on that cut. The full cell B_I values are
independent of both interval endpoints, so NO boundary renormalizing
occurs, even at cut end-cells. -/
theorem parity_original_actual_quarter_fullcell_alpha_eq_b629_cut434
    (prime : Bool) (L S gamma : ℝ) (a b km m : ℕ) :
    let ac := max a (2^km)
    let bc := min b (2^(km+1)-1)
    restrictSequence (Finset.Icc ac bc)
      (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b) m =
    restrictSequence (Finset.Icc ac bc)
      (b629ActualFineAlpha434 prime L S gamma ac bc) m := by
  classical
  dsimp
  have ha : a ≤ max a (2^km) := le_max_left _ _
  have hb : min b (2^(km+1)-1)≤b := min_le_left _ _
  have hh := parity_original_actual_fullcell_proxy_nested_interval_eq434
    prime L S gamma a b (max a (2^km))
    (min b (2^(km+1)-1)) m ha hb
  have hB629 := parity_original_actual_full_dyad_proxy_eq_b629434
    prime L S gamma (max a (2^km)) (min b (2^(km+1)-1)) m
  by_cases hm : m ∈ Finset.Icc (max a (2^km)) (min b (2^(km+1)-1))
  · simpa only [restrictSequence,hm,ite_true] using hh.symm.trans hB629
  · simp [restrictSequence,hm]
end Green64Analytic.Parity

end

end

/-! ## QuarterPhysicalIccLossLedger -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Number of ACTUALLY ATTAINED quarter-product dyadic pair intervals
in a true positive Parity source is at most the exact pre-existing
log-square physical bound. This is independent of the number of
m,n,u triples or arbitrary fine/beta outer allocations. -/
theorem parity_original_actual_quarter_Icc_dyadic_card_le_log_sq434
    (a b c e Y : ℕ) (L : ℝ) :
    (((parityOriginalActualTypeIIDyadicPairScales434
       (parityOriginalTypeIIPhysicalPairs434
         (Finset.Icc a b) (Finset.Icc c e) Y)).filter
        (parityOriginalTypeIIQuarterProductGate434 L)).card) ≤
      (Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1) := by
  calc
    _ ≤ (parityOriginalActualTypeIIDyadicPairScales434
       (parityOriginalTypeIIPhysicalPairs434
         (Finset.Icc a b) (Finset.Icc c e) Y)).card :=
      Finset.card_filter_le _ _
    _ ≤ (Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1) :=
      parity_original_TypeII_physical_pair_dyadic_card_le_log_sq434
        (Finset.Icc a b) (Finset.Icc c e) Y

/-- The exact finite original nested-Icc quarter-dyadic TypeII
ledger. Per-cut analytic saving is an EXPLICIT premise; NO assumption
that a whole-cell estimate automatically transfers to cuts and no
source family cardinality silently hidden. -/
theorem parity_original_TypeII_quarter_Icc_dyadic_loss_ledger434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (hL : 0≤L)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (a b c e Y : ℕ) (ha : 0<a) (hc : 0<c)
    (alpha beta : ℕ → ℂ) (M : ℝ) (hM : 0≤M)
    (hEach : ∀ scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
        (parityOriginalTypeIIPhysicalPairs434
          (Finset.Icc a b) (Finset.Icc c e) Y)).filter
        (parityOriginalTypeIIQuarterProductGate434 L),
      ‖parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
        (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
        (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
        alpha beta Y‖ ≤ M) :
    ‖parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
      (Finset.Icc a b) (Finset.Icc c e) alpha beta Y‖ ≤
    (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ)*M := by
  classical
  rw [parity_original_TypeII_positive_Icc_triple_eq_quarter_nested_cuts434
    d L Psi hL hPsi a b c e Y ha hc alpha beta]
  let T := (parityOriginalActualTypeIIDyadicPairScales434
    (parityOriginalTypeIIPhysicalPairs434
      (Finset.Icc a b) (Finset.Icc c e) Y)).filter
        (parityOriginalTypeIIQuarterProductGate434 L)
  have hCard := parity_original_actual_quarter_Icc_dyadic_card_le_log_sq434
    a b c e Y L
  calc
    _ ≤ ∑ scale ∈ T,
      ‖parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
        (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
        (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
        alpha beta Y‖ := norm_sum_le _ _
    _ ≤ ∑ scale ∈ T, M := Finset.sum_le_sum (by
      intro scale hs
      exact hEach scale hs)
    _ = (T.card:ℝ)*M := by simp
    _ ≤ (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ)*M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact_mod_cast hCard
end Green64Analytic.Parity

end

end

/-! ## QuarterSource3DDerivative -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- Actual original full 3D log Fourier kernel has same bound
‖D^J F_(L,k,Z)(t)‖ ≤ K_J L^[5(K0+90)(J+1)] on fixed log cube
under fully corrected B' geometric Ybox=ceil6UV and physical
Z≤24Cbox expL L^(K0+88), with Cbox fixed, L≥6Cbox.
This is a new SOURCE-CORRECT derivative proof, not assumed
uniform Fourier decay or reuse of old Y0 cap. -/
theorem parity_original_historical_box_full_3d_source_derivative_quarter434
    (L U E V Z K0 Cbox A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤4*U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 → -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J : ℕ)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 32*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
       (J.factorial:ℝ)*A≤L)
    (t : EuclideanSpace ℝ (Fin 3))
    (h0 : -(Real.log A)≤t 0 ∧ t 0≤Real.log A)
    (h1 : -(Real.log A)≤t 1 ∧ t 1≤Real.log A)
    (h2 : -(Real.log A)≤t 2 ∧ t 2≤Real.log A) :
    ‖iteratedFDeriv ℝ J
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport : EuclideanSpace ℝ (Fin 3) → ℂ) t‖ ≤
      parityOriginalHistoricalFull3DFixedDerivativeK434 A buf hBufSmooth
        hBufSupport J * L^((5*(K0+90))*((J:ℝ)+1)) := by
  let F := parityOriginalHistoricalActualFive3DFactors434 L U E V Z hL k buf
  let M := parityOriginalHistoricalFiveFactorFixedBudget434 A buf hBufSmooth hBufSupport J
  let R := L^((K0+90)*((J:ℝ)+1))
  have hMR : 0≤M*R := by
    have hm := parity_original_historical_five_factor_fixed_budget_ge_one434 A buf hBufSmooth hBufSupport J
    have hr0 := parity_original_3d_source_log_power_ge_one434 L (K0+1)
      hL (by linarith : 0≤K0+1) J
    have hr : 1≤R := by
      simpa only [R,show (K0+1)+89=K0+90 by ring] using hr0
    exact mul_nonneg (by linarith) (by linarith)
  have hFive := parity_original_3d_five_factor_derivative_le434
    F (parity_original_historical_actual_five_factors_smooth434
      L U E V Z hL k buf hBufSmooth)
    J t (M*R) hMR
    (parity_original_historical_box_five_factors_all_order_polylog_quarter434
      L U E V Z K0 Cbox A hL hK0 k hk hU hV hUV hE hZ
      hCbox hLargeC hZupper hA
      buf hBufSmooth hBufSupport J hLargeE hLargeN t h0 h1 h2)
  have hEq := parity_original_historical_actual_five_product_eq_schwartz434
    L U E V Z hL k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  have hfun : (fun x : EuclideanSpace ℝ (Fin 3) => ∏i : Fin 5,F i x) =
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport : EuclideanSpace ℝ (Fin 3) → ℂ) := by
    funext x
    exact hEq x
  rw [hfun] at hFive
  have hPower : R^5=L^((5*(K0+90))*((J:ℝ)+1)) := by
    dsimp [R]
    rw [←Real.rpow_natCast (L^((K0+90)*((J:ℝ)+1))) 5]
    rw [←Real.rpow_mul (by linarith : 0≤L)]
    congr 1
    ring
  calc
    _ ≤ parityOriginal3DFiveFactorDerivativeCombinatorial434 J * (M*R)^5 := hFive
    _ = parityOriginalHistoricalFull3DFixedDerivativeK434 A buf
          hBufSmooth hBufSupport J * L^((5*(K0+90))*((J:ℝ)+1)) := by
        unfold parityOriginalHistoricalFull3DFixedDerivativeK434
        rw [mul_pow,hPower]
        ring
end Green64Analytic.Parity

end

end

/-! ## Quarter3DSeminorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Same fixed original 3D Schwartz seminorm budget at
CORRECT Ybox cap-free Parity4.7 physical z-height; all all-order
source Fréchet derivatives and exact Euclidean log support
under genuine 24Cbox factor, no old Y0. -/
theorem parity_original_historical_box_full_3d_source_seminorm_quarter434
    (L U E V Z K0 Cbox A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤4*U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J p : ℕ)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 32*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
       (J.factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    (SchwartzMap.seminorm ℂ p J)
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) ≤
      R^p * parityOriginalHistoricalFull3DFixedDerivativeK434
        A buf hBufSmooth hBufSupport J *
        L^((5*(K0+90))*((J:ℝ)+1)) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  let C := parityOriginalHistoricalFull3DFixedDerivativeK434
    A buf hBufSmooth hBufSupport J
  let P := L^((5*(K0+90))*((J:ℝ)+1))
  have hM1 := parity_original_historical_five_factor_fixed_budget_ge_one434
    A buf hBufSmooth hBufSupport J
  have hCoeff : 0≤C := mul_nonneg
    (parity_original_3d_five_factor_combinatorial_nonneg434 J)
    (pow_nonneg (by linarith : 0≤parityOriginalHistoricalFiveFactorFixedBudget434
      A buf hBufSmooth hBufSupport J) 5)
  have hP : 0≤P := Real.rpow_nonneg (by linarith : 0≤L) _
  have hRpow : 0≤R^p := pow_nonneg (by linarith) _
  have hM : 0≤R^p*C*P := by positivity
  have hTSupport := parity_original_historical_actual_source_schwartz_tsupport_cube434
    L U E V Z A hL k buf hBufSmooth hBufSupport
  apply SchwartzMap.seminorm_le_bound ℂ p J f hM
  intro t
  by_cases ht : t∈parityOriginalHistoricalEuclideanFixedLogCube434 A
  · have hc := parity_original_historical_fixed_3d_cube_coordinates434 A t ht
    have hD := parity_original_historical_box_full_3d_source_derivative_quarter434
      L U E V Z K0 Cbox A hL hK0 k hk hU hV hUV hE hZ
      hCbox hLargeC hZupper
      hA buf hBufSmooth hBufSupport J hLargeE hLargeN t
      (hc 0) (hc 1) (hc 2)
    have hNorm : ‖t‖^p≤R^p :=
      pow_le_pow_left₀ (norm_nonneg t) (hCubeR t ht) p
    calc
      ‖t‖^p * ‖iteratedFDeriv ℝ J (f : EuclideanSpace ℝ (Fin 3) → ℂ) t‖ ≤
        R^p * ‖iteratedFDeriv ℝ J (f : EuclideanSpace ℝ (Fin 3) → ℂ) t‖ :=
          mul_le_mul_of_nonneg_right hNorm (norm_nonneg _)
      _ ≤ R^p*(C*P) := mul_le_mul_of_nonneg_left hD hRpow
      _ = R^p*C*P := by ring
  · have hnot : t∉tsupport (f : EuclideanSpace ℝ (Fin 3) → ℂ) :=
      fun h => ht (hTSupport h)
    have hNo : (iteratedFDeriv ℝ J
        (f : EuclideanSpace ℝ (Fin 3) → ℂ)) t = 0 := by
      have hs : t∉Function.support (iteratedFDeriv ℝ J
          (f : EuclideanSpace ℝ (Fin 3) → ℂ)) :=
        fun h => hnot (support_iteratedFDeriv_subset J h)
      exact not_not.mp hs
    rw [hNo,norm_zero,mul_zero]
    exact hM
end Green64Analytic.Parity

end

end

/-! ## QuarterFiniteSeminorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- Source-correct original cap-free B'(4.7) full 3D Schwartz
FINITE seminorm B_H source budget for arbitrary H on
true Ybox physical Z≤24Cbox expL L^(K0+88), with exactly
original exponent 5(K0+90)(H+P+1) and fixed reference K_J.
Proof invokes rederived true source seminorm, not old cap Y0. -/
theorem parity_original_historical_box_3d_finite_seminorm_budget_quarter434
    (L U E V Z K0 Cbox A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤4*U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J N : ℕ) (hNJ : N≤J)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 32*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
       (J.factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    parityOriginal3DSourceFiniteSeminormBudget434 N
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) ≤
      parityOriginalHistoricalFull3DSourceSeminormFixedK434 A R buf
        hBufSmooth hBufSupport J *
        L^((5*(K0+90))*((J:ℝ)+1)) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf (-Real.log A) (Real.log A)
      hBufSmooth hBufSupport
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let C : ℝ := parityOriginal3DSourceGeometricConstant434
  let K : ℕ → ℝ := fun j =>
    parityOriginalHistoricalFull3DFixedDerivativeK434 A buf hBufSmooth hBufSupport j
  let M : ℝ := ∑j∈Finset.range (J+1),K j
  let Rpow : ℝ := L^((5*(K0+90))*((J:ℝ)+1))
  let D : ℝ := (2:ℝ)^J*C*(1+R^P)*M
  have hK (j : ℕ) : 0≤K j := by
    dsimp [K,parityOriginalHistoricalFull3DFixedDerivativeK434]
    apply mul_nonneg (parity_original_3d_five_factor_combinatorial_nonneg434 j)
    apply pow_nonneg
    have hge := parity_original_historical_five_factor_fixed_budget_ge_one434
      A buf hBufSmooth hBufSupport j
    linarith
  have hM : 0≤M := Finset.sum_nonneg (fun i hi=>hK i)
  have hC : 0≤C := parity_original_3d_source_geometric_constant_nonneg434
  have hRpos : 0≤R^P := pow_nonneg (by linarith) _
  have hRpow : 0≤Rpow := Real.rpow_nonneg (by linarith) _
  have hD : 0≤D := by dsimp [D]; positivity
  have hNthreshold (j : ℕ) (hj : j≤J) :
      32*A^2*(j.factorial:ℝ)*(2:ℝ)^j + (j.factorial:ℝ)*A ≤ L := by
    have hf : (j.factorial:ℝ) ≤ (J.factorial:ℝ) := by
      exact_mod_cast Nat.factorial_le hj
    have hp : (2:ℝ)^j ≤ (2:ℝ)^J := pow_le_pow_right₀ (by norm_num) hj
    have hprod : (j.factorial:ℝ)*(2:ℝ)^j ≤
        (J.factorial:ℝ)*(2:ℝ)^J :=
      mul_le_mul hf hp (by positivity) (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hprod (by positivity : 0≤32*A^2)
    have hlast := mul_le_mul_of_nonneg_right hf hA.le
    nlinarith [hmul,hlast,hLargeN]
  have h0 (j : ℕ) (hj : j≤J) :
      (SchwartzMap.seminorm ℂ 0 j) f ≤ K j * Rpow := by
    have hLE := parity_original_eta_e_threshold_mono434
      A hA.le J j hj L hLargeE
    have hLN := hNthreshold j hj
    have hs := parity_original_historical_box_full_3d_source_seminorm_quarter434
      L U E V Z K0 Cbox A hL hK0 k hk hU hV hUV hE hZ
      hCbox hLargeC hZupper hA
      buf hBufSmooth hBufSupport j 0 hLE hLN R hR hCubeR
    have hjReal : (j:ℝ) ≤ (J:ℝ) := by exact_mod_cast hj
    have hExp : (5*(K0+90))*((j:ℝ)+1) ≤ (5*(K0+90))*((J:ℝ)+1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤L) hExp
    have hm : 0≤K j := hK j
    calc
      _ ≤ R^0*K j*L^((5*(K0+90))*((j:ℝ)+1)) := hs
      _ = K j*L^((5*(K0+90))*((j:ℝ)+1)) := by ring
      _ ≤ K j*Rpow := mul_le_mul_of_nonneg_left hp hm
  have hPbound (j : ℕ) (hj : j≤J) :
      (SchwartzMap.seminorm ℂ P j) f ≤ R^P*K j*Rpow := by
    have hLE := parity_original_eta_e_threshold_mono434
      A hA.le J j hj L hLargeE
    have hLN := hNthreshold j hj
    have hs := parity_original_historical_box_full_3d_source_seminorm_quarter434
      L U E V Z K0 Cbox A hL hK0 k hk hU hV hUV hE hZ
      hCbox hLargeC hZupper hA
      buf hBufSmooth hBufSupport j P hLE hLN R hR hCubeR
    have hjReal : (j:ℝ) ≤ (J:ℝ) := by exact_mod_cast hj
    have hExp : (5*(K0+90))*((j:ℝ)+1) ≤ (5*(K0+90))*((J:ℝ)+1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤L) hExp
    calc
      _ ≤ R^P*K j*L^((5*(K0+90))*((j:ℝ)+1)) := hs
      _ ≤ R^P*K j*Rpow := by
        have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg hRpos (hK j))
        exact hh
  have hSum :
      (∑j∈Finset.range (N+1),
        ((SchwartzMap.seminorm ℂ 0 j) f +
         (SchwartzMap.seminorm ℂ P j) f)) ≤
      (1+R^P)*M*Rpow := by
    have hs :
      (∑j∈Finset.range (N+1),
        ((SchwartzMap.seminorm ℂ 0 j) f +
         (SchwartzMap.seminorm ℂ P j) f)) ≤
      ∑j∈Finset.range (N+1), (1+R^P)*K j*Rpow := by
      apply Finset.sum_le_sum
      intro j hj
      have hjJ : j≤J := Nat.le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hNJ
      have hh := add_le_add (h0 j hjJ) (hPbound j hjJ)
      convert hh using 1 <;> ring
    have hSubset : (Finset.range (N+1) : Finset ℕ)⊆Finset.range (J+1) :=
      Finset.range_mono (Nat.succ_le_succ hNJ)
    have hSub : (∑j∈Finset.range (N+1),K j)≤M :=
      Finset.sum_le_sum_of_subset_of_nonneg hSubset
        (fun j hj hnot=>hK j)
    calc
      _ ≤ ∑j∈Finset.range (N+1),(1+R^P)*K j*Rpow := hs
      _ = (1+R^P)*(∑j∈Finset.range (N+1),K j)*Rpow := by
        rw [Finset.mul_sum,Finset.sum_mul]
      _ ≤ (1+R^P)*M*Rpow := by
        have hcoef : 0≤1+R^P := by linarith
        have hm := mul_le_mul_of_nonneg_left hSub hcoef
        exact mul_le_mul_of_nonneg_right hm hRpow
  have hPow : (2:ℝ)^N≤(2:ℝ)^J := pow_le_pow_right₀ (by norm_num) hNJ
  have hFactor : 0≤C*((1+R^P)*M*Rpow) := by positivity
  change (2:ℝ)^N * C *
      (∑j∈Finset.range (N+1),
        ((SchwartzMap.seminorm ℂ 0 j) f+
         (SchwartzMap.seminorm ℂ P j) f)) ≤ D*Rpow
  calc
    _ ≤ (2:ℝ)^N*C*((1+R^P)*M*Rpow) :=
      mul_le_mul_of_nonneg_left hSum
        (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) _) hC)
    _ ≤ (2:ℝ)^J*C*((1+R^P)*M*Rpow) := by
      have h2 : (2:ℝ)^N*C ≤ (2:ℝ)^J*C :=
        mul_le_mul_of_nonneg_right hPow hC
      have hQ : 0≤(1+R^P)*M*Rpow := by positivity
      exact mul_le_mul_of_nonneg_right h2 hQ
    _ = D*Rpow := by dsimp [D]; ring
end Green64Analytic.Parity

end

end

