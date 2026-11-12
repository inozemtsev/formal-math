module

public import Green64.Library.Sieve.Foundations.Part041
public import Green64.Library.Sieve.Foundations.Part042
public import Green64.Library.Sieve.Foundations.Part040
public import Green64.Library.Sieve.Foundations.Part031
public import Green64.Library.Sieve.Foundations.Part038
public import Green64.Library.Sieve.Foundations.Part032
public import Green64.Library.Sieve.Foundations.Part007
public import Green64.Library.Sieve.Foundations.Part012

@[expose] public section

/-!
# Sieve / Foundations / Part043

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ZeroEtaGhostDoubleFullMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- The two legitimate positive Fourier-tail ghosts from zero-eta
physical pairs cost at most TWICE the original unrestricted positive
source absolute coefficient mass. The eta-active source is an actual
subset of full physical events BEFORE Fourier truncation, so the
inclusion may be used for |W| but NOT for complex signed Fourier norms.
No source e-Pfree cut, no fake #characters or #e/n multiplicities. -/
theorem parity_original_actual_true_psi_zero_eta_spectral_ghost_double_full_mass434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (ZS : Finset ℕ)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U)
    (hZpos : ∀Z∈ZS,0<Z)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (H : ℕ) (T : ℝ) (hT : 0<T) :
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Full := parityOriginalActualTruePsiGlobalPhysicalBall434
      d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
      buf a b T hSmooth hSupport
    let Active := parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
      d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
      buf a b T hSmooth hSupport
    let FullMass := ∑k∈KS,∑Z∈ZS,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K J k
          let W : (ℕ×ℕ) → ℂ := fun q =>
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
          let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hL U E V (Z:ℝ) k buf a b hSmooth hSupport
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
            (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
        else 0
    let ActiveMass := ∑k∈KS,∑Z∈ZS,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
            d L E V hL band slot delta Y e m K J k
          let W : (ℕ×ℕ) → ℂ := fun q =>
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
          let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hL U E V (Z:ℝ) k buf a b hSmooth hSupport
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
            (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
        else 0
    ‖Full-Active‖ ≤ 2*FullMass := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Src := parityOriginalActualTruePsiGlobalPhysicalSource434
    d L E V hL band slot delta freq rho alpha signed Y K KS ZS
  let Full := parityOriginalActualTruePsiGlobalPhysicalBall434
    d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
    buf a b T hSmooth hSupport
  let Active := parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
    d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
    buf a b T hSmooth hSupport
  let FullMass : ℝ := ∑k∈KS,∑Z∈ZS,
    ∑e∈EF,∑m∈K,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
          d L band slot delta Y e m K J k
        let W : (ℕ×ℕ) → ℂ := fun q =>
          parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
        let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V (Z:ℝ) k buf a b hSmooth hSupport
        parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
      else 0
  let ActiveMass : ℝ := ∑k∈KS,∑Z∈ZS,
    ∑e∈EF,∑m∈K,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
          d L E V hL band slot delta Y e m K J k
        let W : (ℕ×ℕ) → ℂ := fun q =>
          parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
        let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V (Z:ℝ) k buf a b hSmooth hSupport
        parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
      else 0

  have hOld := parity_original_actual_true_psi_zero_eta_spectral_ghost_two_paid434
    d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
    hU hE hV hDyad hZpos buf a b hSmooth hSupport hOne4 H T hT
  dsimp only at hOld ⊢
  change ‖Full-Active‖≤FullMass+ActiveMass at hOld
  change ‖Full-Active‖≤2*FullMass
  have hSub : ActiveMass ≤ FullMass := by
    dsimp only [ActiveMass,FullMass]
    apply Finset.sum_le_sum
    intro k hk
    apply Finset.sum_le_sum
    intro Z hz
    apply Finset.sum_le_sum
    intro e he
    apply Finset.sum_le_sum
    intro m hm
    by_cases hkm : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
    · simp only [hkm,ite_true]
      let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K J k
      let W : (ℕ×ℕ) → ℂ := fun q =>
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V (Z:ℝ) k buf a b hSmooth hSupport
      have hcell := parity_original_actual_3d_eta_filtered_moment_tail_le_full434
        S (fun q : ℕ×ℕ =>
          parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 ≠ 0)
        W H f T hT
      simpa only [parityOriginalActualTruePsiEtaActivePhysicalEvents434,
        S,W,f] using hcell
    · simp [hkm]
  linarith
end Green64Analytic.Parity

end

end

/-! ## EtaActiveFullBallNormGhost -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The true original C∞ ψ and η-active physical Fourier ball is
bounded by the complete physical source ball plus TWO paid nonnegative
Fourier-tail ghost masses. This is the only valid direction of a
complex-source-subset transfer: the source η=0 event is removed before
truncation, and the norm triangle is applied AFTER the complete
signed source and character projector, never pointwise in χ.
All original e,n,m,m',z multiplicities, W1,H0,Q/P,ε and ψ stay literal.
This is NOT yet the unrestricted Parity(4.17) correlation theorem. -/
theorem parity_original_actual_true_psi_eta_ball_norm_le_full_plus_two_ghost434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (ZS : Finset ℕ)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U)
    (hZpos : ∀Z∈ZS,0<Z)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (H : ℕ) (T : ℝ) (hT : 0<T) :
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Full := parityOriginalActualTruePsiGlobalPhysicalBall434
      d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
      buf a b T hSmooth hSupport
    let Active := parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
      d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
      buf a b T hSmooth hSupport
    let FullMass := ∑k∈KS,∑Z∈ZS,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K J k
          let W : (ℕ×ℕ) → ℂ := fun q =>
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
          let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hL U E V (Z:ℝ) k buf a b hSmooth hSupport
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
            (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
        else 0
    let ActiveMass := ∑k∈KS,∑Z∈ZS,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
            d L E V hL band slot delta Y e m K J k
          let W : (ℕ×ℕ) → ℂ := fun q =>
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
          let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hL U E V (Z:ℝ) k buf a b hSmooth hSupport
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
            (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
        else 0
    ‖Active‖ ≤ ‖Full‖ + 2*FullMass := by
  have hOld := parity_original_actual_true_psi_zero_eta_spectral_ghost_double_full_mass434
    d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
    hU hE hV hDyad hZpos buf a b hSmooth hSupport hOne4 H T hT
  have hTransfer (Full Active : ℂ) (Mass : ℝ)
      (hBound : ‖Full-Active‖ ≤ 2*Mass) :
      ‖Active‖ ≤ ‖Full‖ + 2*Mass := by
    calc
      ‖Active‖ = ‖(Active-Full)+Full‖ := by congr 1 <;> ring
      _ ≤ ‖Active-Full‖ + ‖Full‖ := norm_add_le _ _
      _ = ‖Full-Active‖ + ‖Full‖ := by rw [norm_sub_rev]
      _ ≤ 2*Mass + ‖Full‖ := add_le_add_left hBound _
      _ = ‖Full‖ + 2*Mass := by ring
  dsimp only at hOld ⊢
  exact hTransfer _ _ _ hOld
end Green64Analytic.Parity

end

end

/-! ## CauchyFullPsiTwoGhost -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Full literal original Parity (4.10) cap-free B-prime Cauchy square
is bounded by the genuine FULL smooth ψ post-Cauchy physical Fourier
ball, plus the source positive diagonal, the already paid η-active
Fourier high-frequency tail, and TWO nonnegative zero-η spectral
ghosts. The source η-filter is never dropped for a complex signed
subset without paying these errors. All natural e including odd
P-bad e, original h=-2 Q/P/H0/W1/epsilon and true physical k/Z
remain inside the original B-prime Cauchy source. This is NOT yet
an unconditional Parity (4.2) bound, nor a full source↔Eq4.17 audit. -/
theorem parity_eventually_original_capfree_Bprime_Cauchy_full_psi_two_ghost_precursor434
    (K0 Cbox A R : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
      ∀ (hL : 32≤L) (U V E : ℝ),
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
      E=U*L^(-K0) →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖alpha m‖≤Acoef) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      ∀ (Dgoal : ℝ), 0≤Dgoal →
      let hLw : 8≤L := by linarith
      let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
      let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
      let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
      let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
      let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      let d := sourceOriginalLiteralDepth 20 L
      let Y := Nat.ceil (6*U*V)
      let EF := parityOriginalHistoricalFullOddEEnvelope434 E
      let Nfull := parityOriginalHistoricalFullNEnvelope434 V
      let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
        d L E V hLw band slot delta Y K
      let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
        (parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Y K)
      let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
        d L E band slot delta freq rho K J alpha beta signed
      let Wout := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          d L E band slot delta freq rho e*beta n‖^2
      let FullMass := ∑k∈KS,∑Z∈ZS,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K Nfull k
          let W : (ℕ×ℕ) → ℂ := fun q =>
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
          let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hLw U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
            (parityOriginal3DSourceMomentFiniteBudget434 1 f/T^1)
        else 0
      ‖Bp‖^2 ≤ Wout *
        (2*Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+344) +
         ‖parityOriginalActualTruePsiGlobalPhysicalBall434
           d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
           buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ +
         2*FullMass +
         8*C1*Acoef^2*Real.exp L*L^(-Dgoal)) := by
  have hOld := parity_eventually_original_capfree_Bprime_Cauchy_true_psi_ball_precursor434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  filter_upwards [hOld] with L hOldL
  refine ⟨hOldL.1,hOldL.2.1,?_⟩
  intro hL U V E hU hV hUV hUVhi hE band slot delta freq
    rho K J alpha beta signed Acoef hAcoef hAlpha hDyad hJ Dgoal hD
  classical
  let hLw : 8≤L := by linarith
  let d := sourceOriginalLiteralDepth 20 L
  let Y := Nat.ceil (6*U*V)
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let Nfull := parityOriginalHistoricalFullNEnvelope434 V
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K)
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
  let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
  let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
    d L E band slot delta freq rho K J alpha beta signed
  let Wout := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
    d L E band slot delta,
    ∑n∈J,‖parityOriginalHistoricalWindowAE434
      d L E band slot delta freq rho e*beta n‖^2
  let Active := parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
    d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
    buf (-Real.log A) (Real.log A) T hSmooth hSupport
  let Full := parityOriginalActualTruePsiGlobalPhysicalBall434
    d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
    buf (-Real.log A) (Real.log A) T hSmooth hSupport
  let FullMass := ∑k∈KS,∑Z∈ZS,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K Nfull k
          let W : (ℕ×ℕ) → ℂ := fun q =>
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
          let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hLw U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
            (parityOriginal3DSourceMomentFiniteBudget434 1 f/T^1)
        else 0
  have hEpos : 0<E := by rw [hE]; positivity
  have hTpos : 0<T := by
    dsimp [T]
    exact Real.rpow_pos_of_pos (by linarith : 0<L) _
  have hClosed : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U := by
    intro mp hmp
    exact ⟨(hDyad mp hmp).1,(hDyad mp hmp).2.le⟩
  have hZpos : ∀Z∈ZS,0<Z := by
    intro Z hz
    have hh := parity_original_full_odd_true_smooth_neighbor_Z_box_window434
      d L U V E K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
      band slot delta K hDyad Z hz
    have hProd : 0 < (Real.exp L/64)*L^K0 := by
      exact mul_pos (div_pos (Real.exp_pos L) (by norm_num))
        (Real.rpow_pos_of_pos (by linarith : 0<L) _)
    have hzReal : (0:ℝ)<(Z:ℝ) := hProd.trans hh.1
    exact_mod_cast hzReal
  have hNorm := parity_original_actual_true_psi_eta_ball_norm_le_full_plus_two_ghost434
    d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
    hU hEpos hV hClosed hZpos buf (-Real.log A) (Real.log A)
    hSmooth hSupport hOne4 1 T hTpos
  have hOldBound := hOldL.2.2 hL U V E hU hV hUV hUVhi hE
    band slot delta freq rho K J alpha beta signed Acoef
    hAcoef hAlpha hDyad hJ Dgoal hD
  dsimp only at hOldBound hNorm ⊢
  change ‖Active‖ ≤ ‖Full‖ + 2*FullMass at hNorm
  change ‖Bp‖^2 ≤ Wout *
      (2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
       ‖Active‖ + 8*C1*Acoef^2*Real.exp L*L^(-Dgoal)) at hOldBound
  change ‖Bp‖^2 ≤ Wout *
      (2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
       ‖Full‖ + 2*FullMass + 8*C1*Acoef^2*Real.exp L*L^(-Dgoal))
  have hWout : 0≤Wout := by
    dsimp [Wout]
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro n hn
    positivity
  calc
    _ ≤ Wout*(2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
        ‖Active‖ + 8*C1*Acoef^2*Real.exp L*L^(-Dgoal)) := hOldBound
    _ ≤ Wout*(2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
        ‖Full‖ + 2*FullMass + 8*C1*Acoef^2*Real.exp L*L^(-Dgoal)) :=
      mul_le_mul_of_nonneg_left (by linarith [hNorm]) hWout
end Green64Analytic.Parity

end

end

/-! ## ZeroEtaGhostPowerAlgebra -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact numerical two-ghost precision transfer for Parity(4.10):
if the original complete positive ghost mass (not a signed complex
subsum) has the certified full-k-degree source bound and its ORIGINAL
Cauchy diagonal has the known shifted-divisor moment saving, then the
single polynomial 3D Fourier T=L^[X+(K0+89)+M+D] pays TWO ghosts to
order O_D(exp(L)L^-D), with explicit constant 16*C1*Acoef².
Only this last real-power arithmetic is proved here; the hypotheses
must be supplied by genuine source bounds, never arbitrary masks. -/
theorem parity_original_true_psi_two_ghost_power_absorption434
    (L K0 X M D C1 Acoef mass diag : ℝ)
    (hL : 8≤L) (hK0 : 0≤K0) (hC1 : 0≤C1)
    (hMass : mass ≤
      (C1*L^X/L^((X+(K0+89)+M)+D)) *
      (2*((((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ))*diag)))
    (hDiag : diag ≤ Acoef^2*Real.exp L*L^M) :
    2*mass ≤ 16*C1*Acoef^2*Real.exp L*L^(-D) := by
  have hNumeric := parity_original_historical_ungated_full_odd_global_tail_power_numeric434
    L K0 X M D C1 Acoef hL hK0 hC1
  have hPositive : 0≤C1*L^X/L^((X+(K0+89)+M)+D) := by positivity
  have hDegree : (0:ℝ)≤(((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ)) := by positivity
  have hReduce :
      (C1*L^X/L^((X+(K0+89)+M)+D)) *
        ((((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ))*diag) ≤
      (C1*L^X/L^((X+(K0+89)+M)+D)) *
        ((((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ))*
          (Acoef^2*Real.exp L*L^M)) := by
    apply mul_le_mul_of_nonneg_left _ hPositive
    exact mul_le_mul_of_nonneg_left hDiag hDegree
  calc
    2*mass ≤ 2*((C1*L^X/L^((X+(K0+89)+M)+D)) *
      (2*((((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ))*diag))) :=
        mul_le_mul_of_nonneg_left hMass (by norm_num)
    _ = 4*((C1*L^X/L^((X+(K0+89)+M)+D)) *
      ((((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ))*diag)) := by ring
    _ ≤ 4*((C1*L^X/L^((X+(K0+89)+M)+D)) *
      ((((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ))*
        (Acoef^2*Real.exp L*L^M))) :=
        mul_le_mul_of_nonneg_left hReduce (by norm_num)
    _ ≤ 4*(4*C1*Acoef^2*Real.exp L*L^(-D)) :=
        mul_le_mul_of_nonneg_left hNumeric (by norm_num)
    _ = 16*C1*Acoef^2*Real.exp L*L^(-D) := by ring
end Green64Analytic.Parity

end

end

/-! ## ZeroEtaTrueSourceGeometry -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 5500000

/-- Every signed nonzero k and both real smooth-psi dyadic Z values
of the ORIGINAL cap-free r0=20, h=-2 B509 source have the exact
short-k, positive-height, Fourier moment and binary-power geometry.
The hypotheses are those on the true physical source m∈[U,2U)
and exp(L)≤UV≤Cbox exp(L), not artificial post-Cauchy masks.
This package can be applied independently to source ghost masses,
without unfolding large dependent finite source sums. -/
theorem parity_original_true_smooth_zero_eta_ghost_geometry434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let hLw : 8≤L := by linarith
    let Y := Nat.ceil (6*U*V)
    let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hLw band slot delta Y K
    let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V hLw band slot delta Y K)
    let N := Nat.ceil (L^(K0+89))
    (∀k∈KS,k≠0 ∧ k.natAbs≤N) ∧
    (∀Z∈ZS,0<Z ∧ (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88) ∧
      ∃j : ℕ, Z=(2:ℕ)^j) ∧
    (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U) := by
  classical
  let hLw : 8≤L := by linarith
  let Y := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K)
  let N := Nat.ceil (L^(K0+89))
  have hKShort : ∀k∈KS,k≠0 ∧ k.natAbs≤N := by
    intro k hk
    have hh := parity_original_full_odd_smoothed_k_genuine_polylog434
      d L U E V K0 hLw hU hE band slot delta Y K hDyad k hk
    exact ⟨hh.1,hh.2.2⟩
  have hZWindow : ∀Z∈ZS,0<Z ∧
      (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88) := by
    intro Z hz
    have hh := parity_original_full_odd_true_smooth_neighbor_Z_box_window434
      d L U V E K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
      band slot delta K hDyad Z hz
    have hp : (0:ℝ)<(Real.exp L/64)*L^K0 := by positivity
    have hpz : (0:ℝ)<(Z:ℝ) := hp.trans hh.1
    exact ⟨by exact_mod_cast hpz,hh.2.le⟩
  have hZPow : ∀Z∈ZS,∃j : ℕ,Z=(2:ℕ)^j := by
    intro Z hz
    exact parity_original_full_odd_smooth_neighbor_Z_is_binary_power434
      d L U V E K0 Cbox hL hK0 hCbox hU hV hUV hUVhi hE
      band slot delta K hDyad Z hz
  have hClosed : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U := by
    intro mp hm
    exact ⟨(hDyad mp hm).1,(hDyad mp hm).2.le⟩
  dsimp only
  refine ⟨hKShort,?_,hClosed⟩
  intro Z hz
  exact ⟨(hZWindow Z hz).1,(hZWindow Z hz).2,hZPow Z hz⟩
end Green64Analytic.Parity

end

end

/-! ## ZeroEtaActualSourceMassBridge -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- Exact physical SOURCE geometry specializes the verified positive
coefficient ghost-mass theorem to the *actual*, not abstract, signed k
and full smooth-psi dyadic Z carriers. Natural e,n,m,m',z source
multiplicities, both character-projected endpoints, h=-2, Q/P/H0,
W1 and epsilon are retained in the ghost mass abbreviation.
No signed-complex-subsum monotonicity is used. -/
theorem parity_original_true_psi_zero_eta_actual_source_mass_bridge434
    (d : ℕ) (L U E V K0 Cbox A R : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox) (hLargeC : 6*Cbox≤L)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (buf : ℝ → ℂ) (hA : 0<A) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hR : 1≤R)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (hLargeE : 2*A*((1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
      (2:ℝ)^(1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
      ((1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L) :
    let hLw : 8≤L := (by linarith : 8≤L)
    let Y := Nat.ceil (6*U*V)
    let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hLw band slot delta Y K
    let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V hLw band slot delta Y K)
    let N := Nat.ceil (L^(K0+89))
    let D := parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
      d L band slot delta freq rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V) alpha signed Y
    let P := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
    let X := (5*(K0+90))*(((1+P:ℕ):ℝ)+1)
    let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hSmooth hSupport 1
    ∀ (T : ℝ), 0<T →
      parityOriginalActualTruePsiGlobalPositiveGhostMass434
        d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
        buf (-Real.log A) (Real.log A) hSmooth hSupport 1 T ≤
      (C1*L^X/T)*(2*(((2*N+1:ℕ):ℝ)*D)) := by
  classical
  let hLw : 8≤L := (by linarith : 8≤L)
  let Y := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K)
  let N := Nat.ceil (L^(K0+89))
  have hGeo := parity_original_true_smooth_zero_eta_ghost_geometry434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta K hDyad
  have hKS : ∀k∈KS,k≠0 ∧ k.natAbs≤N := hGeo.1
  have hZPos : ∀Z∈ZS,0<Z := fun Z hZ => (hGeo.2.1 Z hZ).1
  have hZUpper : ∀Z∈ZS,(Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88) :=
    fun Z hZ => (hGeo.2.1 Z hZ).2.1
  have hZPower : ∀Z∈ZS,∃j : ℕ,Z=(2:ℕ)^j :=
    fun Z hZ => (hGeo.2.1 Z hZ).2.2
  have hClosed : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U := hGeo.2.2
  dsimp only at ⊢
  intro T hT
  have hMass := parity_original_true_psi_full_global_ghost_mass_le_diagonal434
    d L U E V K0 Cbox A R hLw hK0 hU hV hUV hE
    (by linarith : 0≤Cbox) hLargeC
    band slot delta freq rho K alpha signed Y KS ZS N
    hKS hZPos hZUpper hZPower hClosed
    buf hA hSmooth hSupport hOne4 1 hLargeE hLargeN hR hCube T hT
  dsimp only at hMass ⊢
  convert hMass using 1 <;> simp only [parityOriginalActualTruePsiGlobalPositiveGhostMass434, pow_one,
    Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] <;> ring
end Green64Analytic.Parity

end

end

/-! ## ZeroEtaRealSourceAbsorption -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3800000

/-- Source-true global zero-η positive Fourier ghost mass is
absorbed at arbitrary inverse-log depth, with its actual original
cap-free B' diagonal and literal k×smooth-Z carriers. Only the
already native-verified actual shifted-divisor diagonal estimate is
passed as hDiag; there is NO postulated ghost-mass estimate.
The single 3D T is fixed explicitly as a power of L before summation. -/
theorem parity_original_true_psi_zero_eta_source_mass_absorbed434
    (d : ℕ) (L U E V K0 Cbox A R : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox) (hLargeC : 6*Cbox≤L)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (buf : ℝ → ℂ) (hA : 0<A) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hR : 1≤R)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (hLargeE : 2*A*((1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
      (2:ℝ)^(1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
      ((1 + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (Acoef Dgoal : ℝ)
    (hDiag : parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
      d L band slot delta freq rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V) alpha signed
      (Nat.ceil (6*U*V)) ≤
      Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+256)) :
    let hLw : 8≤L := by linarith
    let Y := Nat.ceil (6*U*V)
    let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hLw band slot delta Y K
    let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V hLw band slot delta Y K)
    let P := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
    let X := (5*(K0+90))*(((1+P:ℕ):ℝ)+1)
    let M := 2*parityOriginalW1PolylogExponent434+256
    let T := L^((X+(K0+89)+M)+Dgoal)
    let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hSmooth hSupport 1
    2*parityOriginalActualTruePsiGlobalPositiveGhostMass434
        d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
        buf (-Real.log A) (Real.log A) hSmooth hSupport 1 T ≤
      16*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by
  classical
  let hLw : 8≤L := by linarith
  let Y := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K)
  let P := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X : ℝ := (5*(K0+90))*(((1+P:ℕ):ℝ)+1)
  let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
  let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
  let C1 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let D0 : ℝ := parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
    d L band slot delta freq rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E)
    (parityOriginalHistoricalFullNEnvelope434 V) alpha signed Y
  let FullMass : ℝ := parityOriginalActualTruePsiGlobalPositiveGhostMass434
    d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
    buf (-Real.log A) (Real.log A) hSmooth hSupport 1 T
  have hTpos : 0<T := Real.rpow_pos_of_pos (by linarith : 0<L) _
  have hSrc := parity_original_true_psi_zero_eta_actual_source_mass_bridge434
    d L U E V K0 Cbox A R hL hK0 hU hV hCbox hLargeC hUV hUVhi hE
    band slot delta freq rho K alpha signed hDyad
    buf hA hSmooth hSupport hOne4 hR hCube hLargeE hLargeN
  have hMass : FullMass≤(C1*L^X/T)*(2*(((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ)*D0)) := by
    dsimp only at hSrc
    simpa only [FullMass,T,C1,X,M,D0,Y,KS,ZS] using hSrc T hTpos
  have hC1 : 0≤C1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hFinal := parity_original_true_psi_two_ghost_power_absorption434
    L K0 X M Dgoal C1 Acoef FullMass D0 (by linarith : 8≤L) hK0 hC1
    (by simpa only [T] using hMass) (by simpa only [D0,M,Y] using hDiag)
  dsimp only at ⊢
  exact hFinal
end Green64Analytic.Parity

end

end

/-! ## ZeroEtaGlobalAnyLogModular -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The COMPLETE actual post-Cauchy full smooth-psi physical positive
zero-eta spectral ghost mass (two paid ghosts) is UNCONDITIONALLY
O_D(exp(L)L^-D) for any fixed original Parity source data. SOURCE input
is the actual bounded-k and both-neighbor Z geometry, plus the genuine
shifted divisor-moment diagonal. There are no invented e/P gates,
no signed sub-sum norm monotonicity and no arbitrary ghost premise.
The polynomial T is fixed as an explicit exponent after K0, before L.
This is not yet the global source family TypeII(4.2). -/
theorem parity_eventually_original_true_psi_zero_eta_two_ghost_any_log_modular434
    (K0 Cbox A R : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
      ∀ (hL : 32≤L) (U V E : ℝ),
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
      E=U*L^(-K0) →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
        (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖alpha m‖≤Acoef) →
      (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) →
      ∀ (Dgoal : ℝ), 0≤Dgoal →
      let d := sourceOriginalLiteralDepth 20 L
      let hLw : 8≤L := by linarith
      let Y := Nat.ceil (6*U*V)
      let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
        d L E V hLw band slot delta Y K
      let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
        (parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Y K)
      let P := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
      let X := (5*(K0+90))*(((1+P:ℕ):ℝ)+1)
      let M := 2*parityOriginalW1PolylogExponent434+256
      let T := L^((X+(K0+89)+M)+Dgoal)
      let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      2*parityOriginalActualTruePsiGlobalPositiveGhostMass434
        d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
        buf (-Real.log A) (Real.log A) hSmooth hSupport 1 T ≤
      16*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let J1 : ℕ := 1+P
  let BE : ℝ := 2*A*(J1.factorial:ℝ)
  let BN : ℝ := 8*A^2*(J1.factorial:ℝ)*(2:ℝ)^J1+(J1.factorial:ℝ)*A
  filter_upwards [parity_eventually_original_historical_ungated_box_diagonal_polylog434 Cbox hCbox,
    eventually_ge_atTop (32:ℝ),eventually_ge_atTop (6*Cbox),
    eventually_ge_atTop BE,eventually_ge_atTop BN]
    with L hDiag h32 hLargeC hBE hBN
  refine ⟨h32,hLargeC,?_⟩
  intro hL U V E hU hV hUV hUVhi hE band slot delta freq
    rho K alpha signed Acoef hAcoef hAlpha hDyad Dgoal hDgoal
  let d := sourceOriginalLiteralDepth 20 L
  have hD0 := hDiag.2 U V hU.le hV.le hUVhi band slot delta freq
    rho K (parityOriginalHistoricalFullOddEEnvelope434 E)
    (parityOriginalHistoricalFullNEnvelope434 V) alpha signed Acoef hAcoef hAlpha
  have hSrc := parity_original_true_psi_zero_eta_source_mass_absorbed434
    d L U E V K0 Cbox A R hL hK0 hU hV hCbox hLargeC
    hUV hUVhi hE band slot delta freq rho K alpha signed hDyad
    buf hA hSmooth hSupport hOne4 hR hCube
    (by simpa only [J1] using hBE)
    (by simpa only [J1] using hBN)
    Acoef Dgoal hD0
  dsimp only at ⊢ hSrc
  exact hSrc
end Green64Analytic.Parity

end

end

/-! ## CauchyFullPsiPaidGhost -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The original Parity cap-free selected-Q B' Cauchy square has its TWO
zero-η spectral ghosts UNCONDITIONALLY paid in a SINGLE polynomial
Fourier cutoff. The only remaining lowfrequency term is the literal
full physical C∞ ψ ball. The original positive diagonal, selected
Q-e/β exterior energy, r0=20, h=-2, correct all-odd e, natural
multiplicities and H0/W1/epsilon are preserved. The source-to-Eq417
comparison and full fine/Q Fourier family integration remain open. -/
theorem parity_eventually_original_capfree_Bprime_Cauchy_full_psi_paid_ghost_precursor434
    (K0 Cbox A R : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
      ∀ (hL : 32≤L) (U V E : ℝ),
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
      E=U*L^(-K0) →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖alpha m‖≤Acoef) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      ∀ (Dgoal : ℝ), 0≤Dgoal →
      let hLw : 8≤L := by linarith
      let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
      let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
      let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
      let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
      let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      let d := sourceOriginalLiteralDepth 20 L
      let Y := Nat.ceil (6*U*V)
      let EF := parityOriginalHistoricalFullOddEEnvelope434 E
      let Nfull := parityOriginalHistoricalFullNEnvelope434 V
      let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
        d L E V hLw band slot delta Y K
      let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
        (parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Y K)
      let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
        d L E band slot delta freq rho K J alpha beta signed
      let Wout := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          d L E band slot delta freq rho e*beta n‖^2
      let FullMass := ∑k∈KS,∑Z∈ZS,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K Nfull k
          let W : (ℕ×ℕ) → ℂ := fun q =>
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
          let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hLw U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
            (parityOriginal3DSourceMomentFiniteBudget434 1 f/T^1)
        else 0
      ‖Bp‖^2 ≤ Wout *
        (2*Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+344) +
         ‖parityOriginalActualTruePsiGlobalPhysicalBall434
           d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
           buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ +
         24*C1*Acoef^2*Real.exp L*L^(-Dgoal)) := by
  have hBase := parity_eventually_original_capfree_Bprime_Cauchy_full_psi_two_ghost_precursor434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  have hGhost := parity_eventually_original_true_psi_zero_eta_two_ghost_any_log_modular434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  filter_upwards [hBase,hGhost] with L hBaseL hGhostL
  refine ⟨hBaseL.1,hBaseL.2.1,?_⟩
  intro hL U V E hU hV hUV hUVhi hE band slot delta freq
    rho K J alpha beta signed Acoef hAcoef hAlpha hDyad hJ Dgoal hD
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let hLw : 8≤L := by linarith
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let Xold : ℝ := 5*(K0+90)*((P:ℝ)+2)
  let Xnew : ℝ := (5*(K0+90))*(((1+P:ℕ):ℝ)+1)
  let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
  let T : ℝ := L^((Xold+(K0+89)+M)+Dgoal)
  let C1 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Y := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K)
  let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
    d L E band slot delta freq rho K J alpha beta signed
  let Wout := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
    d L E band slot delta,
    ∑n∈J,‖parityOriginalHistoricalWindowAE434
      d L E band slot delta freq rho e*beta n‖^2
  let Full := parityOriginalActualTruePsiGlobalPhysicalBall434
    d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
    buf (-Real.log A) (Real.log A) T hSmooth hSupport
  let FullMass := parityOriginalActualTruePsiGlobalPositiveGhostMass434
    d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
    buf (-Real.log A) (Real.log A) hSmooth hSupport 1 T
  have hXeq : Xnew=Xold := by dsimp [Xnew,Xold]; push_cast; ring
  have hTeq : L^((Xnew+(K0+89)+M)+Dgoal)=T := by rw [hXeq]
  have hBaseBound := hBaseL.2.2 hL U V E hU hV hUV hUVhi hE
    band slot delta freq rho K J alpha beta signed Acoef
    hAcoef hAlpha hDyad hJ Dgoal hD
  have hGhostBound := hGhostL.2.2 hL U V E hU hV hUV hUVhi hE
    band slot delta freq rho K alpha signed Acoef hAcoef hAlpha hDyad Dgoal hD
  dsimp only at hBaseBound hGhostBound ⊢
  have hTexplicit : L^(((5*(K0+90))*(((1+P:ℕ):ℝ)+1) +
      (K0+89) + (2*parityOriginalW1PolylogExponent434+256)) + Dgoal) = T := by
    simpa only [Xnew,M] using hTeq
  rw [hTexplicit] at hGhostBound
  have hPaid : 2*FullMass≤16*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by
    change 2*FullMass≤16*C1*Acoef^2*Real.exp L*L^(-Dgoal) at hGhostBound
    exact hGhostBound
  have hOld : ‖Bp‖^2 ≤ Wout *
      (2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
       ‖Full‖+2*FullMass+8*C1*Acoef^2*Real.exp L*L^(-Dgoal)) := by
    change ‖Bp‖^2 ≤ Wout *
      (2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
       ‖Full‖+2*FullMass+8*C1*Acoef^2*Real.exp L*L^(-Dgoal)) at hBaseBound
    exact hBaseBound
  have hWout : 0≤Wout := by
    dsimp [Wout]
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro n hn
    positivity
  calc
    ‖Bp‖^2 ≤ Wout*(2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
      ‖Full‖+2*FullMass+8*C1*Acoef^2*Real.exp L*L^(-Dgoal)) := hOld
    _ ≤ Wout*(2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
      ‖Full‖+24*C1*Acoef^2*Real.exp L*L^(-Dgoal)) := by
      apply mul_le_mul_of_nonneg_left _ hWout
      linarith [hPaid]
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## CauchyActualWoutGhost -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Literal source Cauchy square, actual selected-Q/β exterior energy
Wout replaced by its native physical bound 6 E V A_gate², with
original factorial-normalized Fourier gate amplitude intact.
The full true smooth ψ Fourier ball and both fully paid positive
ghost errors remain. This is an unconditional reduction under the
specified original geometric and coefficient hypotheses, not an
estimate of the full Fourier ball or full Parity TypeII (4.2). -/
theorem parity_eventually_original_capfree_Bprime_Cauchy_actual_Wout_paid434
    (K0 Cbox A R : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
      ∀ (hL : 32≤L) (U V E : ℝ),
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
      E=U*L^(-K0) → 1≤E → 1≤V →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖alpha m‖≤Acoef) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      (∀n∈J,‖beta n‖≤1) →
      ∀ (Dgoal : ℝ), 0≤Dgoal →
      let hLw : 8≤L := by linarith
      let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
      let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
      let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
      let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
      let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      let d := sourceOriginalLiteralDepth 20 L
      let Y := Nat.ceil (6*U*V)
      let EF := parityOriginalHistoricalFullOddEEnvelope434 E
      let Nfull := parityOriginalHistoricalFullNEnvelope434 V
      let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
        d L E V hLw band slot delta Y K
      let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
        (parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Y K)
      let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
        d L E band slot delta freq rho K J alpha beta signed
      let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
        (∏ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length,
          ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
      let Wout := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          d L E band slot delta freq rho e*beta n‖^2
      let FullMass := ∑k∈KS,∑Z∈ZS,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K Nfull k
          let W : (ℕ×ℕ) → ℂ := fun q =>
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
          let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hLw U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
            (parityOriginal3DSourceMomentFiniteBudget434 1 f/T^1)
        else 0
      ‖Bp‖^2 ≤ (6*E*V*AGate^2) *
        (2*Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+344) +
         ‖parityOriginalActualTruePsiGlobalPhysicalBall434
           d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
           buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ +
         24*C1*Acoef^2*Real.exp L*L^(-Dgoal)) := by
  have hBase := parity_eventually_original_capfree_Bprime_Cauchy_full_psi_paid_ghost_precursor434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  have hWout := parity_eventually_original_actual_cauchy_Wout_EV_all_log434
  filter_upwards [hBase,hWout] with L hBaseL hWoutL
  refine ⟨hBaseL.1,hBaseL.2.1,?_⟩
  intro hL U V E hU hV hUV hUVhi hE hEone hVone band slot delta freq
    rho K J alpha beta signed Acoef hAcoef hAlpha hDyad hJ hBeta Dgoal hD
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let hLw : 8≤L := by linarith
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
  let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
  let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
  let C1 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Y := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K)
  let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
    d L E band slot delta freq rho K J alpha beta signed
  let Full := parityOriginalActualTruePsiGlobalPhysicalBall434
    d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
    buf (-Real.log A) (Real.log A) T hSmooth hSupport
  let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
    (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
  let Wout := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
    d L E band slot delta,
    ∑n∈J, ‖parityOriginalHistoricalWindowAE434
      d L E band slot delta freq rho e*beta n‖^2
  have hOld := hBaseL.2.2 hL U V E hU hV hUV hUVhi hE
    band slot delta freq rho K J alpha beta signed Acoef
    hAcoef hAlpha hDyad hJ Dgoal hD
  have hJhi : ∀n∈J,(n:ℝ)≤2*V := by
    intro n hn
    exact (hJ n hn).2
  have hW := hWoutL band slot E V hEone hVone delta freq rho J beta hJhi hBeta
  have hCone : 0≤C1 := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
    A R buf hSmooth hSupport 1 hR
  have hBracketNonneg : 0≤
      2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
      ‖Full‖+24*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by
    have hLp : 0<L := by linarith
    have hh1 : 0≤L^(2*parityOriginalW1PolylogExponent434+344) :=
      (Real.rpow_pos_of_pos hLp _).le
    have hh2 : 0≤L^(-Dgoal) := (Real.rpow_pos_of_pos hLp _).le
    positivity
  dsimp only at hOld hW ⊢
  have hOldBound : ‖Bp‖^2 ≤ Wout *
      (2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
       ‖Full‖+24*C1*Acoef^2*Real.exp L*L^(-Dgoal)) := by
    simpa only [Wout,Bp,Full,X,M,T,P,C1,d,hLw,Y,KS,ZS] using hOld
  have hWBound : Wout ≤ 6*E*V*AGate^2 := by
    simpa only [Wout,AGate,d] using hW
  calc
    ‖Bp‖^2 ≤ Wout * (2*Acoef^2*Real.exp L*
        L^(2*parityOriginalW1PolylogExponent434+344) + ‖Full‖+
        24*C1*Acoef^2*Real.exp L*L^(-Dgoal)) := hOldBound
    _ ≤ (6*E*V*AGate^2) * (2*Acoef^2*Real.exp L*
        L^(2*parityOriginalW1PolylogExponent434+344) + ‖Full‖+
        24*C1*Acoef^2*Real.exp L*L^(-Dgoal)) :=
      mul_le_mul_of_nonneg_right hWBound hBracketNonneg
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## CauchyActualFineAlphaWout -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- No independent α-size assumption: actual original Parity b629
fine PRIME or ROUGH coefficient has norm <=1 on its full actual
K-support. Its true selected Q Fourier Cauchy Bprime is bounded
with genuine Wout replaced by 6EV A_gate², positive diagonal and
both source-paid eta ghosts. Actual β remains bounded by one.
The remaining actual smooth-psi ball is NOT identified here with
unrestricted Parity4.17 and full original TypeII is still open. -/
theorem parity_eventually_original_capfree_Bprime_Cauchy_actual_b629_Wout_paid434
    (S beta gamma K0 Cbox A R : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
      ∀ (hL : 32≤L) (U V E : ℝ),
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
      E=U*L^(-K0) → 1≤E → 1≤V →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K J : Finset ℕ) (prime : Bool) (lFine uFine : ℕ)
        (betaCoeff : ℕ → ℂ) (signed : Bool),
      Real.exp (beta*L)≤(lFine:ℝ) → 2≤lFine →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      (∀n∈J,‖betaCoeff n‖≤1) →
      ∀ (Dgoal : ℝ), 0≤Dgoal →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let Acoef : ℝ := 1
      let hLw : 8≤L := by linarith
      let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
      let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
      let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
      let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
      let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      let d := sourceOriginalLiteralDepth 20 L
      let Y := Nat.ceil (6*U*V)
      let EF := parityOriginalHistoricalFullOddEEnvelope434 E
      let Nfull := parityOriginalHistoricalFullNEnvelope434 V
      let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
        d L E V hLw band slot delta Y K
      let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
        (parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Y K)
      let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
        d L E band slot delta freq rho K J alpha betaCoeff signed
      let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
        (∏ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length,
          ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
      let Wout := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          d L E band slot delta freq rho e*betaCoeff n‖^2
      let FullMass := ∑k∈KS,∑Z∈ZS,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K Nfull k
          let W : (ℕ×ℕ) → ℂ := fun q =>
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
          let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hLw U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
            (parityOriginal3DSourceMomentFiniteBudget434 1 f/T^1)
        else 0
      ‖Bp‖^2 ≤ (6*E*V*AGate^2) *
        (2*Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+344) +
         ‖parityOriginalActualTruePsiGlobalPhysicalBall434
           d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
           buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ +
         24*C1*Acoef^2*Real.exp L*L^(-Dgoal)) := by
  have hBase := parity_eventually_original_capfree_Bprime_Cauchy_actual_Wout_paid434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  have hFine := parity_eventually_original_actual_b629_K_fine_alpha_norm_one434
    S beta gamma hS hbeta hgamma
  filter_upwards [hBase,hFine] with L hBaseL hFineL
  refine ⟨hBaseL.1,hBaseL.2.1,?_⟩
  intro hL U V E hU hV hUV hUVhi hE hEone hVone band slot delta freq
    rho K J prime lFine uFine betaCoeff signed hFineLow hl hDyad hJ hBeta Dgoal hD
  classical
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  have hAlpha : ∀m∈K, ‖alpha m‖≤1 := by
    intro m hm
    exact hFineL prime lFine uFine hFineLow K m
  have hh := hBaseL.2.2 hL U V E hU hV hUV hUVhi hE hEone hVone
    band slot delta freq rho K J alpha betaCoeff signed 1
    (by norm_num) hAlpha hDyad hJ hBeta Dgoal hD
  dsimp only at hh ⊢
  exact hh
end Green64Analytic.Parity

end

end

/-! ## CauchyActualFineXScale -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The full original post-Cauchy Bprime for ACTUAL native b629
prime/rough fine alpha, beta<=1, with all odd e and real source
eta/psi/H0/W1/epsilon weights, satisfies its correct x L^-K0
Cauchy exterior prefactor with SQUARED original Q Fourier-gate
variation still visible. True physical B509 low-frequency ball
and both paid ghosts are not replaced by an unproved correlation
saving. Source UV≤Cbox x and E=U L^-K0 are used explicitly. -/
theorem parity_eventually_original_capfree_Bprime_Cauchy_actual_b629_x_K0_paid434
    (S beta gamma K0 Cbox A R : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
      ∀ (hL : 32≤L) (U V E : ℝ),
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
      E=U*L^(-K0) → 1≤E → 1≤V →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K J : Finset ℕ) (prime : Bool) (lFine uFine : ℕ)
        (betaCoeff : ℕ → ℂ) (signed : Bool),
      Real.exp (beta*L)≤(lFine:ℝ) → 2≤lFine →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      (∀n∈J,‖betaCoeff n‖≤1) →
      ∀ (Dgoal : ℝ), 0≤Dgoal →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let Acoef : ℝ := 1
      let hLw : 8≤L := by linarith
      let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
      let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
      let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
      let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
      let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      let d := sourceOriginalLiteralDepth 20 L
      let Y := Nat.ceil (6*U*V)
      let EF := parityOriginalHistoricalFullOddEEnvelope434 E
      let Nfull := parityOriginalHistoricalFullNEnvelope434 V
      let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
        d L E V hLw band slot delta Y K
      let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
        (parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Y K)
      let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
        d L E band slot delta freq rho K J alpha betaCoeff signed
      let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
        (∏ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length,
          ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
      let Wout := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          d L E band slot delta freq rho e*betaCoeff n‖^2
      let FullMass := ∑k∈KS,∑Z∈ZS,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K Nfull k
          let W : (ℕ×ℕ) → ℂ := fun q =>
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
          let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hLw U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
            (parityOriginal3DSourceMomentFiniteBudget434 1 f/T^1)
        else 0
      ‖Bp‖^2 ≤ ((6*Cbox*Real.exp L*L^(-K0))*AGate^2) *
        (2*Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+344) +
         ‖parityOriginalActualTruePsiGlobalPhysicalBall434
           d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
           buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ +
         24*C1*Acoef^2*Real.exp L*L^(-Dgoal)) := by
  have hSource := parity_eventually_original_capfree_Bprime_Cauchy_actual_b629_Wout_paid434
    S beta gamma K0 Cbox A R hS hbeta hgamma hK0 hCbox hA hR
    buf hSmooth hSupport hOne4 hCube
  filter_upwards [hSource] with L hLdata
  refine ⟨hLdata.1,hLdata.2.1,?_⟩
  intro hL U V E hU hV hUV hUVhi hE hEone hVone
    band slot delta freq rho K J prime lFine uFine betaCoeff signed
    hFineLow hl hDyad hJ hBeta Dgoal hD
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let hLw : 8≤L := by linarith
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
  let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
  let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
  let C1 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Y := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K)
  let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
    d L E band slot delta freq rho K J alpha betaCoeff signed
  let Full := parityOriginalActualTruePsiGlobalPhysicalBall434
    d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
    buf (-Real.log A) (Real.log A) T hSmooth hSupport
  let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
    (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
  have hOld := hLdata.2.2 hL U V E hU hV hUV hUVhi hE hEone hVone
    band slot delta freq rho K J prime lFine uFine betaCoeff signed
    hFineLow hl hDyad hJ hBeta Dgoal hD
  have hEV : E*V ≤ Cbox*Real.exp L*L^(-K0) := by
    rw [hE]
    calc
      (U*L^(-K0))*V = (U*V)*L^(-K0) := by ring
      _ ≤ (Cbox*Real.exp L)*L^(-K0) :=
        mul_le_mul_of_nonneg_right hUVhi
          (Real.rpow_nonneg (by linarith : 0≤L) _)
      _ = _ := by ring
  have hC1 : 0≤C1 := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
    A R buf hSmooth hSupport 1 hR
  have hBr : 0≤2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
      ‖Full‖+24*C1*Real.exp L*L^(-Dgoal) := by
    have hLp : 0<L := by linarith
    have hPow1 := (Real.rpow_pos_of_pos hLp
      (2*parityOriginalW1PolylogExponent434+344)).le
    have hPow2 := (Real.rpow_pos_of_pos hLp (-Dgoal)).le
    positivity
  have hFactor : (6*E*V*AGate^2) ≤
      ((6*Cbox*Real.exp L*L^(-K0))*AGate^2) := by
    have h := mul_le_mul_of_nonneg_right hEV (by positivity : 0≤6*AGate^2)
    nlinarith [h]
  dsimp only at hOld ⊢
  simp only [one_pow, mul_one] at hOld ⊢
  have hOldBound : ‖Bp‖^2 ≤ (6*E*V*AGate^2)*
    (2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
      ‖Full‖+24*C1*Real.exp L*L^(-Dgoal)) := by
    simpa only [Bp,Full,AGate,alpha,Y,KS,ZS,d,hLw,P,X,M,T,C1] using hOld
  calc
    ‖Bp‖^2 ≤ (6*E*V*AGate^2) *
      (2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
        ‖Full‖+24*C1*Real.exp L*L^(-Dgoal)) := hOldBound
    _ ≤ ((6*Cbox*Real.exp L*L^(-K0))*AGate^2) *
      (2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344) +
        ‖Full‖+24*C1*Real.exp L*L^(-Dgoal)) :=
      mul_le_mul_of_nonneg_right hFactor hBr
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## ActualFineCauchyEq417Combined -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- For the ACTUAL Parity(4.10) cap-free B' of one reserved Q band,
slot, delta/freq and b629 fine interval, unconditional Parity(4.17)
source cancellation is substituted into the TRUE original positive
Cauchy inequality. The same polynomial T pays the original B633
two ghosts AND original zero-eta spectral ghosts. The exterior
selected-Q/beta squared Fourier gate is KEPT: no invalid L1 to L2
reduction occurs. All parameters are selected before L:
K0, Dghost=Agoal+K0+200, Dmain=K0+315+Dghost,
Cf=X+Dmain+2CW1+30, then the Parity J,B,S.
The original all-fine/outer Fourier TypeII(4.2) remains OPEN. -/
theorem parity_eventually_original_actual_fine_Cauchy_with_eq417_paid434
    (jQ : ℕ) (Agoal C0 beta gamma K0 Cbox A R : ℝ)
    (hAgoal : 0≤Agoal)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 32≤L) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
          E=U*L^(-K0) → 1≤E → 1≤V →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → ℝ)
          (rho : ℝ), |rho|≤L^C0 →
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
        let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
        let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
        let CW : ℝ := parityOriginalW1PolylogExponent434
        let Dghost : ℝ := Agoal+K0+200
        let Dmain : ℝ := K0+315+Dghost
        let Cf : ℝ := X+Dmain+2*CW+30
        let T : ℝ := L^Cf
        let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
        let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
          d L E band slot delta freq rho K Jbeta alpha betaCoeff signed
        let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
          (∏ i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length,
            ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
        ‖Bp‖^2 ≤ ((6*Cbox*Real.exp L*L^(-K0))*AGate^2)*
          (2*Real.exp L*L^(2*CW+344) +
            Cphys*Real.exp L*L^(-Agoal) +
            24*C1*Real.exp L*L^(-Dghost)) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
  let CW : ℝ := parityOriginalW1PolylogExponent434
  let Dghost : ℝ := Agoal+K0+200
  let Dmain : ℝ := K0+315+Dghost
  let Cf : ℝ := X+Dmain+2*CW+30
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
  have hDmainPos : 0<Dmain := by dsimp [Dmain,Dghost]; linarith
  have hDgoal : 0≤Dghost := by dsimp [Dghost]; linarith
  have hPrec : Agoal+(K0+89)+K0+90≤Dmain := by
    dsimp [Dmain,Dghost]
    linarith
  have hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (Dmain+2*parityOriginalW1PolylogExponent434+30) := by
    dsimp [Cf,X,CW]
    push_cast
    ring
  have hTmatch : Cf = X+(K0+89)+(2*CW+256)+Dghost := by
    dsimp [Cf,Dmain]
    ring
  obtain ⟨J,B,S,hBS,hBall⟩ :=
    parity_eventually_original_actual_true_psi_full_physical_ball_any_log434
      jQ Agoal Dmain C0 Cf beta gamma K0 Cbox A R
      hDmainPos hPrec hCf hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  have hS : 0<S := by
    have hBn : (0:ℝ)≤B := Nat.cast_nonneg _
    linarith
  have hCauchy := parity_eventually_original_capfree_Bprime_Cauchy_actual_b629_x_K0_paid434
    S beta gamma K0 Cbox A R hS hbeta hgamma hK0 hCbox hA hR
    buf hSmooth hSupport hOne4 hCube
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hBall,hCauchy] with L hBL hCL
  refine ⟨hBL.1,hBL.2.1,hBL.2.2.1,hBL.2.2.2.1,?_⟩
  intro hL hFamily U V E hU hV hUV hUVhi hEscale hEone hVone
    band hBand slot delta freq rho hrho a b Jbeta prime lFine uFine
    betaCoeff signed hFineLow hl hu huExp hDyad hJ hBeta
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let T : ℝ := L^Cf
  let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
    d L E band slot delta freq rho K Jbeta alpha betaCoeff signed
  let Full := parityOriginalActualTruePsiGlobalPhysicalBall434
    d L U E V (by linarith : 8≤L) band slot delta freq rho alpha signed
    (Nat.ceil (6*U*V)) K
    (parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K)
    (parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K))
    buf (-Real.log A) (Real.log A) T hSmooth hSupport
  let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
    (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
  have hTC : T=L^((X+(K0+89)+(2*CW+256))+Dghost) := by
    dsimp [T]
    rw [hTmatch]
  have hB := hBL.2.2.2.2 (by linarith : 8≤L) hFamily band hBand slot
    delta freq rho U E V T signed hU (by positivity : 0<E) hV hUV hEscale
    rfl hrho prime lFine uFine a b hFineLow hl hu huExp hDyad hUVhi
  have hC := hCL.2.2 hL U V E hU hV hUV hUVhi hEscale hEone hVone
    band slot delta freq rho K Jbeta prime lFine uFine betaCoeff signed
    hFineLow hl hDyad hJ hBeta Dghost hDgoal
  dsimp only at hB hC ⊢
  rw [←hTC] at hC
  have hBallBound : ‖Full‖≤Cphys*Real.exp L*L^(-Agoal) := by
    simpa only [Full,Cphys,Cmoment,C1] using hB
  have hCauchyBound : ‖Bp‖^2 ≤
      ((6*Cbox*Real.exp L*L^(-K0))*AGate^2)*
      (2*Real.exp L*L^(2*CW+344)+‖Full‖+
         24*C1*Real.exp L*L^(-Dghost)) := by
    simpa only [Bp,AGate,Full,C1,T,Cf,X,CW,Dghost,P,alpha,K,d, one_pow, mul_one, one_mul] using hC
  have hFactorNonneg : 0≤(6*Cbox*Real.exp L*L^(-K0))*AGate^2 := by
    have hLpos : 0<L := by linarith
    dsimp only [AGate]
    positivity
  exact hCauchyBound.trans (mul_le_mul_of_nonneg_left
    (by linarith [hBallBound]) hFactorNonneg)
end Green64Analytic.Parity

end

end

/-! ## ActualCauchySquarePowerAbsorption -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- ORIGINAL Parity(4.10) final power bookkeeping, with the exact
selected-Q squared Fourier gate AGate^2 still visible. The true
positive diagonal costs Cd=2*C_W1+344; the original B633 source
ball and both paid zero-eta ghosts cost separately arbitrary-log
powers. Choosing K0>=2*A+Cd pays the Cauchy square root at the
original physical x=exp L scale, *without* dropping AGate, assuming
an L1-to-L2 Fourier inequality or inventing an analytic saving. -/
theorem parity_original_actual_cauchy_square_power_absorption434
    (L A K0 CW Dghost Cbox Cphys C1 AGate : ℝ) (Bp : ℂ)
    (hL : 1≤L) (hA : 0≤A) (hCW : 0≤CW)
    (hDghost : 0≤Dghost) (hCbox : 0≤Cbox)
    (hCphys : 0≤Cphys) (hC1 : 0≤C1)
    (hK0 : 2*A+2*CW+344≤K0)
    (hCauchy : ‖Bp‖^2 ≤
      ((6*Cbox*Real.exp L*L^(-K0))*AGate^2)*
        (2*Real.exp L*L^(2*CW+344)+
          Cphys*Real.exp L*L^(-A)+
          24*C1*Real.exp L*L^(-Dghost))) :
    ‖Bp‖^2 ≤
      (6*Cbox*(2+Cphys+24*C1))*AGate^2*
        (Real.exp L*L^(-A))^2 := by
  let Cd : ℝ := 2*CW+344
  have hCd : 0≤Cd := by dsimp [Cd]; linarith
  have hLp : 0<L := by linarith
  have hp1 : L^(Cd-K0)≤L^(-2*A) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    dsimp [Cd]; linarith
  have hp2 : L^(-A-K0)≤L^(-2*A) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    dsimp [Cd] at hCd
    linarith
  have hp3 : L^(-Dghost-K0)≤L^(-2*A) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    linarith
  have hs1 : 2*L^(Cd-K0)≤2*L^(-2*A) :=
    mul_le_mul_of_nonneg_left hp1 (by norm_num)
  have hs2 : Cphys*L^(-A-K0)≤Cphys*L^(-2*A) :=
    mul_le_mul_of_nonneg_left hp2 hCphys
  have hs3 : 24*C1*L^(-Dghost-K0)≤24*C1*L^(-2*A) :=
    mul_le_mul_of_nonneg_left hp3 (by positivity)
  have hSum :
      2*L^(Cd-K0)+Cphys*L^(-A-K0)+24*C1*L^(-Dghost-K0) ≤
      (2+Cphys+24*C1)*L^(-2*A) := by
    calc
      _ ≤ 2*L^(-2*A)+Cphys*L^(-2*A)+24*C1*L^(-2*A) :=
        add_le_add (add_le_add hs1 hs2) hs3
      _ = _ := by ring
  have hPre : 0≤(6*Cbox*AGate^2)*(Real.exp L*Real.exp L) := by positivity
  have hpow1 : L^(-K0)*L^Cd=L^(Cd-K0) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  have hpow2 : L^(-K0)*L^(-A)=L^(-A-K0) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  have hpow3 : L^(-K0)*L^(-Dghost)=L^(-Dghost-K0) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  have hpowA : L^(-A)*L^(-A)=L^(-2*A) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  calc
    ‖Bp‖^2 ≤ ((6*Cbox*Real.exp L*L^(-K0))*AGate^2)*
      (2*Real.exp L*L^Cd+Cphys*Real.exp L*L^(-A)+
        24*C1*Real.exp L*L^(-Dghost)) := by
        simpa only [Cd] using hCauchy
    _ = (6*Cbox*AGate^2)*(Real.exp L*Real.exp L)*
        (2*L^(Cd-K0)+Cphys*L^(-A-K0)+24*C1*L^(-Dghost-K0)) := by
        rw [←hpow1,←hpow2,←hpow3]
        ring
    _ ≤ (6*Cbox*AGate^2)*(Real.exp L*Real.exp L)*
        ((2+Cphys+24*C1)*L^(-2*A)) :=
          mul_le_mul_of_nonneg_left hSum hPre
    _ = (6*Cbox*(2+Cphys+24*C1))*AGate^2*
        (Real.exp L*L^(-A))^2 := by
        rw [←hpowA]
        ring

/-- The square is genuinely a complex norm square; the previous
source estimate therefore yields the correct original Cauchy root,
with the square of the real Q-Fourier gate restored as ONE AGate.
The source-dependent positive constant is kept explicit. -/
theorem parity_original_actual_cauchy_norm_power_absorption434
    (L A K0 CW Dghost Cbox Cphys C1 AGate : ℝ) (Bp : ℂ)
    (hL : 1≤L) (hA : 0≤A) (hCW : 0≤CW)
    (hDghost : 0≤Dghost) (hCbox : 0≤Cbox)
    (hCphys : 0≤Cphys) (hC1 : 0≤C1)
    (hAGate : 0≤AGate)
    (hK0 : 2*A+2*CW+344≤K0)
    (hCauchy : ‖Bp‖^2 ≤
      ((6*Cbox*Real.exp L*L^(-K0))*AGate^2)*
        (2*Real.exp L*L^(2*CW+344)+
          Cphys*Real.exp L*L^(-A)+
          24*C1*Real.exp L*L^(-Dghost))) :
    ‖Bp‖ ≤ (1+6*Cbox*(2+Cphys+24*C1))*
      AGate*Real.exp L*L^(-A) := by
  let Q : ℝ := 6*Cbox*(2+Cphys+24*C1)
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hBound := parity_original_actual_cauchy_square_power_absorption434
    L A K0 CW Dghost Cbox Cphys C1 AGate Bp
    hL hA hCW hDghost hCbox hCphys hC1 hK0 hCauchy
  change ‖Bp‖^2 ≤ Q*AGate^2*(Real.exp L*L^(-A))^2 at hBound
  have hQCoeff : Q≤(1+Q)^2 := by nlinarith [sq_nonneg Q]
  have hCoeffPos : 0≤AGate^2*(Real.exp L*L^(-A))^2 := by positivity
  have hSq : ‖Bp‖^2 ≤ ((1+Q)*AGate*Real.exp L*L^(-A))^2 := by
    calc
      _ ≤ Q*AGate^2*(Real.exp L*L^(-A))^2 := hBound
      _ ≤ (1+Q)^2*(AGate^2*(Real.exp L*L^(-A))^2) :=
        by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right hQCoeff hCoeffPos)
      _ = ((1+Q)*AGate*Real.exp L*L^(-A))^2 := by ring
  have hGoalPos : 0≤(1+Q)*AGate*Real.exp L*L^(-A) := by
    have hLp : 0<L := by linarith
    positivity
  change ‖Bp‖ ≤ (1+Q)*AGate*Real.exp L*L^(-A)
  nlinarith [norm_nonneg Bp]
end Green64Analytic.Parity

end

end

/-! ## ActualFineCauchyAGateAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- ACTUAL source-correct cap-free Parity(4.10) Bprime at a fixed
reserved Q band/slot, actual Fourier allocation and b629 fine
interval satisfies arbitrary inverse-log TypeII-size saving, with
exact original Fourier gate factor AGate retained outside the
square root. K0 is fixed before the Parity J,B,S and L, large enough
to pay the positive source diagonal and the physical signed 4.17
correlation plus both zero-eta spectral ghosts. No false L1-to-L2
Gate bound, omitted source e,n or replacement hard masks.

The external high-dimensional Q Fourier and remaining fine/β
families are NOT yet summed: this is a true original Bprime
per-allocation source estimate, not entire Parity(4.2). -/
theorem parity_eventually_original_actual_fine_Cauchy_agate_any_log434
    (jQ : ℕ) (Agoal C0 beta gamma K0 Cbox A R : ℝ)
    (hAgoal : 0≤Agoal)
    (hK0Target : 2*Agoal+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 32≤L) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
          E=U*L^(-K0) → 1≤E → 1≤V →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → ℝ)
          (rho : ℝ), |rho|≤L^C0 →
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
        let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
        let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
        let CW : ℝ := parityOriginalW1PolylogExponent434
        let Dghost : ℝ := Agoal+K0+200
        let Dmain : ℝ := K0+315+Dghost
        let Cf : ℝ := X+Dmain+2*CW+30
        let T : ℝ := L^Cf
        let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
        let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
          d L E band slot delta freq rho K Jbeta alpha betaCoeff signed
        let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
          (∏ i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length,
            ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
        ‖Bp‖ ≤
          (1+6*Cbox*(2+Cphys+24*C1))*AGate*Real.exp L*L^(-Agoal) := by
  obtain ⟨J,B,S,hBS,hCauchy⟩ :=
    parity_eventually_original_actual_fine_Cauchy_with_eq417_paid434
      jQ Agoal C0 beta gamma K0 Cbox A R
      hAgoal hbeta hgamma hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hCauchy] with L hLbound
  refine ⟨hLbound.1,hLbound.2.1,hLbound.2.2.1,hLbound.2.2.2.1,?_⟩
  intro hL hFamily U V E hU hV hUV hUVhi hEscale hEone hVone
    band hBand slot delta freq rho hrho a b Jbeta prime lFine uFine
    betaCoeff signed hFineLow hl hu huExp hDyad hJ hBeta
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
  let CW : ℝ := parityOriginalW1PolylogExponent434
  let Dghost : ℝ := Agoal+K0+200
  let Dmain : ℝ := K0+315+Dghost
  let Cf : ℝ := X+Dmain+2*CW+30
  let T : ℝ := L^Cf
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cphys := 250*Cbox*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Bp := parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
    d L E band slot delta freq rho K Jbeta alpha betaCoeff signed
  let AGate := L^parityOriginalSelectedECoefficientPolylogExponent434 *
    (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      ‖(𝓕 (sourceBufferedGate 20 (delta i)) : 𝓢(ℝ,ℂ)) (freq i)‖)
  have hOld := hLbound.2.2.2.2 hL hFamily U V E hU hV hUV hUVhi
    hEscale hEone hVone band hBand slot delta freq rho hrho
    a b Jbeta prime lFine uFine betaCoeff signed hFineLow hl hu
    huExp hDyad hJ hBeta
  have hCW : 0≤CW := parity_original_actual_W1_polylog_exponent_nonneg434
  have hDghost : 0≤Dghost := by dsimp [Dghost]; linarith
  have hC1 : 0≤C1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hC0 : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hLog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hCphys : 0≤Cphys := by
    dsimp [Cphys]
    positivity
  have hGate : 0≤AGate := by
    dsimp [AGate]
    have hLp : 0<L := by linarith
    positivity
  dsimp only at hOld ⊢
  exact parity_original_actual_cauchy_norm_power_absorption434
    L Agoal K0 CW Dghost Cbox Cphys C1 AGate Bp
    (by linarith : 1≤L) hAgoal hCW hDghost (by linarith) hCphys hC1
    hGate hK0Target hOld
end Green64Analytic.Parity

end

end

/-! ## ActualFineBprimeFullQPositive -/

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
theorem parity_eventually_original_actual_fine_Bprime_fullQ_positive_anylog434
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
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 32≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
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
    parity_eventually_original_actual_fine_Cauchy_agate_any_log434
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
    have hSingle := hRest hL hFamily0 U V E hU hV hUV hUVhi
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

/-! ## ActualFineBprimeAllSlotsFullQPositive -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Complete true ORIGINAL twenty reserved Q-slot sum of the genuine
cap-free pre-Cauchy Bprime absolute Fourier integral. For each slot,
all original 2^N Boolean allocations and its own N-dimensional cube
are integrated exactly once; labelled Q prime tuples remain inside
native selected-e/skipped-Q coefficients and are not re-counted.
This is per original b629 fine interval and fixed reserved Q band,
not original whole TypeII(4.2). The numeric slot loss is exactly 20. -/
theorem parity_eventually_original_actual_fine_Bprime_all_reserved_slots_fullQ_positive_anylog434
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
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 32≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
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
    parity_eventually_original_actual_fine_Bprime_fullQ_positive_anylog434
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

/-! ## ActualFineFamilyFullQPositive -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9500000

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
theorem parity_eventually_original_actual_b629_fine_family_fullQ_positive_anylog434
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
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 32≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
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
    parity_eventually_original_actual_fine_Bprime_all_reserved_slots_fullQ_positive_anylog434
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

/-! ## FullDyadProxyExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The literal Parity section 7.1 full-cell test minus its normalized
proxy, restricted AFTER the full cell C_j has been formed to one
arbitrary interval [l,u].  All full-cell averages use the original
logarithmic cell width L^(-S); a cut end-cell is NEVER renormalized.
The two supported tests are prime and x^gamma-rough, with exact
W=exp(sqrt L). This is a WHOLE INTERVAL source coefficient and does
not sum separate TypeII estimates over tiny proxy cells. -/
def parityOriginalActualFullDyadProxyDifference434
    (prime : Bool) (L S gamma : ℝ) (l u n : ℕ) : ℂ :=
  if n ∈ Finset.Icc l u then
    if prime then
      ((if n.Prime then (1:ℝ) else 0) -
        b627PrimeFullProxy434 (L^(-S)) (Real.exp (Real.sqrt L)) n : ℝ)
    else
      (sourceD19RoughTest ((Real.exp L)^gamma) n -
        sourceD20FullProxy (L^(-S)) (Real.exp (Real.sqrt L))
          ((Real.exp L)^gamma) n : ℝ)
  else 0

/-- Source-exact comparison to the existing native b629 fine-alpha:
what looked like a one-cell alpha is ACTUALLY the full [l,u] proxy
discrepancy, with its per-n value taken from the full C_j. -/
theorem parity_original_actual_full_dyad_proxy_eq_b629434
    (prime : Bool) (L S gamma : ℝ) (l u n : ℕ) :
    parityOriginalActualFullDyadProxyDifference434 prime L S gamma l u n =
      b629ActualFineAlpha434 prime L S gamma l u n := by
  classical
  cases prime <;>
    simp [parityOriginalActualFullDyadProxyDifference434,
      b629ActualFineAlpha434,b627PrimeFullDelta434,sourceD20FullDelta]

/-- No extra #logarithmic-cells factor is inserted into type II when
K is already the original interval [a,b].  This is the exact source
Parity(7.1) prime/rough discrepancy for the WHOLE K, still supported
on every original full cell and allowing K to cut its boundary.
Full Q Fourier saving and all 20 reserved slots are carried over
from the kernel-proved per-interval theorem.  This does not assert
arbitrary-alpha TypeII(4.2), nor the pre-Cauchy whole source join. -/
theorem parity_eventually_original_actual_full_dyad_proxy_Bprime_fullQ_all_slots_anylog434
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
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 32≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (U V E : ℝ),
          0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
          E=U*L^(-K0) → 1≤E → 1≤V →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (rho : ℝ), |rho|≤L^C0 →
        ∀ (a b : ℕ) (Jbeta : Finset ℕ) (prime : Bool)
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
        (∑slot : Fin 20,
          ∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → Bool,
            ∫freq in parityOriginalActualFullQFrequencyCube434 L,
              ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                d L E band slot delta freq rho K Jbeta alpha betaCoeff signed‖) ≤
          20*Csource*Real.exp L*L^(-goal) := by
  obtain ⟨J,B,S,hBS,hOld⟩ :=
    parity_eventually_original_actual_fine_Bprime_all_reserved_slots_fullQ_positive_anylog434
      jQ goal target C0 beta gamma K0 Cbox A R
      hTarget hK0Target hPrecision hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hOne4 hCube
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hOld] with L hL
  rcases hL with ⟨h32,h6,hFam,hReserved,hRest⟩
  refine ⟨h32,h6,hFam,hReserved,?_⟩
  intro hL hFamily U V E hU hV hUV hUVhi hEscale hEone hVone
    band hBand rho hrho a b Jbeta prime betaCoeff signed
    hFineLow hTwo hUpper hExp hDyad hJ hBeta
  have h := hRest hL hFamily U V E hU hV hUV hUVhi
    hEscale hEone hVone band hBand rho hrho a b Jbeta prime
    a b betaCoeff signed hFineLow hTwo hUpper hExp hDyad hJ hBeta
  have hAlpha :
      parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b =
      b629ActualFineAlpha434 prime L S gamma a b := by
    funext n
    exact parity_original_actual_full_dyad_proxy_eq_b629434 prime L S gamma a b n
  rw [hAlpha]
  exact h
end Green64Analytic.Parity

end

end

/-! ## FullDyadProxyDiscrepancy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationMellin Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- The WHOLE INTERVAL source Parity section 7.1 test-minus-full-cell
proxy, not a single tiny cell, satisfies the exact E4.1 character
and real-frequency discrepancy condition (including q=0) for any
original interval [l,u] in one dyad. It inherits the native b629
proof with S>2B, chosen AFTER required discrepancy accuracy B.
Consequently no L^S count of tiny cells is needed to apply the
specialized original TypeII source saving to this full-K coefficient.
This is NOT a universal statement for arbitrary alpha. -/
theorem parity_eventually_original_full_dyad_proxy_discrepancy434
    (B S beta gamma : ℝ) (hB : 0<B) (hS : 2*B<S)
    (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, ∀ (prime : Bool) (l u : ℕ),
      2≤l → u≤2*l → Real.exp (beta*L)≤(l:ℝ) →
      (u:ℝ)≤Real.exp (2*L) →
      SourceAlphaDiscrepancy L B (Real.exp L)
        (parityOriginalActualFullDyadProxyDifference434 prime L S gamma l u) := by
  filter_upwards [b629_actual_fine_source_discrepancy434
    B S beta gamma hB hS hbeta hgamma] with L hDisc
  intro prime l u hl hu hLow hUpper
  have hAlpha :
      parityOriginalActualFullDyadProxyDifference434 prime L S gamma l u =
      b629ActualFineAlpha434 prime L S gamma l u := by
    funext n
    exact parity_original_actual_full_dyad_proxy_eq_b629434 prime L S gamma l u n
  rw [hAlpha]
  exact hDisc prime l u hl hu hLow hUpper

/-- The SAME entire interval proxy discrepancy has |alpha_m|<=1
and genuine exp(sqrt L)-rough support uniformly in the full-cell
precision S, exactly the original conditions of Parity(4.2)/(7.3).
No #cells or cell endpoint renormalization occurs. -/
theorem parity_eventually_original_full_dyad_proxy_norm_rough434
    (S beta gamma : ℝ) (hS : 0<S)
    (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop,∀ (prime : Bool) (l u : ℕ),
      Real.exp (beta*L)≤(l:ℝ) → ∀ n : ℕ,
      ‖parityOriginalActualFullDyadProxyDifference434 prime L S gamma l u n‖≤1 ∧
      (parityOriginalActualFullDyadProxyDifference434 prime L S gamma l u n≠0 →
        SourceRoughAbove n (Real.exp (Real.sqrt L))) := by
  filter_upwards [b629_actual_fine_coefficient_and_rough_support434
    S beta gamma hS hbeta hgamma] with L hSource
  intro prime l u hl n
  have hAlpha := parity_original_actual_full_dyad_proxy_eq_b629434
    prime L S gamma l u n
  rw [hAlpha]
  exact hSource prime l u hl n
end Green64Analytic.Parity

end

end

