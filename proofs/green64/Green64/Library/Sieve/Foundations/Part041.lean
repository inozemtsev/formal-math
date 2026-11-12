module

public import Green64.Library.Sieve.Foundations.Part040
public import Green64.Library.Sieve.Foundations.Part028
public import Green64.Library.Sieve.Foundations.Part023
public import Green64.Library.Sieve.Foundations.Part030
public import Green64.Library.Sieve.Foundations.Part032
public import Green64.Library.Sieve.Foundations.Part029
public import Green64.Library.Sieve.Foundations.Part031
public import Green64.Library.Sieve.Foundations.Part013

@[expose] public section

/-!
# Sieve / Foundations / Part041

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## TruePsiGlobalBallError -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Correct full-original source complex smooth Fourier physical
outer with ALL natural (e,m,k,m',n), the ACTUAL all-odd positive
Cauchy support, and the full ψ(z/Z) neighboring Z dyads. The
cofactor α and authentic two-endpoint B509 Q/P/H0/W1/ε signed
weights are kept INSIDE the source cell definition. -/
def parityOriginalActualTruePsiGlobalPhysicalSource434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (ZS : Finset ℕ) : ℂ :=
  ∑k∈KS,∑Z∈ZS,
    ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
      ∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          parityOriginalActualTruePsiPhysicalCell434
            d L E V (Z:ℝ) hL band slot δ ξ rho alpha signed
            Y e m K (parityOriginalHistoricalFullNEnvelope434 V) k
        else 0

/-- The same actual h=-2 full-odd source finite sum with ONE 3D
Schwartz Fourier BALL per original signed k and every real smooth
ψ scale Z. Buffer one through log4 is necessary for SOURCE equality. -/
def parityOriginalActualTruePsiGlobalPhysicalBall434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (ZS : Finset ℕ)
    (buf : ℝ → ℂ) (a b T : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → a≤t ∧ t≤b) : ℂ :=
  ∑k∈KS,∑Z∈ZS,
    ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
      ∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          parityOriginalActualTruePsiPhysicalCellFourierBall434
            d L U E V (Z:ℝ) hL band slot δ ξ rho alpha signed
            Y e m K (parityOriginalHistoricalFullNEnvelope434 V) k
            buf a b T hSmooth hSupport
        else 0

/-- Every real original source term belongs to its genuine smooth
ψ source carrier and has an actual per-cell paid 3D Fourier error.
This is an EXACT global complex-four-sum triangle after taking
SOURCE−BALL difference, with true signed k and both neighboring Z.
It does not invoke false norm monotonicity of a subset of characters
and does not add any scalar saving hypothesis. -/
theorem parity_original_actual_true_psi_global_physical_ball_error_le_mass434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
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
    ‖parityOriginalActualTruePsiGlobalPhysicalSource434
        d L E V hL band slot δ ξ rho alpha signed Y K KS ZS -
      parityOriginalActualTruePsiGlobalPhysicalBall434
        d L U E V hL band slot δ ξ rho alpha signed Y K KS ZS
        buf a b T hSmooth hSupport‖ ≤
    ∑k∈KS,∑Z∈ZS,
      ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
        ∑m∈K,
          if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
            let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
              d L band slot δ Y e m K (parityOriginalHistoricalFullNEnvelope434 V) k
            let W : (ℕ×ℕ) → ℂ := fun q =>
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
              parityOriginalHistoricalDyadicSmoothPsi434
                ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
            let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
              L hL U E V (Z:ℝ) k buf a b hSmooth hSupport
            parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
              (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
          else 0 := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Src : ℤ → ℕ → ℕ → ℕ → ℂ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      parityOriginalActualTruePsiPhysicalCell434
        d L E V (Z:ℝ) hL band slot δ ξ rho alpha signed Y e m K J k
    else 0
  let Bal : ℤ → ℕ → ℕ → ℕ → ℂ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      parityOriginalActualTruePsiPhysicalCellFourierBall434
        d L U E V (Z:ℝ) hL band slot δ ξ rho alpha signed Y e m K J k
        buf a b T hSmooth hSupport
    else 0
  let Err : ℤ → ℕ → ℕ → ℕ → ℝ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k
      let W : (ℕ×ℕ) → ℂ := fun q =>
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V (Z:ℝ) k buf a b hSmooth hSupport
      parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
    else 0
  change ‖(∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,Src k Z e m) -
    (∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,Bal k Z e m)‖ ≤
    ∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,Err k Z e m
  rw [←Finset.sum_sub_distrib]
  apply norm_sum_le_of_le KS
  intro k hk
  rw [←Finset.sum_sub_distrib]
  apply norm_sum_le_of_le ZS
  intro Z hZ
  rw [←Finset.sum_sub_distrib]
  apply norm_sum_le_of_le EF
  intro e he
  rw [←Finset.sum_sub_distrib]
  apply norm_sum_le_of_le K
  intro m hm
  by_cases hK : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
  · have heOdd : Odd e := (Finset.mem_filter.mp he).2
    have hCell := parity_original_true_psi_ungated_physical_cell_ball_error434
      d L U E V (Z:ℝ) hL band slot δ ξ rho alpha signed
      Y e m K J k heOdd hU hE hV (by exact_mod_cast (hZpos Z hZ))
      hm hDyad buf a b hSmooth hSupport hOne4 H T hT
    dsimp only at hCell
    simpa only [Src,Bal,Err,hK,ite_true,J] using hCell
  · simp [Src,Bal,Err,hK]
end Green64Analytic.Parity

end

end

/-! ## FullPsiPhysicalBallFiniteFubini -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Exact original true smooth-psi complex Fourier BALL Fubini for
all natural e,m,(m',n). A SINGLE genuine Schwartz kernel f(k,Z)
is shared within a fixed signed k and smooth Z cell. This identity
interchanges the finite, original signed complex physical outer
with the three-dimensional Fourier integral WITHOUT taking a norm.
Actual coefficients can include original B509 Q/P H0, fine b629 alpha,
complete chi projector, W1, epsilon, and smooth psi with no mask change.
Every Fourier phase uses the exact original 2pi logarithmic convention.
The proof uses the true compact ball integrability of all finite
Schwartz Fourier source terms and no TypeII or E4.1 input. -/
theorem parity_original_full_psi_physical_ball_two_outer_fubini434
    (EF K : Finset ℕ) (S : ℕ → ℕ → Finset (ℕ×ℕ))
    (W : ℕ → ℕ → (ℕ×ℕ) → ℂ)
    (t : ℕ → ℕ → (ℕ×ℕ) → EuclideanSpace ℝ (Fin 3))
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) (T : ℝ) :
    (∑e∈EF,∑m∈K,
      ∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434
          (S e m) (W e m) (t e m) f ζ) =
    ∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (∑e∈EF,∑m∈K,∑q∈S e m,
          W e m q*parityOriginal3DPhysicalLogFourierPhase434 ζ (t e m q)) := by
  classical
  let B : Set (EuclideanSpace ℝ (Fin 3)) := {ζ | ‖ζ‖≤T}
  have hClosed : B=Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) T := by
    ext ζ
    simp [B,Metric.mem_closedBall,dist_zero_right]
  have hCompact : IsCompact B := by
    rw [hClosed]
    exact isCompact_closedBall _ _
  let H : ℕ → ℕ → EuclideanSpace ℝ (Fin 3) → ℂ := fun e m ζ =>
    parityOriginal3DPhysicalFiniteTwistedSource434
      (S e m) (W e m) (t e m) f ζ
  have hContinuous (e m : ℕ) : Continuous (H e m) := by
    dsimp [H,parityOriginal3DPhysicalFiniteTwistedSource434]
    apply (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)).continuous.mul
    apply continuous_finsetSum
    intro q hq
    have hPhase : Continuous (fun ζ : EuclideanSpace ℝ (Fin 3) =>
      parityOriginal3DPhysicalLogFourierPhase434 ζ (t e m q)) := by
      unfold parityOriginal3DPhysicalLogFourierPhase434
      fun_prop
    exact continuous_const.mul hPhase
  have hI (e m : ℕ) : IntegrableOn (H e m) B :=
    (hContinuous e m).continuousOn.integrableOn_compact hCompact
  calc
    (∑e∈EF,∑m∈K,∫ζ in B,H e m ζ) =
        ∑p∈EF.product K,∫ζ in B,H p.1 p.2 ζ := by
          exact (Finset.sum_product EF K (fun p : ℕ × ℕ =>
            ∫ζ in B,H p.1 p.2 ζ)).symm
    _ = ∫ζ in B,∑p∈EF.product K,H p.1 p.2 ζ := by
      apply (integral_finset_sum (EF.product K) ?_).symm
      intro p hp
      exact hI p.1 p.2
    _ = ∫ζ in B,(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (∑e∈EF,∑m∈K,∑q∈S e m,
          W e m q*parityOriginal3DPhysicalLogFourierPhase434 ζ (t e m q)) := by
      apply integral_congr_ae
      filter_upwards [] with ζ
      change (∑p∈EF.product K,
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
        (∑q∈S p.1 p.2,
          W p.1 p.2 q * parityOriginal3DPhysicalLogFourierPhase434 ζ
            (t p.1 p.2 q))) = _
      calc
        (∑p∈EF.product K,
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
          (∑q∈S p.1 p.2,
            W p.1 p.2 q * parityOriginal3DPhysicalLogFourierPhase434 ζ
              (t p.1 p.2 q))) =
          ∑e∈EF, ∑m∈K,
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
            (∑q∈S e m,
              W e m q * parityOriginal3DPhysicalLogFourierPhase434 ζ (t e m q)) :=
                Finset.sum_product EF K _
        _ = (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
            (∑e∈EF,∑m∈K,∑q∈S e m,
              W e m q * parityOriginal3DPhysicalLogFourierPhase434 ζ (t e m q)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## TruePsiEtaFilteredGlobalBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Actual TRUE original h=-2 smooth source 3D Fourier BALL with
only genuine η_eη_n-nonzero events kept BEFORE Fourier truncation.
This is source-exact but NOT automatically the B633 unrestricted
4.17 χ-correlator: a separate ghost comparison is required. -/
def parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (ZS : Finset ℕ)
    (buf : ℝ → ℂ) (a b T : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → a≤t ∧ t≤b) : ℂ :=
  ∑k∈KS,∑Z∈ZS,
    ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
      ∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          parityOriginalActualTruePsiEtaActiveFourierBall434
            d L U E V (Z:ℝ) hL band slot δ ξ rho alpha signed
            Y e m K (parityOriginalHistoricalFullNEnvelope434 V) k
            buf a b T hSmooth hSupport
        else 0

/-- Genuine original full all-odd SOURCE complex sum minus its
ETA-ACTIVE-ONLY 3D Fourier ball has paid error supported strictly
on actual nonzero original ηeηn physical events, preserving all
signed k and both neighboring smooth ψ(Z) dyads. This removes
zero-η ghost contributions BEFORE Fourier inversion, rather than
making a false pointwise truncated-Fourier zero assertion. The
numerical global positive mass still requires a separate proof. -/
theorem parity_original_actual_true_psi_eta_active_global_physical_ball_error_le_mass434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
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
    ‖parityOriginalActualTruePsiGlobalPhysicalSource434
        d L E V hL band slot δ ξ rho alpha signed Y K KS ZS -
      parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
        d L U E V hL band slot δ ξ rho alpha signed Y K KS ZS
        buf a b T hSmooth hSupport‖ ≤
    ∑k∈KS,∑Z∈ZS,
      ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
        ∑m∈K,
          if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
            let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
              d L E V hL band slot δ Y e m K (parityOriginalHistoricalFullNEnvelope434 V) k
            let W : (ℕ×ℕ) → ℂ := fun q =>
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
              parityOriginalHistoricalDyadicSmoothPsi434
                ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
            let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
              L hL U E V (Z:ℝ) k buf a b hSmooth hSupport
            parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
              (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
          else 0 := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Src : ℤ → ℕ → ℕ → ℕ → ℂ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      parityOriginalActualTruePsiPhysicalCell434
        d L E V (Z:ℝ) hL band slot δ ξ rho alpha signed Y e m K J k
    else 0
  let Bal : ℤ → ℕ → ℕ → ℕ → ℂ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      parityOriginalActualTruePsiEtaActiveFourierBall434
        d L U E V (Z:ℝ) hL band slot δ ξ rho alpha signed Y e m K J k
        buf a b T hSmooth hSupport
    else 0
  let Err : ℤ → ℕ → ℕ → ℕ → ℝ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
        d L E V hL band slot δ Y e m K J k
      let W : (ℕ×ℕ) → ℂ := fun q =>
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V (Z:ℝ) k buf a b hSmooth hSupport
      parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
    else 0
  change ‖(∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,Src k Z e m) -
    (∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,Bal k Z e m)‖ ≤
    ∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,Err k Z e m
  rw [←Finset.sum_sub_distrib]
  apply norm_sum_le_of_le KS
  intro k hk
  rw [←Finset.sum_sub_distrib]
  apply norm_sum_le_of_le ZS
  intro Z hZ
  rw [←Finset.sum_sub_distrib]
  apply norm_sum_le_of_le EF
  intro e he
  rw [←Finset.sum_sub_distrib]
  apply norm_sum_le_of_le K
  intro m hm
  by_cases hK : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
  · have heOdd : Odd e := (Finset.mem_filter.mp he).2
    have hCell := parity_original_actual_true_psi_eta_active_cell_ball_error434
      d L U E V (Z:ℝ) hL band slot δ ξ rho alpha signed
      Y e m K J k heOdd hU hE hV (by exact_mod_cast (hZpos Z hZ))
      hm hDyad buf a b hSmooth hSupport hOne4 H T hT
    dsimp only at hCell
    simpa only [Src,Bal,Err,hK,ite_true,J] using hCell
  · simp [Src,Bal,Err,hK]
end Green64Analytic.Parity

end

end

/-! ## TruePsiEtaActiveMassDegree -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The ACTUAL original h=-2 B509 physical offdiagonal absolute
coefficient mass with only nonzero source η_eη_n physical events,
fully summed over all odd e,m and signed k in a proven |k|≤N window,
is controlled by (2N+1) times the REAL original unweighted positive
Cauchy diagonal. No e,m,n multiplicity, no χ cardinal loss, and no
invalid signed-subsum norm comparison. This is the genuine SOURCE
positive mass required by the correctly filtered 3D Fourier tail. -/
theorem parity_original_true_psi_eta_active_k_mass_le_diagonal434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (N : ℕ)
    (hKS : ∀k∈KS,k.natAbs≤N) :
    (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
      ∑m∈K,∑k∈KS,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈parityOriginalActualTruePsiEtaActivePhysicalEvents434
            d L E V hL band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k,
            ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho alpha signed Y e q.2 m q.1‖
        else 0) ≤
      ((2*N+1:ℕ):ℝ) *
        parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
          d L band slot δ ξ rho K
          (parityOriginalHistoricalFullOddEEnvelope434 E)
          (parityOriginalHistoricalFullNEnvelope434 V) alpha signed Y := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Sk (e m : ℕ) : Finset ℤ :=
    parityOriginalHistoricalNonzeroKSupport434 e m K
  let Bk (e m : ℕ) : Finset ℤ :=
    (parityOriginalHistoricalKSupport434 e m K).filter (fun k=>k.natAbs≤N)
  let S (e m : ℕ) (k : ℤ) : Finset (ℕ×ℕ) :=
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
  let W (e m : ℕ) (q : ℕ×ℕ) : ℝ :=
    ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho alpha signed Y e q.2 m q.1‖
  let mass (e m : ℕ) (k : ℤ) : ℝ :=
    ∑q∈parityOriginalActualTruePsiEtaActivePhysicalEvents434
      d L E V hL band slot δ Y e m K J k, W e m q
  let raw (e m : ℕ) (k : ℤ) : ℝ := ∑q∈S e m k,W e m q
  have hRawPos (e m : ℕ) (k : ℤ) : 0≤ raw e m k :=
    Finset.sum_nonneg (fun q hq => norm_nonneg _)
  have hMassLe (e m : ℕ) (k : ℤ) : mass e m k≤ raw e m k := by
    dsimp [mass,raw,S,parityOriginalActualTruePsiEtaActivePhysicalEvents434]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro q hq hnot
      exact norm_nonneg _
  have hK (e m : ℕ) :
      (∑k∈KS,if k∈Sk e m then mass e m k else 0) ≤
      ∑k∈Bk e m,raw e m k := by
    have hSub : (KS.filter (fun k => k∈Sk e m))⊆Bk e m := by
      intro k hk
      obtain ⟨hIn,hSk⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hSk).1,hKS k hIn⟩
    calc
      _ ≤ ∑k∈KS,if k∈Sk e m then raw e m k else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hkk : k∈Sk e m
        · simp only [hkk,ite_true]
          exact hMassLe e m k
        · simp only [hkk,ite_false,le_refl]
      _ = ∑k∈KS.filter (fun k => k∈Sk e m),raw e m k := by
        rw [Finset.sum_filter]
      _ ≤ ∑k∈Bk e m,raw e m k :=
        Finset.sum_le_sum_of_subset_of_nonneg hSub
          (fun k hk hnot => hRawPos e m k)
  have hE (e : ℕ) (he : e∈EF) :
      (∑m∈K,∑k∈KS,if k∈Sk e m then mass e m k else 0) ≤
      ((2*N+1:ℕ):ℝ)*
        (∑n∈J,∑m∈K,
          ‖alpha m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
            d L band slot δ ξ rho signed Y e n m‖^2) := by
    calc
      _ ≤ ∑m∈K,∑k∈Bk e m,raw e m k :=
        Finset.sum_le_sum (fun m hm=>hK e m)
      _ ≤ ((2*N+1:ℕ):ℝ)*
        (∑n∈J,∑m∈K,
          ‖alpha m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
            d L band slot δ ξ rho signed Y e n m‖^2) := by
        exact parity_original_historical_ungated_bounded_k_physical_mass_le_diagonal434
          d L band slot δ ξ rho alpha signed Y e K J N
          (Finset.mem_filter.mp he).2
  unfold parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
  change (∑e∈EF,∑m∈K,∑k∈KS,if k∈Sk e m then mass e m k else 0) ≤
    ((2*N+1:ℕ):ℝ)*
      (∑e∈EF,∑n∈J,∑m∈K,
        ‖alpha m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2)
  calc
    _ ≤ ∑e∈EF,((2*N+1:ℕ):ℝ)*
      (∑n∈J,∑m∈K,
        ‖alpha m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2) :=
      Finset.sum_le_sum hE
    _ = _ := by rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## TruePsiEtaActiveDyadMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The entire ACTUAL original h=-2 full odd-e B509 physical
η-ACTIVE positive coefficient mass over all true signed k and all
smooth ψ neighboring Z contributes at most TWO per physical z.
Coupled to native bounded-quotient k-degree, this is <=
  2(2N+1) × ONE real positive original Cauchy diagonal.
No #Z/#e/#m or character-count loss and no false restricted
complex-norm monotonicity. The statement explicitly requires the
real small k bound and powers-of-two source smooth Z carrier. -/
theorem parity_original_true_psi_eta_active_dyad_k_mass_le_diagonal434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (ZS : Finset ℕ) (N : ℕ)
    (hKS : ∀k∈KS,k.natAbs≤N)
    (hPower : ∀Z∈ZS,∃j : ℕ,Z=(2:ℕ)^j) :
    (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
      ∑m∈K,∑k∈KS,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑Z∈ZS,
            let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
              d L E V hL band slot δ Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) k
            let W : (ℕ×ℕ) → ℂ := fun q =>
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
              parityOriginalHistoricalDyadicSmoothPsi434
                ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
            parityOriginal3DPhysicalFiniteCoefficientMass434 S W
        else 0) ≤
      2*((2*N+1:ℕ):ℝ) *
        parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
          d L band slot δ ξ rho K
          (parityOriginalHistoricalFullOddEEnvelope434 E)
          (parityOriginalHistoricalFullNEnvelope434 V) alpha signed Y := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Sk (e m : ℕ) := parityOriginalHistoricalNonzeroKSupport434 e m K
  let S (e m : ℕ) (k : ℤ) :=
    parityOriginalActualTruePsiEtaActivePhysicalEvents434
      d L E V hL band slot δ Y e m K J k
  let W (e m : ℕ) (q : ℕ×ℕ) : ℂ :=
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho alpha signed Y e q.2 m q.1
  let mass (e m : ℕ) (k : ℤ) :=
    parityOriginal3DPhysicalFiniteCoefficientMass434 (S e m k) (W e m)
  let massZ (e m : ℕ) (k : ℤ) (Z : ℕ) :=
    parityOriginal3DPhysicalFiniteCoefficientMass434 (S e m k)
      (fun q => W e m q*parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ)))
  have hOne (e m : ℕ) (k : ℤ) :
      (∑Z∈ZS,massZ e m k Z) ≤ 2*mass e m k := by
    dsimp only [massZ,mass]
    unfold parityOriginal3DPhysicalFiniteCoefficientMass434
    exact parity_original_true_psi_finite_physical_weighted_mass_le_two434
      (S e m k) (W e m)
      (fun q => parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) ZS hPower
  have hMass := parity_original_true_psi_eta_active_k_mass_le_diagonal434
    d L E V hL band slot δ ξ rho alpha signed Y K KS N hKS
  have hTwo :
      (∑e∈EF,∑m∈K,∑k∈KS,
        if k∈Sk e m then ∑Z∈ZS,massZ e m k Z else 0) ≤
      2*(∑e∈EF,∑m∈K,∑k∈KS,
        if k∈Sk e m then mass e m k else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    by_cases hkk : k∈Sk e m
    · simp only [hkk,ite_true]
      exact hOne e m k
    · simp [hkk]
  dsimp only [massZ,mass,Sk,S,W] at hTwo
  change (∑e∈EF,∑m∈K,∑k∈KS,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑Z∈ZS,
            parityOriginal3DPhysicalFiniteCoefficientMass434
              (parityOriginalActualTruePsiEtaActivePhysicalEvents434
                d L E V hL band slot δ Y e m K J k)
              (fun q => parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
               parityOriginalHistoricalDyadicSmoothPsi434
                ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ)))
        else 0) ≤ 2*((2*N+1:ℕ):ℝ)*
          parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
            d L band slot δ ξ rho K EF J alpha signed Y
  calc
    _ ≤ 2*(∑e∈EF,∑m∈K,∑k∈KS,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        ∑q∈parityOriginalActualTruePsiEtaActivePhysicalEvents434
          d L E V hL band slot δ Y e m K J k,
          ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho alpha signed Y e q.2 m q.1‖
      else 0) := by
        simpa only [parityOriginal3DPhysicalFiniteCoefficientMass434] using hTwo
    _ ≤ 2*((2*N+1:ℕ):ℝ)*
      parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
        d L band slot δ ξ rho K EF J alpha signed Y := by
        have hh := mul_le_mul_of_nonneg_left hMass (by norm_num : (0:ℝ)≤2)
        simpa only [mul_assoc] using hh
end Green64Analytic.Parity

end

end

/-! ## TruePsiEtaGlobalMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Pure finite signed-index SOURCE Fubini, needed to compare the
original (k,Z,e,m) Fourier-ball error mass with the native
(e,m,k,Z) positive bounded-quotient Cauchy diagonal mass. No
source term or multiplicity disappears. -/
theorem parity_original_true_psi_finite_four_outer_comm434
    {κ ζ ε μ : Type*}
    (K : Finset κ) (Z : Finset ζ) (E : Finset ε) (M : Finset μ)
    (W : κ → ζ → ε → μ → ℝ) :
    (∑k∈K,∑z∈Z,∑e∈E,∑m∈M,W k z e m) =
      ∑e∈E,∑m∈M,∑k∈K,∑z∈Z,W k z e m := by
  classical
  calc
    _ = ∑k∈K,∑e∈E,∑z∈Z,∑m∈M,W k z e m := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = ∑e∈E,∑k∈K,∑z∈Z,∑m∈M,W k z e m := Finset.sum_comm
    _ = ∑e∈E,∑k∈K,∑m∈M,∑z∈Z,W k z e m := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = ∑e∈E,∑m∈M,∑k∈K,∑z∈Z,W k z e m := by
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.sum_comm

/-- The ACTUAL true source h=-2 B509 FULL (k,Z,e,m) 3D Fourier
truncation positive coefficient mass on η-ACTIVE physical pairs,
with smooth ψ(z/Z) and literal original H0/W1/ε/fine α, costs at
most 2×(2N+1) times original ungated positive Cauchy diagonal.
No #Z/#e/#m exponent and no arbitrary large-k events survive,
because the physical signed k set is explicitly short and only
η≠0 events are retained before truncation. This is the right
positive mass to multiply by a single real Schwartz H-moment. -/
theorem parity_original_actual_true_psi_eta_global_kZ_mass_le_diagonal434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (ZS : Finset ℕ) (N : ℕ)
    (hKS : ∀k∈KS,k.natAbs≤N)
    (hPower : ∀Z∈ZS,∃j : ℕ,Z=(2:ℕ)^j) :
    (∑k∈KS,∑Z∈ZS,
      ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
        ∑m∈K,
          if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
            let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
              d L E V hL band slot δ Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) k
            let W : (ℕ×ℕ) → ℂ := fun q =>
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
              parityOriginalHistoricalDyadicSmoothPsi434
                ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
            parityOriginal3DPhysicalFiniteCoefficientMass434 S W
          else 0) ≤
      2*((2*N+1:ℕ):ℝ) *
        parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
          d L band slot δ ξ rho K
          (parityOriginalHistoricalFullOddEEnvelope434 E)
          (parityOriginalHistoricalFullNEnvelope434 V) alpha signed Y := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let mass : ℤ → ℕ → ℕ → ℕ → ℝ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
        d L E V hL band slot δ Y e m K J k
      let W : (ℕ×ℕ) → ℂ := fun q =>
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
      parityOriginal3DPhysicalFiniteCoefficientMass434 S W
    else 0
  have hPerm := parity_original_true_psi_finite_four_outer_comm434
    KS ZS EF K mass
  have hIte (e m : ℕ) (k : ℤ) :
      (∑Z∈ZS,mass k Z e m) =
      (if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        ∑Z∈ZS,
          let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
            d L E V hL band slot δ Y e m K J k
          let W : (ℕ×ℕ) → ℂ := fun q =>
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W
      else 0) := by
    by_cases hk : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
    · simp only [mass,hk,ite_true]
    · simp [mass,hk]
  have hBound := parity_original_true_psi_eta_active_dyad_k_mass_le_diagonal434
    d L E V hL band slot δ ξ rho alpha signed Y K KS ZS N hKS hPower
  change (∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,mass k Z e m) ≤ _
  calc
    _ = ∑e∈EF,∑m∈K,∑k∈KS,∑Z∈ZS,mass k Z e m := hPerm
    _ = ∑e∈EF,∑m∈K,∑k∈KS,
        (if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑Z∈ZS,
            let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
              d L E V hL band slot δ Y e m K J k
            let W : (ℕ×ℕ) → ℂ := fun q =>
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
              parityOriginalHistoricalDyadicSmoothPsi434
                ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
            parityOriginal3DPhysicalFiniteCoefficientMass434 S W
        else 0) := by
          apply Finset.sum_congr rfl
          intro e he
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro k hk
          exact hIte e m k
    _ ≤ _ := hBound
end Green64Analytic.Parity

end

end

/-! ## TruePsiEtaActiveGlobalTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The ACTUAL full-odd original h=-2 B509 SOURCE with all true
ηeηn-nonzero natural (e,n,m,m',z) and BOTH real smooth ψ-neighbor
Z scales differs from its globally truncated 3D Fourier BALL by
at most its genuine SOURCE H-Schwartz-moment/T^H times
    2 (2N+1) × ORIGINAL POSITIVE CAUCHY DIAGONAL.
This is a full k,Z,e,m finite source error with NO #χ/#e/#m/#Z
multiplicity loss and no false complex subset norm monotonicity.
Every moment is the literal five-factor Parity(4.14) Schwartz kernel
at the corrected cap-free Z<=24 Cbox exp L L^(K0+88), and every
factor in the actual physical signed H0/W1/ε source is preserved.
The Fourier ball is eta-ACTIVE-ONLY; identifying it with the
unrestricted Parity(4.17) B633 source-image is a distinct SOURCE debt. -/
theorem parity_original_true_psi_eta_active_global_source_tail_le_diagonal434
    (d : ℕ) (L U E V K0 Cbox A R : ℝ) (hL : 8≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hE : E=U*L^(-K0))
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (KS : Finset ℤ) (ZS : Finset ℕ) (N : ℕ)
    (hKS : ∀k∈KS,k≠0 ∧ k.natAbs≤N)
    (hZSpos : ∀Z∈ZS,0<Z)
    (hZSupper : ∀Z∈ZS,(Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88))
    (hPower : ∀Z∈ZS,∃j : ℕ,Z=(2:ℕ)^j)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (hA : 0<A) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (H : ℕ)
    (hLargeE : 2*A*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
      (2:ℝ)^(H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
      ((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (hR : 1≤R)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (T : ℝ) (hT : 0<T) :
    let fconst := parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hSmooth hSupport H
    let Q := (fconst*L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)))/T^H
    let D := parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
      d L band slot δ ξ rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V) alpha signed Y
    ‖parityOriginalActualTruePsiGlobalPhysicalSource434
      d L E V hL band slot δ ξ rho alpha signed Y K KS ZS -
      parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
        d L U E V hL band slot δ ξ rho alpha signed Y K KS ZS
        buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ ≤
      Q*(2*((2*N+1:ℕ):ℝ)*D) := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let fconst := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport H
  let Q := (fconst*L^((5*(K0+90))*(((H+P:ℕ):ℝ)+1)))/T^H
  let D := parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
    d L band slot δ ξ rho K EF J alpha signed Y
  have hfconst : 0≤fconst :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport H hR
  have hQ : 0≤Q := by dsimp [Q]; positivity
  let mass : ℤ → ℕ → ℕ → ℕ → ℝ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
        d L E V hL band slot δ Y e m K J k
      let W : (ℕ×ℕ) → ℂ := fun q =>
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
      parityOriginal3DPhysicalFiniteCoefficientMass434 S W
    else 0
  let err : ℤ → ℕ → ℕ → ℕ → ℝ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
        d L E V hL band slot δ Y e m K J k
      let W : (ℕ×ℕ) → ℂ := fun q =>
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
      parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
    else 0
  have hBase := parity_original_actual_true_psi_eta_active_global_physical_ball_error_le_mass434
    d L U E V hL band slot δ ξ rho alpha signed Y K KS ZS
    hU (by rw [hE]; positivity : 0<E) hV hDyad hZSpos
    buf (-Real.log A) (Real.log A) hSmooth hSupport hOne4 H T hT
  have hMass := parity_original_actual_true_psi_eta_global_kZ_mass_le_diagonal434
    d L E V hL band slot δ ξ rho alpha signed Y K KS ZS N
    (fun k hk => (hKS k hk).2) hPower
  have hMoment (k : ℤ) (hk : k∈KS) (Z : ℕ) (hz : Z∈ZS) :
      parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport) /T^H ≤ Q := by
    have hm := parity_original_historical_box_source_BH_uniform_polylog434
      L U E V (Z:ℝ) K0 Cbox A hL hK0 k (hKS k hk).1 hU hV hUV hE
      (Nat.cast_nonneg _) hCbox hLargeC (hZSupper Z hz) hA
      buf hSmooth hSupport H hLargeE hLargeN R hR hCube
    have hden : 0≤T^H := pow_nonneg hT.le H
    exact div_le_div_of_nonneg_right hm hden
  have hCell (k : ℤ) (hk : k∈KS) (Z : ℕ) (hz : Z∈ZS)
      (e : ℕ) (he : e∈EF) (m : ℕ) (hm : m∈K) :
      err k Z e m≤Q*mass k Z e m := by
    by_cases hkk : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
    · have hCoeff : 0 ≤ mass k Z e m := by
        dsimp [mass]
        simp only [hkk,ite_true]
        exact parity_original_3d_physical_finite_coefficient_mass_nonneg434 _ _
      have hh := mul_le_mul_of_nonneg_left (hMoment k hk Z hz) hCoeff
      simpa only [mass,err,hkk,ite_true,mul_comm,div_eq_mul_inv] using hh
    · simp [err,mass,hkk]
  have hTotal :
      (∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,err k Z e m) ≤
      Q*(∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,mass k Z e m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Z hz
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    exact hCell k hk Z hz e he m hm
  dsimp only at hBase hMass ⊢
  change ‖parityOriginalActualTruePsiGlobalPhysicalSource434
      d L E V hL band slot δ ξ rho alpha signed Y K KS ZS -
      parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
        d L U E V hL band slot δ ξ rho alpha signed Y K KS ZS
        buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ ≤ Q*(2*((2*N+1:ℕ):ℝ)*D)
  calc
    _ ≤ ∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,err k Z e m := by
      simpa only [err,J,EF] using hBase
    _ ≤ Q*(∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,mass k Z e m) := hTotal
    _ ≤ Q*(2*((2*N+1:ℕ):ℝ)*D) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [mass,D,EF,J] using hMass) hQ
end Green64Analytic.Parity

end

end

/-! ## TruePsiFullKMassDegree -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The ACTUAL original h=-2 B509 physical offdiagonal absolute
coefficient mass over the entire ORIGINAL full-odd physical event source,
fully summed over all odd e,m and signed k in a proven |k|≤N window,
is controlled by (2N+1) times the REAL original unweighted positive
Cauchy diagonal. No e,m,n multiplicity, no χ cardinal loss, and no
invalid signed-subsum norm comparison. This is the genuine SOURCE positive mass for even zero-eta ghost terms. No complex signed subset inequality is used. -/
theorem parity_original_true_psi_full_k_mass_le_diagonal434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (N : ℕ)
    (hKS : ∀k∈KS,k.natAbs≤N) :
    (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
      ∑m∈K,∑k∈KS,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k,
            ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho alpha signed Y e q.2 m q.1‖
        else 0) ≤
      ((2*N+1:ℕ):ℝ) *
        parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
          d L band slot δ ξ rho K
          (parityOriginalHistoricalFullOddEEnvelope434 E)
          (parityOriginalHistoricalFullNEnvelope434 V) alpha signed Y := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Sk (e m : ℕ) : Finset ℤ :=
    parityOriginalHistoricalNonzeroKSupport434 e m K
  let Bk (e m : ℕ) : Finset ℤ :=
    (parityOriginalHistoricalKSupport434 e m K).filter (fun k=>k.natAbs≤N)
  let S (e m : ℕ) (k : ℤ) : Finset (ℕ×ℕ) :=
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
  let W (e m : ℕ) (q : ℕ×ℕ) : ℝ :=
    ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho alpha signed Y e q.2 m q.1‖
  let mass (e m : ℕ) (k : ℤ) : ℝ :=
    ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k, W e m q
  let raw (e m : ℕ) (k : ℤ) : ℝ := ∑q∈S e m k,W e m q
  have hRawPos (e m : ℕ) (k : ℤ) : 0≤ raw e m k :=
    Finset.sum_nonneg (fun q hq => norm_nonneg _)
  have hMassLe (e m : ℕ) (k : ℤ) : mass e m k≤ raw e m k := by
    change raw e m k ≤ raw e m k
    exact le_refl _
  have hK (e m : ℕ) :
      (∑k∈KS,if k∈Sk e m then mass e m k else 0) ≤
      ∑k∈Bk e m,raw e m k := by
    have hSub : (KS.filter (fun k => k∈Sk e m))⊆Bk e m := by
      intro k hk
      obtain ⟨hIn,hSk⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hSk).1,hKS k hIn⟩
    calc
      _ ≤ ∑k∈KS,if k∈Sk e m then raw e m k else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hkk : k∈Sk e m
        · simp only [hkk,ite_true]
          exact hMassLe e m k
        · simp only [hkk,ite_false,le_refl]
      _ = ∑k∈KS.filter (fun k => k∈Sk e m),raw e m k := by
        rw [Finset.sum_filter]
      _ ≤ ∑k∈Bk e m,raw e m k :=
        Finset.sum_le_sum_of_subset_of_nonneg hSub
          (fun k hk hnot => hRawPos e m k)
  have hE (e : ℕ) (he : e∈EF) :
      (∑m∈K,∑k∈KS,if k∈Sk e m then mass e m k else 0) ≤
      ((2*N+1:ℕ):ℝ)*
        (∑n∈J,∑m∈K,
          ‖alpha m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
            d L band slot δ ξ rho signed Y e n m‖^2) := by
    calc
      _ ≤ ∑m∈K,∑k∈Bk e m,raw e m k :=
        Finset.sum_le_sum (fun m hm=>hK e m)
      _ ≤ ((2*N+1:ℕ):ℝ)*
        (∑n∈J,∑m∈K,
          ‖alpha m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
            d L band slot δ ξ rho signed Y e n m‖^2) := by
        exact parity_original_historical_ungated_bounded_k_physical_mass_le_diagonal434
          d L band slot δ ξ rho alpha signed Y e K J N
          (Finset.mem_filter.mp he).2
  unfold parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
  change (∑e∈EF,∑m∈K,∑k∈KS,if k∈Sk e m then mass e m k else 0) ≤
    ((2*N+1:ℕ):ℝ)*
      (∑e∈EF,∑n∈J,∑m∈K,
        ‖alpha m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2)
  calc
    _ ≤ ∑e∈EF,((2*N+1:ℕ):ℝ)*
      (∑n∈J,∑m∈K,
        ‖alpha m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2) :=
      Finset.sum_le_sum hE
    _ = _ := by rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## TruePsiFullDyadKMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The entire ACTUAL original h=-2 full odd-e B509 physical
FULL original positive coefficient mass (including zero-η events) over all true signed k and all
smooth ψ neighboring Z contributes at most TWO per physical z.
Coupled to native bounded-quotient k-degree, this is <=
  2(2N+1) × ONE real positive original Cauchy diagonal.
No #Z/#e/#m or character-count loss and no false restricted
complex-norm monotonicity. The statement explicitly requires the
real small k bound and powers-of-two source smooth Z carrier. -/
theorem parity_original_true_psi_full_dyad_k_mass_le_diagonal434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (ZS : Finset ℕ) (N : ℕ)
    (hKS : ∀k∈KS,k.natAbs≤N)
    (hPower : ∀Z∈ZS,∃j : ℕ,Z=(2:ℕ)^j) :
    (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
      ∑m∈K,∑k∈KS,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑Z∈ZS,
            let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
              d L band slot δ Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) k
            let W : (ℕ×ℕ) → ℂ := fun q =>
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
              parityOriginalHistoricalDyadicSmoothPsi434
                ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
            parityOriginal3DPhysicalFiniteCoefficientMass434 S W
        else 0) ≤
      2*((2*N+1:ℕ):ℝ) *
        parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
          d L band slot δ ξ rho K
          (parityOriginalHistoricalFullOddEEnvelope434 E)
          (parityOriginalHistoricalFullNEnvelope434 V) alpha signed Y := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Sk (e m : ℕ) := parityOriginalHistoricalNonzeroKSupport434 e m K
  let S (e m : ℕ) (k : ℤ) :=
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
  let W (e m : ℕ) (q : ℕ×ℕ) : ℂ :=
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho alpha signed Y e q.2 m q.1
  let mass (e m : ℕ) (k : ℤ) :=
    parityOriginal3DPhysicalFiniteCoefficientMass434 (S e m k) (W e m)
  let massZ (e m : ℕ) (k : ℤ) (Z : ℕ) :=
    parityOriginal3DPhysicalFiniteCoefficientMass434 (S e m k)
      (fun q => W e m q*parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ)))
  have hOne (e m : ℕ) (k : ℤ) :
      (∑Z∈ZS,massZ e m k Z) ≤ 2*mass e m k := by
    dsimp only [massZ,mass]
    unfold parityOriginal3DPhysicalFiniteCoefficientMass434
    exact parity_original_true_psi_finite_physical_weighted_mass_le_two434
      (S e m k) (W e m)
      (fun q => parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) ZS hPower
  have hMass := parity_original_true_psi_full_k_mass_le_diagonal434
    d L E V hL band slot δ ξ rho alpha signed Y K KS N hKS
  have hTwo :
      (∑e∈EF,∑m∈K,∑k∈KS,
        if k∈Sk e m then ∑Z∈ZS,massZ e m k Z else 0) ≤
      2*(∑e∈EF,∑m∈K,∑k∈KS,
        if k∈Sk e m then mass e m k else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    by_cases hkk : k∈Sk e m
    · simp only [hkk,ite_true]
      exact hOne e m k
    · simp [hkk]
  dsimp only [massZ,mass,Sk,S,W] at hTwo
  change (∑e∈EF,∑m∈K,∑k∈KS,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑Z∈ZS,
            parityOriginal3DPhysicalFiniteCoefficientMass434
              (parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
                d L band slot δ Y e m K J k)
              (fun q => parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
               parityOriginalHistoricalDyadicSmoothPsi434
                ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ)))
        else 0) ≤ 2*((2*N+1:ℕ):ℝ)*
          parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
            d L band slot δ ξ rho K EF J alpha signed Y
  calc
    _ ≤ 2*(∑e∈EF,∑m∈K,∑k∈KS,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
          d L band slot δ Y e m K J k,
          ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho alpha signed Y e q.2 m q.1‖
      else 0) := by
        simpa only [parityOriginal3DPhysicalFiniteCoefficientMass434] using hTwo
    _ ≤ 2*((2*N+1:ℕ):ℝ)*
      parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
        d L band slot δ ξ rho K EF J alpha signed Y := by
        have hh := mul_le_mul_of_nonneg_left hMass (by norm_num : (0:ℝ)≤2)
        simpa only [mul_assoc] using hh
end Green64Analytic.Parity

end

end

/-! ## TruePsiFullGlobalMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The ACTUAL true source h=-2 B509 FULL (k,Z,e,m) 3D Fourier
truncation positive coefficient mass on FULL original physical pairs (including zero-η),
with smooth ψ(z/Z) and literal original H0/W1/ε/fine α, costs at
most 2×(2N+1) times original ungated positive Cauchy diagonal.
No #Z/#e/#m exponent and no arbitrary large-k events survive,
because the physical signed k set is explicitly short and only
the full true original source physical carrier is retained before truncation. This is the right
positive mass to multiply by a single real Schwartz H-moment. -/
theorem parity_original_actual_true_psi_full_global_kZ_mass_le_diagonal434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (ZS : Finset ℕ) (N : ℕ)
    (hKS : ∀k∈KS,k.natAbs≤N)
    (hPower : ∀Z∈ZS,∃j : ℕ,Z=(2:ℕ)^j) :
    (∑k∈KS,∑Z∈ZS,
      ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
        ∑m∈K,
          if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
            let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
              d L band slot δ Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) k
            let W : (ℕ×ℕ) → ℂ := fun q =>
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
              parityOriginalHistoricalDyadicSmoothPsi434
                ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
            parityOriginal3DPhysicalFiniteCoefficientMass434 S W
          else 0) ≤
      2*((2*N+1:ℕ):ℝ) *
        parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
          d L band slot δ ξ rho K
          (parityOriginalHistoricalFullOddEEnvelope434 E)
          (parityOriginalHistoricalFullNEnvelope434 V) alpha signed Y := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let mass : ℤ → ℕ → ℕ → ℕ → ℝ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k
      let W : (ℕ×ℕ) → ℂ := fun q =>
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
      parityOriginal3DPhysicalFiniteCoefficientMass434 S W
    else 0
  have hPerm := parity_original_true_psi_finite_four_outer_comm434
    KS ZS EF K mass
  have hIte (e m : ℕ) (k : ℤ) :
      (∑Z∈ZS,mass k Z e m) =
      (if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        ∑Z∈ZS,
          let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot δ Y e m K J k
          let W : (ℕ×ℕ) → ℂ := fun q =>
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W
      else 0) := by
    by_cases hk : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
    · simp only [mass,hk,ite_true]
    · simp [mass,hk]
  have hBound := parity_original_true_psi_full_dyad_k_mass_le_diagonal434
    d L E V hL band slot δ ξ rho alpha signed Y K KS ZS N hKS hPower
  change (∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,mass k Z e m) ≤ _
  calc
    _ = ∑e∈EF,∑m∈K,∑k∈KS,∑Z∈ZS,mass k Z e m := hPerm
    _ = ∑e∈EF,∑m∈K,∑k∈KS,
        (if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑Z∈ZS,
            let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
              d L band slot δ Y e m K J k
            let W : (ℕ×ℕ) → ℂ := fun q =>
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
              parityOriginalHistoricalDyadicSmoothPsi434
                ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
            parityOriginal3DPhysicalFiniteCoefficientMass434 S W
        else 0) := by
          apply Finset.sum_congr rfl
          intro e he
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro k hk
          exact hIte e m k
    _ ≤ _ := hBound
end Green64Analytic.Parity

end

end

/-! ## FullPsiGhostMassBudget -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Explicit source-true POSITIVE total coefficient error mass of the
complete all-odd physical C∞ ψ global k/Z Fourier ball is bounded by
one uniform three-dimensional Schwartz moment and by twice the true
bounded-k Parity(4.10) Cauchy diagonal. This proves a mass estimate,
not merely a norm estimate; hence the same budget legally pays the
two zero-η spectral ghosts before comparison with Eq(4.17).
No complex signed-subsum monotonicity or artificial e-Pfree gate. -/
theorem parity_original_true_psi_full_global_ghost_mass_le_diagonal434
    (d : ℕ) (L U E V K0 Cbox A R : ℝ) (hL : 8≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hE : E=U*L^(-K0))
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (KS : Finset ℤ) (ZS : Finset ℕ) (N : ℕ)
    (hKS : ∀k∈KS,k≠0 ∧ k.natAbs≤N)
    (hZSpos : ∀Z∈ZS,0<Z)
    (hZSupper : ∀Z∈ZS,(Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88))
    (hPower : ∀Z∈ZS,∃j : ℕ,Z=(2:ℕ)^j)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (hA : 0<A) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (H : ℕ)
    (hLargeE : 2*A*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
      (2:ℝ)^(H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
      ((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (hR : 1≤R)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (T : ℝ) (hT : 0<T) :
    let fconst := parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hSmooth hSupport H
    let Q := (fconst*L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)))/T^H
    let D := parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
      d L band slot δ ξ rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V) alpha signed Y
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let err : ℤ → ℕ → ℕ → ℕ → ℝ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k
      let W : (ℕ×ℕ) → ℂ := fun q =>
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
      parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
    else 0
    (∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,err k Z e m) ≤
      Q*(2*((2*N+1:ℕ):ℝ)*D) := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let fconst := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport H
  let Q := (fconst*L^((5*(K0+90))*(((H+P:ℕ):ℝ)+1)))/T^H
  let D := parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
    d L band slot δ ξ rho K EF J alpha signed Y
  have hfconst : 0≤fconst :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport H hR
  have hQ : 0≤Q := by dsimp [Q]; positivity
  let mass : ℤ → ℕ → ℕ → ℕ → ℝ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k
      let W : (ℕ×ℕ) → ℂ := fun q =>
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
      parityOriginal3DPhysicalFiniteCoefficientMass434 S W
    else 0
  let err : ℤ → ℕ → ℕ → ℕ → ℝ := fun k Z e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k
      let W : (ℕ×ℕ) → ℂ := fun q =>
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
      parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
    else 0
  have hMass := parity_original_actual_true_psi_full_global_kZ_mass_le_diagonal434
    d L E V hL band slot δ ξ rho alpha signed Y K KS ZS N
    (fun k hk => (hKS k hk).2) hPower
  have hMoment (k : ℤ) (hk : k∈KS) (Z : ℕ) (hz : Z∈ZS) :
      parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport) /T^H ≤ Q := by
    have hm := parity_original_historical_box_source_BH_uniform_polylog434
      L U E V (Z:ℝ) K0 Cbox A hL hK0 k (hKS k hk).1 hU hV hUV hE
      (Nat.cast_nonneg _) hCbox hLargeC (hZSupper Z hz) hA
      buf hSmooth hSupport H hLargeE hLargeN R hR hCube
    have hden : 0≤T^H := pow_nonneg hT.le H
    exact div_le_div_of_nonneg_right hm hden
  have hCell (k : ℤ) (hk : k∈KS) (Z : ℕ) (hz : Z∈ZS)
      (e : ℕ) (he : e∈EF) (m : ℕ) (hm : m∈K) :
      err k Z e m≤Q*mass k Z e m := by
    by_cases hkk : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
    · have hCoeff : 0 ≤ mass k Z e m := by
        dsimp [mass]
        simp only [hkk,ite_true]
        exact parity_original_3d_physical_finite_coefficient_mass_nonneg434 _ _
      have hh := mul_le_mul_of_nonneg_left (hMoment k hk Z hz) hCoeff
      simpa only [mass,err,hkk,ite_true,mul_comm,div_eq_mul_inv] using hh
    · simp [err,mass,hkk]
  have hTotal :
      (∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,err k Z e m) ≤
      Q*(∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,mass k Z e m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Z hz
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    exact hCell k hk Z hz e he m hm
  dsimp only at hMass ⊢
  change (∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,err k Z e m) ≤
      Q*(2*((2*N+1:ℕ):ℝ)*D)
  calc
    _ ≤ Q*(∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,mass k Z e m) := hTotal
    _ ≤ Q*(2*((2*N+1:ℕ):ℝ)*D) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [mass,D,EF,J] using hMass) hQ
end Green64Analytic.Parity

end

end

/-! ## TruePsiGhostMassDefinition -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The actual positive source Fourier ghost MASS of the complete
post-Cauchy Parity(4.10) original all-odd physical k×Z envelope.
This is an exact abbreviation of the already source-audited positive
sum: the true h=-2 H0/W1/epsilon atom, original smooth ψ(z/Z),
actual genuine 3D Parity(4.14) Schwartz finite moment and natural
(e,m,m',n,z) multiplicities. No η mask or roughness gate is added.
The new compact definition prevents repeated elaboration of the
entire dependent source sum in downstream quantitative algebra. -/
def parityOriginalActualTruePsiGlobalPositiveGhostMass434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (ZS : Finset ℕ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → a≤t ∧ t≤b)
    (H : ℕ) (T : ℝ) : ℝ :=
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  ∑k∈KS,∑Z∈ZS,∑e∈EF,∑m∈K,
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
end Green64Analytic.Parity

end

end

/-! ## TruePsiOriginalOuterExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- EXACT SOURCE-correct all-odd physical Parity(4.10) h=-2
post-Cauchy offdiagonal with natural source e,n,m,m' is IDENTICAL
to the full true C∞ ψ-neighbor source outer used in the new 3D
Schwartz Fourier ball error. The full original Q/P/H0 pair weights,
true moving ηeηn, b629 fine cofactor alpha and signed epsilon are
not changed. The original source uses a half-open K⊂[U,2U) and
all odd e including original P-group-prime factors. This is a
complex signed EQUALITY before triangle, not an illicit comparison
between a restricted and an unrestricted signed sum. -/
theorem parity_original_ungated_true_psi_physical_source_outer_exact434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox) (hUV : Real.exp L≤U*V)
    (hUVhi : U*V≤Cbox*Real.exp L) (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let hLw : 8≤L := by linarith
    let Y := Nat.ceil (6*U*V)
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hLw band slot δ Y K
    let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V hLw band slot δ Y K)
    (∑e∈EF,∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
          d L band slot δ Y e m K J k,
          (((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ) *
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho alpha signed Y e q.2 m q.1)) =
    parityOriginalActualTruePsiGlobalPhysicalSource434
      d L E V hLw band slot δ ξ rho alpha signed Y K KS ZS := by
  classical
  have hLw : 8≤L := by linarith
  let Y := Nat.ceil (6*U*V)
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot δ Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot δ Y K)
  let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
  let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
    (((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ) *
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho alpha signed Y e q.2 m q.1)
  have hOld := parity_original_full_odd_actual_weight_global_smoothed_k_Z_outer434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot δ ξ rho K alpha signed hDyad
  dsimp only at hOld ⊢
  calc
    _ = ∑k∈KS,∑Z∈ZS,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈S e m k,
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ)) *
            W e m k q
        else 0 := hOld
    _ = parityOriginalActualTruePsiGlobalPhysicalSource434
      d L E V hLw band slot δ ξ rho alpha signed Y K KS ZS := by
      unfold parityOriginalActualTruePsiGlobalPhysicalSource434
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro Z hZ
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hK : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
      · simp only [hK,ite_true]
        unfold parityOriginalActualTruePsiPhysicalCell434
        apply Finset.sum_congr rfl
        intro q hq
        dsimp only [S,W]
        ring
      · simp [hK]
end Green64Analytic.Parity

end

end

/-! ## OriginalCauchyOddPhysicalEvents -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Exact ORIGINAL ungated Cauchy k-fibre from (m',z,n) to its
natural physical (m',n) events. All e,n,m,m',z multiplicities,
source H0/P/Q and signed epsilon remain literal; `z` is a canonical
function of (e,m,m',n), not an independent multiplicity. -/
theorem parity_original_ungated_cauchy_k_physical_event_exact434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (w : ℕ → ℕ → ℝ) :
    (∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
      ∑z∈parityOriginalHistoricalUngatedPhysicalValidZSupport434
        d L band slot delta Y e m mp J,
        ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
          (parityOriginalHistoricalUngatedPhysicalValidN434 d L band slot delta Y e m mp),
          ((w e n:ℝ):ℂ)*
          parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot delta freq rho alpha signed Y e n m mp) =
    ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K J k,
      ((w e q.2:ℝ):ℂ)*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e q.2 m q.1 := by
  classical
  let F : ℕ → ℕ → ℂ := fun mp n =>
    ((w e n:ℝ):ℂ)*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e n m mp
  have hMP (mp : ℕ) :
      (∑z∈parityOriginalHistoricalUngatedPhysicalValidZSupport434
        d L band slot delta Y e m mp J,
        ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
          (parityOriginalHistoricalUngatedPhysicalValidN434 d L band slot delta Y e m mp),
          F mp n) =
      ∑n∈J.filter (parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot delta Y e m mp),F mp n := by
    have hZ := parity_original_historical_ungated_weighted_z_source_filter_exact434
      d L band slot delta freq rho alpha signed Y e m mp
      (fun n => ((w e n:ℝ):ℂ)) J
    have hN := parity_original_historical_ungated_weighted_N_source_filter_exact434
      d L band slot delta freq rho alpha signed Y e m mp
      (fun n => ((w e n:ℝ):ℂ)) J
    have hFibre := parity_original_historical_n_sum_eq_canonical_z_fibres434
      e m mp J (F mp)
    exact hZ.symm.trans (hFibre.symm.trans hN)
  calc
    _ = ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
        ∑n∈J.filter (parityOriginalHistoricalUngatedPhysicalValidN434
          d L band slot delta Y e m mp),F mp n := by
      apply Finset.sum_congr rfl
      intro mp hmp
      exact hMP mp
    _ = ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
       d L band slot delta Y e m K J k,F q.1 q.2 := by
      unfold parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      simp only [Finset.sum_filter]
      exact (Finset.sum_product
        (parityOriginalHistoricalKPrimeFibre434 e m K k) J
        (fun q : ℕ×ℕ => if parityOriginalHistoricalUngatedPhysicalValidN434
          d L band slot delta Y e m q.1 q.2 then F q.1 q.2 else 0)).symm
    _ = _ := rfl

/-- The EXACT original natural full-odd post-Cauchy offdiagonal with
eta_e(e/E) eta_n(n/V) is the complete original k/(m',n) physical
source, before adding the true C-infinity psi partition or truncating
Fourier. No P-free-e mask survives positive Cauchy enlargement. -/
theorem parity_original_ungated_cauchy_od_eq_full_odd_physical_events434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K EF J : Finset ℕ) (alpha : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ)
    (hOdd : ∀e∈EF,Odd e) :
    parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
      d L band slot delta freq rho K EF J alpha signed Y w =
    ∑e∈EF,∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
          d L band slot delta Y e m K J k,
          ((w e q.2:ℝ):ℂ)*
          parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot delta freq rho alpha signed Y e q.2 m q.1 := by
  classical
  rw [parity_original_historical_ungated_weighted_full_odd_offdiag_k_z_exact434
    d L band slot delta freq rho K EF J alpha signed Y w hOdd]
  unfold parityOriginalHistoricalUngatedWeightedExtendedPhysicalKZ434
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  exact parity_original_ungated_cauchy_k_physical_event_exact434
    d L band slot delta freq rho alpha signed Y e m K J k w
end Green64Analytic.Parity

end

end

/-! ## CauchyODTruePsiSourceJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- EXACT identification of the full, true original Parity (4.10)
post-Cauchy all-odd-e complex offdiagonal with the complete
SOURCE-CONSTRUCTED smooth ψ physical outer. First the natural
n→canonical z physical fibre is reindexed with no multiplicities,
then the genuine C∞ ψ and its TWO attained dyadic neighbors are
inserted as an exact partition of unity. Neither signed-subset
monotonicity nor P-free e or the old incorrect u cap is used.
This is the full SOURCE bridge needed to apply paid true-ψ Fourier
tail directly to the Cauchy Gram, but not yet Parity (4.17) saving. -/
theorem parity_original_capfree_Cauchy_OD_eq_true_psi_global_source434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox) (hUV : Real.exp L≤U*V)
    (hUVhi : U*V≤Cbox*Real.exp L) (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let hLw : 8≤L := by linarith
    let Y := Nat.ceil (6*U*V)
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hLw band slot delta Y K
    let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V hLw band slot delta Y K)
    parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
      d L band slot delta freq rho K EF J alpha signed Y
      (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw) =
    parityOriginalActualTruePsiGlobalPhysicalSource434
      d L E V hLw band slot delta freq rho alpha signed Y K KS ZS := by
  classical
  have hLw : 8≤L := by linarith
  let Y := Nat.ceil (6*U*V)
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K)
  have hOdd : ∀e∈EF, Odd e := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hReindex := parity_original_ungated_cauchy_od_eq_full_odd_physical_events434
    d L band slot delta freq rho K EF J alpha signed Y
    (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw) hOdd
  have hPsi := parity_original_ungated_true_psi_physical_source_outer_exact434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta freq rho K alpha signed hDyad
  dsimp only at hReindex hPsi ⊢
  exact hReindex.trans hPsi
end Green64Analytic.Parity

end

end

/-! ## TruePsiActualOriginalTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- SOURCE-TRUE original full-odd Parity(4.10) post-Cauchy physical
signed h=-2 offdiagonal is approximated by its complete ORIGINAL
smooth ψ(Z) Fourier BALL on all actual signed k and BOTH true
neighboring dyads, with the real η-ACTIVE carrier selected BEFORE
truncation. Its high-frequency tail has an UNCONDITIONAL source
bound in terms of ONE original positive diagonal:

 ||OD_original - Lowfreq_eta_active|| ≤
 (C_H L^[5(K0+90)(H+P+1)]/T^H)
   × 2(2 ceil L^(K0+89)+1) × D_original.

Every external band/slot/Q allocation, Fourier ξ and fine α is
fixed but arbitrary. The k/Z carriers, Ybox=ceil6UV, original
η_eη_n, H0/W1/epsilon and two smooth ψ dyads are genuine
SOURCE-DERIVED. There is no hidden χ multiplicity, post-Fourier
hard filter, or e,m,n,z exponential factor. The low-frequency ball
on this statement is ETA-ACTIVE and still must be joined to the
unrestricted B633 Eq(4.17) Fourier source-image; do not assert TypeII. -/
theorem parity_original_true_smooth_post_cauchy_eta_active_tail_le_diagonal434
    (d : ℕ) (L U V E K0 Cbox A R : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox) (hUV : Real.exp L≤U*V)
    (hUVhi : U*V≤Cbox*Real.exp L) (hE : E=U*L^(-K0))
    (hLargeC : 6*Cbox≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (buf : ℝ → ℂ) (hA : 0<A) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (H : ℕ)
    (hLargeE : 2*A*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
      (2:ℝ)^(H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
      ((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (hR : 1≤R)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (T : ℝ) (hT : 0<T) :
    let hLw : 8≤L := by linarith
    let Y := Nat.ceil (6*U*V)
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hLw band slot δ Y K
    let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V hLw band slot δ Y K)
    let N := Nat.ceil (L^(K0+89))
    let D := parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
      d L band slot δ ξ rho K EF J alpha signed Y
    let C := parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hSmooth hSupport H
    ‖(∑e∈EF,∑m∈K,
        ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
          ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot δ Y e m K J k,
            (((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ) *
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho alpha signed Y e q.2 m q.1)) -
      parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
        d L U E V hLw band slot δ ξ rho alpha signed Y K KS ZS
        buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ ≤
      ((C*L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)))/T^H)*
        (2*((2*N+1:ℕ):ℝ)*D) := by
  classical
  have hLw : 8≤L := by linarith
  let Y := Nat.ceil (6*U*V)
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot δ Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot δ Y K)
  let N := Nat.ceil (L^(K0+89))
  have hEpos : 0<E := by rw [hE]; positivity
  have hK : ∀k∈KS,k≠0 ∧ k.natAbs≤N := by
    intro k hk
    have hh := parity_original_full_odd_smoothed_k_genuine_polylog434
      d L U E V K0 hLw hU hE band slot δ Y K hDyad k hk
    exact ⟨hh.1,hh.2.2⟩
  have hZS : ∀Z∈ZS,0<Z ∧
      (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88) ∧
      (∃j:ℕ,Z=(2:ℕ)^j) := by
    intro Z hz
    have hh := parity_original_full_odd_true_smooth_neighbor_Z_box_window434
      d L U V E K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
      band slot δ K hDyad Z hz
    have hPos : (0:ℝ)<(Z:ℝ) := by
      have hb : 0<(Real.exp L/64)*L^K0 := by positivity
      exact hb.trans hh.1
    have hBin := parity_original_full_odd_true_smooth_neighbor_Z_index_capacity434
      d L U V E K0 Cbox hL hK0 hCbox hU hV hUV hUVhi hE
      band slot δ K hDyad Z hz
    exact ⟨by exact_mod_cast hPos,hh.2.le,⟨hBin.choose,hBin.choose_spec.2⟩⟩
  have hSource := parity_original_ungated_true_psi_physical_source_outer_exact434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot δ ξ rho K alpha signed hDyad
  have hTail := parity_original_true_psi_eta_active_global_source_tail_le_diagonal434
    d L U E V K0 Cbox A R hLw hK0 hU hV hUV hE (by linarith : 0≤Cbox) hLargeC
    band slot δ ξ rho K alpha signed Y KS ZS N hK
    (fun Z hz=>(hZS Z hz).1)
    (fun Z hz=>(hZS Z hz).2.1)
    (fun Z hz=>(hZS Z hz).2.2)
    (fun mp hmp=>⟨(hDyad mp hmp).1,(hDyad mp hmp).2.le⟩)
    buf hA hSmooth hSupport hOne4 H hLargeE hLargeN hR hCube T hT
  dsimp only at hTail hSource ⊢
  rw [hSource]
  exact hTail
end Green64Analytic.Parity

end

end

/-! ## TruePsiActualOriginalTailAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- SOURCE-CORRECT ORIGINAL Parity(4.10)--(4.15) complete cap-free signed
post-Cauchy offdiagonal versus true C-infinity ψ, η-active global
3-dimensional Fourier ball. For EVERY fixed inverse-log goal D≥0,
ONE polynomial cutoff T=L^[5(K0+90)(P+2)+(K0+89)+2*C_W1+256+D]
is chosen after the source constants and before L. The high-frequency
error is <= 8 C_1 Acoef² exp(L) L^-D, with no #e, #n, #m, #chi,
#z or hard-binary dyad loss. Unlike the older artificial Y0 source,
the actual cap is Ybox=ceil(6UV), every odd e survives and BOTH
smooth dyadic ψ neighbors are included. This is only the tail;
the low-frequency true η-active ball still requires its exact
identification with the full source Parity(4.17) signal. -/
theorem parity_eventually_original_true_psi_post_cauchy_eta_active_tail_any_log434
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
      let hLw : 8≤L := by linarith
      let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
      let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
      let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
      let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
      let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      let Y := Nat.ceil (6*U*V)
      let EF := parityOriginalHistoricalFullOddEEnvelope434 E
      let J := parityOriginalHistoricalFullNEnvelope434 V
      let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
        (sourceOriginalLiteralDepth 20 L) L E V hLw band slot delta Y K
      let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
        (parityOriginalHistoricalFullOddOriginalZUnion434
          (sourceOriginalLiteralDepth 20 L) L E V hLw band slot delta Y K)
      ‖(∑e∈EF,∑m∈K,
          ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
            ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
              (sourceOriginalLiteralDepth 20 L) L band slot delta Y e m K J k,
              (((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ) *
                parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                  (sourceOriginalLiteralDepth 20 L) L band slot delta freq
                  rho alpha signed Y e q.2 m q.1)) -
        parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
          (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot delta
          freq rho alpha signed Y K KS ZS buf
          (-Real.log A) (Real.log A) T hSmooth hSupport‖ ≤
        8*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by
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
    rho K alpha signed Acoef hAcoef hAlpha hDyad Dgoal hD
  classical
  let hLw : 8≤L := by linarith
  let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
  let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
  let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
  let C1 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Y := Nat.ceil (6*U*V)
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    (sourceOriginalLiteralDepth 20 L) L E V hLw band slot delta Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      (sourceOriginalLiteralDepth 20 L) L E V hLw band slot delta Y K)
  let D0 := parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
    (sourceOriginalLiteralDepth 20 L) L band slot delta freq rho K EF J alpha signed Y
  have hLp : 0<L := by linarith
  have hT : 0<T := Real.rpow_pos_of_pos hLp _
  have hC1 : 0≤C1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hD0 := hDiag.2 U V hU.le hV.le hUVhi band slot delta freq rho
    K EF J alpha signed Acoef hAcoef hAlpha
  have hQ : 0≤C1*L^X/T := by positivity
  have hX : X=(5*(K0+90))*(((1+P:ℕ):ℝ)+1) := by
    dsimp [X]
    push_cast
    ring
  have hTail := parity_original_true_smooth_post_cauchy_eta_active_tail_le_diagonal434
    (sourceOriginalLiteralDepth 20 L) L U V E K0 Cbox A R hL hK0
    hU hV hCbox hUV hUVhi hE hLargeC band slot delta freq
    rho K alpha signed hDyad buf hA hSmooth hSupport hOne4 1
    (by simpa only [J1] using hBE)
    (by simpa only [J1] using hBN) hR hCube T hT
  dsimp only at hTail ⊢
  rw [←hX] at hTail
  have hNum := parity_original_historical_ungated_full_odd_global_tail_power_numeric434
    L K0 X M Dgoal C1 Acoef hLw hK0 hC1
  have hBoundDiag : D0≤Acoef^2*Real.exp L*L^M := by
    simpa only [D0,M,EF,J,Y] using hD0
  have hDegree : (0:ℝ)≤((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ) := by positivity
  have hPositive : 0≤C1*L^X/T := by positivity
  have hReduced :
      (C1*L^X/T)*(((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ)*D0) ≤
      (C1*L^X/T)*(((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ)*
        (Acoef^2*Real.exp L*L^M)) := by
    apply mul_le_mul_of_nonneg_left _ hPositive
    exact mul_le_mul_of_nonneg_left hBoundDiag hDegree
  have hConcl :
      (C1*L^X/T)*(2*(((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ)*D0)) ≤
      8*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by
    have hNumeric' :
        (C1*L^X/T)*(((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ)*
          (Acoef^2*Real.exp L*L^M)) ≤
          4*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by
      simpa only [T] using hNum
    calc
      _ = 2*((C1*L^X/T)*(((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ)*D0)) := by ring
      _ ≤ 2*((C1*L^X/T)*(((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ)*
          (Acoef^2*Real.exp L*L^M))) :=
        mul_le_mul_of_nonneg_left hReduced (by norm_num)
      _ ≤ 2*(4*C1*Acoef^2*Real.exp L*L^(-Dgoal)) :=
        mul_le_mul_of_nonneg_left hNumeric' (by norm_num)
      _ = _ := by ring
  refine hTail.trans ?_
  calc
    _ = (C1*L^X/T)*(2*(((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ)*D0)) := by ring
    _ ≤ _ := hConcl
end Green64Analytic.Parity

end

end

/-! ## CauchyODTruePsiTailAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Complete ORIGINAL cap-free Parity(4.10) weighted Cauchy offdiagonal
OD (not merely an isolated physical source) differs from its exactly
source-compatible eta-active actual smooth ψ global Fourier ball by
<=8*C1*Acoef²*exp(L)*L^-D for any prescribed D>=0. This joins
an exact n->z source-multiplicity Fubini, real smooth ψ partition,
nonnegative Cauchy diagonal, source Schwartz moment, and globally
paid Fourier tail. Does not compare truncated complex subsets or
assert the unresolved full lowfrequency Eq4.17 use-site equality. -/
theorem parity_eventually_original_capfree_Cauchy_OD_eta_active_ball_tail_any_log434
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
      let hLw : 8≤L := by linarith
      let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
      let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
      let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
      let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
      let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      let Y := Nat.ceil (6*U*V)
      let EF := parityOriginalHistoricalFullOddEEnvelope434 E
      let J := parityOriginalHistoricalFullNEnvelope434 V
      let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
        (sourceOriginalLiteralDepth 20 L) L E V hLw band slot delta Y K
      let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
        (parityOriginalHistoricalFullOddOriginalZUnion434
          (sourceOriginalLiteralDepth 20 L) L E V hLw band slot delta Y K)
      ‖parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
          (sourceOriginalLiteralDepth 20 L) L band slot delta freq rho K EF J
          alpha signed Y (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw) -
        parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
          (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot delta
          freq rho alpha signed Y K KS ZS buf
          (-Real.log A) (Real.log A) T hSmooth hSupport‖ ≤
        8*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by
  have hTail := parity_eventually_original_true_psi_post_cauchy_eta_active_tail_any_log434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  filter_upwards [hTail] with L hTailL
  refine ⟨hTailL.1,hTailL.2.1,?_⟩
  intro hL U V E hU hV hUV hUVhi hE
    band slot delta freq rho K alpha signed Acoef hAcoef hAlpha hDyad
    Dgoal hD
  have hErr := hTailL.2.2 hL U V E hU hV hUV hUVhi hE
    band slot delta freq rho K alpha signed Acoef hAcoef hAlpha hDyad Dgoal hD
  have hEq := parity_original_capfree_Cauchy_OD_eq_true_psi_global_source434
    (sourceOriginalLiteralDepth 20 L) L U E V K0 Cbox hL hK0
    hU hV hCbox hUV hUVhi hE band slot delta freq rho K alpha signed hDyad
  have hPsi := parity_original_ungated_true_psi_physical_source_outer_exact434
    (sourceOriginalLiteralDepth 20 L) L U E V K0 Cbox hL hK0
    hU hV hCbox hUV hUVhi hE band slot delta freq rho K alpha signed hDyad
  dsimp only at hErr hEq hPsi ⊢
  rw [hPsi] at hErr
  rw [hEq]
  exact hErr
end Green64Analytic.Parity

end

end

/-! ## OriginalCapfreeCauchyBallPrecursor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- SOURCE-CORRECT original Parity (4.10) cap-free positive Cauchy
precursor DIRECTLY controlled by the ACTUAL true smooth ψ η-active
3D Fourier ball, plus the original positive diagonal and a fully
paid global O_A(exp(L)L^-A) high-frequency error. The selected Q
a_e beta_n energy stays EXACTLY outside the square, and the
positive Cauchy enlargement permits ALL odd e, including P-group
factors. Neither a complex signed-subset inequality nor any
unproved Type II input is used. The remaining gap is the exact
eta-active Fourier ball -> unrestricted Eq4.17 source saving over
all Q/fine/allocation families; this theorem does not assert TypeII. -/
theorem parity_eventually_original_capfree_Bprime_Cauchy_true_psi_ball_precursor434
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
      ‖Bp‖^2 ≤ Wout *
        (2*Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+344) +
         ‖parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
           d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
           buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ +
         8*C1*Acoef^2*Real.exp L*L^(-Dgoal)) := by
  have hPrec := parity_eventually_original_capfree_Bprime_Cauchy_box_precursor434 Cbox hCbox
  have hTail := parity_eventually_original_capfree_Cauchy_OD_eta_active_ball_tail_any_log434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  filter_upwards [hPrec,hTail] with L hPrecL hTailL
  refine ⟨hTailL.1,hTailL.2.1,?_⟩
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
  let OD := parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
    d L band slot delta freq rho K EF Nfull alpha signed Y
    (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw)
  let Ball := parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
    d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
    buf (-Real.log A) (Real.log A) T hSmooth hSupport
  let Wout := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
    d L E band slot delta,
    ∑n∈J,‖parityOriginalHistoricalWindowAE434
      d L E band slot delta freq rho e*beta n‖^2
  have hEpos : 0<E := by rw [hE]; positivity
  have hPrecBound := hPrecL.2.2 hLw U V E hU hV hUVhi hEpos band slot
    delta freq rho K J alpha beta signed Acoef
    (fun m hm=>⟨(hDyad m hm).1,(hDyad m hm).2⟩)
    hJ hAcoef hAlpha
  have hTailBound := hTailL.2.2 hL U V E hU hV hUV hUVhi hE band slot
    delta freq rho K alpha signed Acoef hAcoef hAlpha hDyad Dgoal hD
  dsimp only at hPrecBound hTailBound ⊢
  have hOuter : 0≤Wout := by
    dsimp [Wout]
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hOD : ‖OD‖≤‖Ball‖+8*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by
    calc
      ‖OD‖ = ‖(OD-Ball)+Ball‖ := by ring
      _ ≤ ‖OD-Ball‖+‖Ball‖ := norm_add_le _ _
      _ ≤ (8*C1*Acoef^2*Real.exp L*L^(-Dgoal))+‖Ball‖ :=
        add_le_add_left hTailBound _
      _ = _ := by ring
  have hAdd :
      2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)+‖OD‖ ≤
      2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)+
        ‖Ball‖+8*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by linarith
  have hFinal := hPrecBound.trans (mul_le_mul_of_nonneg_left hAdd hOuter)
  exact hFinal
end Green64Analytic.Parity

end

end

/-! ## TruePsiZeroEtaGhostPaid -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The TRUE ORIGINAL unfiltered C∞ ψ physical Fourier BALL and the
η-ACTIVE-BEFORE-TRUNCATION Fourier BALL differ by at most TWO explicit
positive source coefficient-mass × genuine Schwartz Fourier tails.

This is a correct spectral ghost payment: physical η_e(e/E)η_n(n/V)
may vanish although the truncated complex Fourier inversion still
has a nonzero contribution. We do NOT infer norm monotonicity of
complex subsums, pointwise χ-vanishing, or source P-free-e.

The original natural full-odd e,n,m,m',z source, physical H0/W1,
actual signed ε, full k support, and all genuine C∞ dyadic ψ pieces
are preserved. This theorem quantifies every source input and
holds before invoking the specialized Parity(4.17) correlation saving. -/
theorem parity_original_actual_true_psi_zero_eta_spectral_ghost_two_paid434
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
    ‖Full-Active‖ ≤ FullMass+ActiveMass := by
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
  have hFull := parity_original_actual_true_psi_global_physical_ball_error_le_mass434
    d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
    hU hE hV hDyad hZpos buf a b hSmooth hSupport hOne4 H T hT
  have hActive := parity_original_actual_true_psi_eta_active_global_physical_ball_error_le_mass434
    d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
    hU hE hV hDyad hZpos buf a b hSmooth hSupport hOne4 H T hT
  dsimp only at hFull hActive ⊢
  change ‖Src-Full‖≤FullMass at hFull
  change ‖Src-Active‖≤ActiveMass at hActive
  change ‖Full-Active‖≤FullMass+ActiveMass
  have hAlgebra : Full-Active=(Src-Active)-(Src-Full) := by ring
  rw [hAlgebra]
  calc
    ‖(Src-Active)-(Src-Full)‖ ≤ ‖Src-Active‖+‖Src-Full‖ := norm_sub_le _ _
    _ ≤ ActiveMass+FullMass := add_le_add hActive hFull
    _ = FullMass+ActiveMass := add_comm _ _
end Green64Analytic.Parity

end

end

/-! ## TrueYboxShiftedTauMass -/

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
Ybox=ceil(6UV), for all physical U,V with exp L<=UV<=Cbox exp L.
No extension by pointwise s cutoff: this is an independent
POSITIVE arithmetic estimate from the genuine fourth divisor moment.
Its exponent 16 is fixed before TypeII precision; Cbox affects only
the eventual lower threshold for L. -/
theorem parity_eventually_original_true_Ybox_shifted_tau_square_polylog434
    (Cbox : ℝ) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop,
      1≤L ∧ ∀ (U V : ℝ),
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
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
  intro U V hU hV hUV hUVhi
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
theorem parity_eventually_original_true_Ybox_W1_shifted_tau_polylog434
    (Cbox : ℝ) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop,
      1≤L ∧ ∀ (U V : ℝ),
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
      let Y := Nat.ceil (6*U*V)
      (∑u∈Finset.Ioc 0 Y,
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) ≤
        Real.exp L*L^parityOriginalW1PolylogExponent434*L^16 := by
  filter_upwards [parity_eventually_original_true_Ybox_shifted_tau_square_polylog434
      Cbox hCbox,
    parity_eventually_original_actual_W1_pointwise_polylog434]
    with L hMoment hW1
  refine ⟨hMoment.1,?_⟩
  intro U V hU hV hUV hUVhi
  let Y := Nat.ceil (6*U*V)
  have hL : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hMoment.1
  have hWpos : 0≤L^parityOriginalW1PolylogExponent434 := by positivity
  have hFirst := parity_original_shift_two_tau_first_le_second_moment434 Y
  have hSecond := hMoment.2 U V hU hV hUV hUVhi
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

