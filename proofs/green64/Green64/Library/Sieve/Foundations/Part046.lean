module

public import Green64.Library.Sieve.Foundations.Part043
public import Green64.Library.Sieve.Foundations.Part041
public import Green64.Library.Sieve.Foundations.Part045
public import Green64.Library.Sieve.Foundations.Part040
public import Green64.Library.Sieve.Foundations.Part042
public import Green64.Library.Sieve.Foundations.Part007
public import Green64.Library.Sieve.Foundations.Part032
public import Green64.Library.Sieve.Foundations.Part038

@[expose] public section

/-!
# Sieve / Foundations / Part046

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## QuarterZeroEtaBallMassBridge -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Source-exact comparison of actual full and eta-active Fourier
balls with twice the ORIGINAL positive ghost coefficient mass.
This is uniform in the original signed k, two smooth neighbouring
Z-scales, actual e,n,m,m' and all Q/P allocations. No signed
complex subset monotonicity is used. -/
theorem parity_original_true_psi_zero_eta_full_active_ball_le_mass434
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
    ‖parityOriginalActualTruePsiGlobalPhysicalBall434
        d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
        buf a b T hSmooth hSupport -
      parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
        d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
        buf a b T hSmooth hSupport‖ ≤
    2*parityOriginalActualTruePsiGlobalPositiveGhostMass434
      d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
      buf a b hSmooth hSupport H T := by
  have hh := parity_original_actual_true_psi_zero_eta_spectral_ghost_double_full_mass434
    d L U E V hL band slot delta freq rho alpha signed Y K KS ZS
    hU hE hV hDyad hZpos buf a b hSmooth hSupport hOne4 H T hT
  simpa only [parityOriginalActualTruePsiGlobalPositiveGhostMass434] using hh
end Green64Analytic.Parity

end

end

/-! ## QuarterZeroEtaBallAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Actual source full-minus-eta-active lowfrequency Fourier ball
has arbitrary inverse-log saving on the genuine quarter U*V dyads.
Both ghosts paid as a source positive mass; no signed subset trick. -/
theorem parity_eventually_original_true_psi_zero_eta_full_active_ball_any_log_quarter434
    (K0 Cbox A R : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
      ∀ (hL : 128≤L) (U V E : ℝ),
      0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
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
      let d := sourceOriginalLiteralDepth 20 L
      let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
        (sourceOriginalLiteralDepth 20 L) L E V hLw band slot delta Y K
      let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
        (parityOriginalHistoricalFullOddOriginalZUnion434
          (sourceOriginalLiteralDepth 20 L) L E V hLw band slot delta Y K)
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
            L hLw U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
          parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
            (parityOriginal3DSourceMomentFiniteBudget434 1 f/T^1)
        else 0
      ‖parityOriginalActualTruePsiGlobalPhysicalBall434
        d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
        buf (-Real.log A) (Real.log A) T hSmooth hSupport -
      parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
        d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
        buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ ≤
      16*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by
  have hMass := parity_eventually_original_true_psi_zero_eta_two_ghost_any_log_quarter434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  filter_upwards [hMass] with L hh
  rcases hh with ⟨h128,h6,hRest⟩
  refine ⟨h128,h6,?_⟩
  intro hL U V E hU hV hUV hUVhi hE band slot delta freq
    rho K alpha signed Acoef hAcoef hAlpha hDyad Dgoal hD
  have hBound := hRest hL U V E hU hV hUV hUVhi hE band slot delta freq
    rho K alpha signed Acoef hAcoef hAlpha hDyad Dgoal hD
  let hLw : 8≤L := by linarith
  let Y := Nat.ceil (6*U*V)
  let d := sourceOriginalLiteralDepth 20 L
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K)
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
  let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
  let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
  have hEpos : 0<E := by rw [hE]; positivity
  have hTpos : 0<T := by dsimp [T]; positivity
  have hClosed : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U := by
    intro m hm
    exact ⟨(hDyad m hm).1,(hDyad m hm).2.le⟩
  have hZpos : ∀Z∈ZS,0<Z := by
    intro Z hz
    have hZR := parity_original_full_odd_true_smooth_neighbor_Z_box_window_quarter434
      d L U V E K0 Cbox hL hK0 hU hV (by linarith : 1≤Cbox)
      hUV hUVhi hE band slot delta K hDyad Z hz
    have hp : 0<(Real.exp L/256)*L^K0 := by positivity
    have hCast : (0:ℝ)<(Z:ℝ) := hp.trans hZR.1
    exact_mod_cast hCast
  have hBridge := parity_original_true_psi_zero_eta_full_active_ball_le_mass434
    d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
    hU hEpos hV hClosed hZpos buf (-Real.log A) (Real.log A)
    hSmooth hSupport hOne4 1 T hTpos
  dsimp only at hBound hBridge ⊢
  exact hBridge.trans (by
    simpa only [parityOriginalActualTruePsiGlobalPositiveGhostMass434,
      pow_one, d,Y,KS,ZS,T,X,M,P] using hBound)
end Green64Analytic.Parity

end

end

/-! ## TruePhysicalSmoothPsiReindexQuarter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6300000

/-- The original η_e,L(e/E)η_n(n/V) weighted full-odd B509 physical
Cauchy pair at fixed e,m,k has an exact smooth-ψ source partition
with NO external weight-support or physical z-range assumptions.
The original full n envelope, cap-free Ybox=ceil(6UV), actual H0,
α,epsilon and natural u/e remain literal. The sole dyadic capacity
hypothesis is the elementary 2^(N+1) upper bound for the REAL
corrected source z-height; its explicit N is constructed next. -/
theorem parity_original_full_odd_actual_weight_smooth_psi_neighbor_reindex_quarter434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V) (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (e m : ℕ) (k : ℤ) (N : ℕ)
    (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E)
    (hm : m∈K) (hk : k∈parityOriginalHistoricalNonzeroKSupport434 e m K)
    (hCapacity : 48*Cbox*Real.exp L*L^(K0+88)≤(2:ℝ)^(N+1)) :
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Y := Nat.ceil (6*U*V)
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V (by linarith : 8≤L) band slot δ Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
    let W : ℕ×ℕ → ℂ := fun q =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V (by linarith : 8≤L) e q.2:ℝ):ℂ)*
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1
    (∑q∈S,W q) =
      ∑j∈(Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈ZSmooth),
        ∑q∈S,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*W q := by
  classical
  have hLw : 8≤L := by linarith
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := Nat.ceil (6*U*V)
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let W : ℕ×ℕ → ℂ := fun q =>
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho alpha signed Y e q.2 m q.1
  have hW (q : ℕ×ℕ) (hq : q∈S) (hNZ : W q≠0) :
      parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2≠0 := by
    intro hzero
    apply hNZ
    dsimp [W]
    simp [hzero]
  have hLone : 1≤L := by linarith
  have hKone : 1≤L^K0 := Real.one_le_rpow hLone hK0
  have hExpLarge : (128:ℝ)≤Real.exp L := by
    have hh := Real.add_one_le_exp L
    linarith
  have hZrange (q : ℕ×ℕ) (hq : q∈S) (hNZ : W q≠0) :
      (2:ℝ)≤(parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ) ∧
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)≤(2:ℝ)^(N+1) := by
    have hw := hW q hq hNZ
    have hdata := Finset.mem_filter.mp hq
    have hprod := Finset.mem_product.mp hdata.1
    have hmpK := (Finset.mem_erase.mp (Finset.mem_filter.mp hprod.1).1).2
    have hneq : m≠q.1 :=
      (Finset.mem_erase.mp (Finset.mem_filter.mp hprod.1).1).1.symm
    have hOdd : Odd e := (Finset.mem_filter.mp he).2
    have hPhys := parity_original_historical_ungated_physical_valid_k_z434
      d L band slot δ Y e m q.1 q.2 hOdd hneq hdata.2
    dsimp only at hPhys
    let z := parityOriginalHistoricalCanonicalZ434 e m q.1 q.2
    let Z : ℕ := parityOriginalHistoricalActualZDyadicScale434 z
    have hzpos : 0<z := hPhys.2.1
    have hqZ : q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z := by
      apply Finset.mem_filter.mpr
      exact ⟨hdata.1,⟨hdata.2,hzpos,rfl⟩⟩
    have hzBound := parity_original_historical_ungated_full_box_smoothed_actual_Z_window_quarter434
      d L U V E K0 Cbox (by linarith : 32≤L) band slot δ K J e m k Z
      hOdd hU hV (by linarith : 0<Cbox) hUV hUVhi hE hm hDyad q hqZ hw
    have hdy := parity_original_historical_actual_z_in_own_dyad434 z hzpos
    have hzRealLow : (Z:ℝ)≤(z:ℝ) := by exact_mod_cast hdy.2.1
    have hzRealHigh : (z:ℝ)<2*(Z:ℝ) := by exact_mod_cast hdy.2.2
    have hLBound : (2:ℝ)≤(Real.exp L/64)*L^K0 := by
      have hExp16 : (2:ℝ)≤Real.exp L/64 := by linarith
      have hePos : 0≤Real.exp L/64 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hKone hePos]
    have hTop : (z:ℝ)≤(2:ℝ)^(N+1) := by
      calc
        _ ≤ 2*(Z:ℝ) := hzRealHigh.le
        _ ≤ 48*Cbox*Real.exp L*L^(K0+88) := by
          nlinarith [hzBound.2]
        _ ≤ (2:ℝ)^(N+1) := hCapacity
    exact ⟨by linarith [hLBound,hzBound.1,hzRealLow],hTop⟩
  have hF := parity_original_true_physical_full_smooth_dyadic_source_neighbor_reindex434
    d L E V hLw band slot δ Y e m K J k N W he hm hk
    (Finset.Subset.rfl) hW hZrange
  dsimp only at hF ⊢
  exact hF
end Green64Analytic.Parity

end

end

/-! ## TruePhysicalPsiExplicitCapacityQuarter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The entire original C-infinity ψ decomposition of one physical
post-Cauchy (e,m,k) fibre, with the real original eta_e(e/E)eta_n(n/V)
and full-odd e carrier, using a canonical N(L) fixed from source
geometry alone. No assumed dyadic capacity or artificial sharp ψ mask.
The filtered j are precisely the physically attained true smooth
neighbor scales; no character-wise or complex-subsummand inequality. -/
theorem parity_original_full_odd_actual_weight_smooth_psi_explicit_capacity_quarter434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V) (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (e m : ℕ) (k : ℤ)
    (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E)
    (hm : m∈K) (hk : k∈parityOriginalHistoricalNonzeroKSupport434 e m K)
    :
    let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Y := Nat.ceil (6*U*V)
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V (by linarith : 8≤L) band slot δ Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
    let W : ℕ×ℕ → ℂ := fun q =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V (by linarith : 8≤L) e q.2:ℝ):ℂ)*
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1
    (∑q∈S,W q) =
      ∑j∈(Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈ZSmooth),
        ∑q∈S,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*W q := by
  exact parity_original_full_odd_actual_weight_smooth_psi_neighbor_reindex_quarter434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot δ ξ rho K alpha signed hDyad
    e m k (parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox)
    he hm hk (parity_original_true_smooth_dyadic_capacity434 L K0 Cbox)
end Green64Analytic.Parity

end

end

/-! ## QuarterSmoothOriginalEMKOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- EXACT full original h=-2 B' post-Cauchy weighted physical source
outer e,m,k with ALL original odd e, all Q/P/B509 two-endpoint source
support, original H0/W1/epsilon and fine alpha. The true eta_e eta_n
weights on natural e,n are not changed. An explicit dyadic capacity
N(L) is chosen from source data before the sum. Inserting the complete
fixed C∞ ψ(z/2^j) dyadic partition and restricting j to exactly the
attained physical binary heights or immediately preceding half-heights
is an IDENTITY of complex sums, not an upper bound of signed subsums.
This is the genuine GLOBAL e/m/k source smoothization; it does not
by itself identify the Fourier integral of the full physical outer. -/
theorem parity_original_full_odd_actual_weight_complete_emk_smooth_psi_outer_quarter434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let hLw : 8≤L := by linarith
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Y := Nat.ceil (6*U*V)
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
    let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
      parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K J k
    let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e q.2 m q.1
    (∑e∈EF,∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      ∑q∈S e m k, W e m k q) =
    (∑e∈EF,∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      ∑j∈(Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈ZSmooth),
        ∑q∈S e m k,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
          W e m k q) := by
  classical
  have hLw : 8≤L := by linarith
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := Nat.ceil (6*U*V)
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Y K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
  let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
  let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K J k
  let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1
  dsimp only
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  have hCell := parity_original_full_odd_actual_weight_smooth_psi_explicit_capacity_quarter434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta freq rho K alpha signed hDyad
    e m k he hm hk
  dsimp only at hCell ⊢
  exact hCell
end Green64Analytic.Parity

end

end

/-! ## QuarterRawKOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The complete original full-odd physical source e,m,k,m',n
complex B' offdiagonal, with its genuine eta_e eta_n and C∞ ψ,
is EXACTLY grouped by global original physically-derived SIGNED k
with all e,m,q multiplicities retained in the new inner sum. The
outer k union is the literal source union (not an analytic window
or the smaller smoothed nonzero k carrier). This is a true algebraic
bridge toward identifying the globally smoothed Fourier source;
it neither applies a signed-subsum inequality nor claims TypeII. -/
theorem parity_original_full_odd_actual_weight_global_raw_k_smooth_psi_outer_quarter434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let hLw : 8≤L := by linarith
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Y := Nat.ceil (6*U*V)
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
    let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
    let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
      parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K J k
    let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e q.2 m q.1
    (∑e∈EF,∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      ∑q∈S e m k, W e m k q) =
    (∑k∈KG,∑j∈(Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈ZSmooth),
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈S e m k,
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
            W e m k q
        else 0) := by
  classical
  have hLw : 8≤L := by linarith
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := Nat.ceil (6*U*V)
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Y K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
  let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
  let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
  let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K J k
  let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1
  let T : Finset ℕ := (Finset.range (N+1)).filter
    (fun j => (2:ℕ)^j∈ZSmooth)
  let F : ℕ → ℕ → ℤ → ℕ → ℂ := fun e m k j =>
    ∑q∈S e m k,
      parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
      W e m k q
  have hk : ∀ e∈EF, ∀ m∈K,
      parityOriginalHistoricalNonzeroKSupport434 e m K ⊆ KG := by
    intro e he m hm k hk
    change k∈(EF.biUnion fun e => K.biUnion fun m =>
      parityOriginalHistoricalNonzeroKSupport434 e m K)
    exact Finset.mem_biUnion.mpr ⟨e,he,Finset.mem_biUnion.mpr ⟨m,hm,hk⟩⟩
  have hSmooth := parity_original_full_odd_actual_weight_complete_emk_smooth_psi_outer_quarter434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta freq rho K alpha signed hDyad
  have hKFubini := parity_original_finite_smooth_dyadic_k_outer_fubini434
    EF K (fun e m => parityOriginalHistoricalNonzeroKSupport434 e m K)
    KG T F hk
  dsimp only at hSmooth hKFubini ⊢
  exact hSmooth.trans hKFubini
end Green64Analytic.Parity

end

end

/-! ## QuarterSmoothedKOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 7400000

/-- The original entire weighted all-odd physical Cauchy
(e,m,k,m',n) complex source with genuine eta_e/n and smooth ψ is
EXACTLY reindexed by its ACTUAL NONZERO-ETA signed KSm carrier,
not the much larger unweighted odd-e quotient set. All zero-
weight raw k fibres vanish literally before Fourier truncation,
not by a false norm comparison of signed subsums. Physical source
k and ψ carry their full original multiplicities and no #character
or Pfree-e assumptions. The full Parity TypeII and source frequency
allocation family integration are not asserted here. -/
theorem parity_original_full_odd_actual_weight_global_smoothed_k_psi_outer_quarter434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let hLw : 8≤L := by linarith
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Y := Nat.ceil (6*U*V)
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
    let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
    let KSm := parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hLw band slot delta Y K
    let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
      parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K J k
    let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e q.2 m q.1
    (∑e∈EF,∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      ∑q∈S e m k, W e m k q) =
    (∑k∈KSm,∑j∈(Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈ZSmooth),
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈S e m k,
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
            W e m k q
        else 0) := by
  classical
  have hLw : 8≤L := by linarith
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := Nat.ceil (6*U*V)
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Y K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
  let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
  let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
  let KSm := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K J k
  let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1
  let T : Finset ℕ := (Finset.range (N+1)).filter
    (fun j => (2:ℕ)^j∈ZSmooth)
  let F : ℤ → ℂ := fun k =>
    ∑j∈T, ∑e∈EF, ∑m∈K,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        ∑q∈S e m k,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
          W e m k q
      else 0
  have hRaw := parity_original_full_odd_actual_weight_global_raw_k_smooth_psi_outer_quarter434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta freq rho K alpha signed hDyad
  have hSub : KSm⊆KG := parity_original_full_odd_smoothed_k_sub_raw434
    d L E V hLw band slot delta Y K
  have hZero (k : ℤ) (hk : k∈KG) (hNo : k∉KSm) : F k=0 := by
    dsimp [F]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro e he
    apply Finset.sum_eq_zero
    intro m hm
    by_cases hK : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
    · simp only [hK,ite_true]
      apply Finset.sum_eq_zero
      intro q hq
      have hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2=0 :=
        parity_original_full_odd_outside_smoothed_k_eta_zero434
          d L E V hLw band slot delta Y e m K k he hm hK hNo q hq
      dsimp only [W]
      rw [hw]
      simp
    · simp [hK]
  have hOmit : (∑k∈KG,F k)=(∑k∈KSm,F k) := by
    exact (Finset.sum_subset hSub hZero).symm
  dsimp only at hRaw ⊢
  exact hRaw.trans hOmit
end Green64Analytic.Parity

end

end

/-! ## QuarterFullKZOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The entire original all-odd B' physical source Cauchy off-diagonal,
with TRUE nonzero η-weight signed KSm and true C∞ ψ-neighbor dyads,
reindexed EXACTLY as a signed k×ZSmooth complex outer. This is a
literal identity of all natural e,m',n,q factors and original H0/W1,
b629 alpha, ε branches, with the same original no-u-cap Ybox. It
uses exact j↦2^j power-of-two image and injectivity, not the false
inequality for norms of complex subsets. Still no Fourier truncation,
all-fine-family summation or full TypeII 4.2 is claimed. -/
theorem parity_original_full_odd_actual_weight_global_smoothed_k_Z_outer_quarter434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let hLw : 8≤L := by linarith
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Y := Nat.ceil (6*U*V)
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
    let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
    let KSm := parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hLw band slot delta Y K
    let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
      parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K J k
    let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e q.2 m q.1
    (∑e∈EF,∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      ∑q∈S e m k, W e m k q) =
    (∑k∈KSm,∑Z∈ZSmooth,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈S e m k,
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))*
            W e m k q
        else 0) := by
  classical
  have hLw : 8≤L := by linarith
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := Nat.ceil (6*U*V)
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Y K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
  let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
  let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
  let KSm := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K J k
  let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1
  let T : Finset ℕ := (Finset.range (N+1)).filter
    (fun j => (2:ℕ)^j∈ZSmooth)
  let G : ℤ → ℕ → ℂ := fun k Z =>
    ∑e∈EF,∑m∈K,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        ∑q∈S e m k,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))*
          W e m k q
      else 0
  have hOriginal := parity_original_full_odd_actual_weight_global_smoothed_k_psi_outer_quarter434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta freq rho K alpha signed hDyad
  have hImage := parity_original_full_odd_true_smooth_Z_image_exact_quarter434
    d L U V E K0 Cbox hL hK0 hCbox hU hV hUV hUVhi hE
    band slot delta K hDyad
  change T.image (fun j : ℕ => (2:ℕ)^j)=ZSmooth at hImage
  have hKZ (k : ℤ) :
      (∑j∈T,∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈S e m k,
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
            W e m k q else 0) =
      ∑Z∈ZSmooth,G k Z := by
    calc
      _ = ∑j∈T,G k (2^j) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [G]
        simp only [Nat.cast_pow, Nat.cast_ofNat]
      _ = ∑Z∈ZSmooth,G k Z :=
        parity_original_finite_true_smooth_dyadic_sum_image_exact434
          ZSmooth N (by simpa only [T] using hImage) (G k)
  dsimp only at hOriginal ⊢
  calc
    _ = ∑k∈KSm,∑j∈T,∑e∈EF,∑m∈K,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        ∑q∈S e m k,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
          W e m k q else 0 := hOriginal
    _ = ∑k∈KSm,∑Z∈ZSmooth,G k Z := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hKZ k
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## QuarterParity417Height -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6800000

/-- Numeric original Parity(4.17) height remains valid for true smooth
ψ preceding-half scale. The slightly wider low endpoint 1/64 is
absorbed by the existing reserved two logarithmic powers of height
(CZ=K0+90), uniformly in all physical k, fine α and source labels. -/
theorem parity_original_true_smooth_neighbor_417_height_numeric_quarter434
    (L K0 Cbox Z : ℝ) (hL : 128≤L) (hK0 : 0≤K0)
    (hCbox : 1≤Cbox) (hLarge : 24*Cbox≤L)
    (hZlo : (Real.exp L/256)*L^K0 < Z)
    (hZhi : Z < 24*Cbox*Real.exp L*L^(K0+88)) :
    Real.exp L*L^(-(K0+90))≤Z ∧
      Z≤Real.exp L*L^(K0+90) := by
  have hLp : 0<L := by linarith
  have hL1 : 1≤L := by linarith
  have hLsq256 : (256:ℝ)≤L^2 := by nlinarith [hL]
  have hp2 : 0<L^(K0-2) := Real.rpow_pos_of_pos hLp _
  have hExp : -(K0+90)≤K0-2 := by linarith
  have hsmall : L^(-(K0+90))≤L^(K0-2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 hExp
  have h256 : 256*L^(-(K0+90))≤L^K0 := by
    calc
      _ ≤ 256*L^(K0-2) := mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ ≤ L^2*L^(K0-2) := mul_le_mul_of_nonneg_right hLsq256 hp2.le
      _ = L^K0 := by
        rw [←Real.rpow_natCast L 2,←Real.rpow_add hLp]
        congr 1
        ring
  have hLow : Real.exp L*L^(-(K0+90)) ≤ (Real.exp L/256)*L^K0 := by
    have hh := mul_le_mul_of_nonneg_left h256 (by positivity : 0≤Real.exp L/256)
    calc
      _ = (Real.exp L/256)*(256*L^(-(K0+90))) := by ring
      _ ≤ (Real.exp L/256)*L^K0 := hh
  have hLsq : 24*Cbox≤L^2 := by
    nlinarith [hLarge,hL1]
  have hP : 0≤L^(K0+88) := Real.rpow_nonneg hLp.le _
  have hUp : 24*Cbox*Real.exp L*L^(K0+88) ≤
      Real.exp L*L^(K0+90) := by
    have hM := mul_le_mul_of_nonneg_right hLsq hP
    have hH : L^2*L^(K0+88) = L^(K0+90) := by
      rw [←Real.rpow_natCast L 2,←Real.rpow_add hLp]
      congr 1
      ring
    have hM2 := mul_le_mul_of_nonneg_left (hM.trans_eq hH)
      (Real.exp_pos L).le
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hM2
  exact ⟨(hLow.trans_lt hZlo).le,(hZhi.trans_le hUp).le⟩

/-- EVERY actual physically populated full-odd source smooth ψ scale,
including exactly the neighboring half-scale needed by support 1<t<4,
meets the native unrestricted signed Parity(4.17) original height
hypothesis at CZ=K0+90. The true cap-free physical Ybox=ceil6UV is
kept, with no Pfree-e condition or dependence on a chosen frequency. -/
theorem parity_original_full_odd_true_smooth_neighbor_Z_Parity417_legal_quarter434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox) (hLarge : 24*Cbox≤L)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (Z : ℕ)
    (hZ : Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K)) :
    Real.exp L*L^(-(K0+90)) ≤ (Z:ℝ) ∧
      (Z:ℝ) ≤ Real.exp L*L^(K0+90) := by
  have hZrange := parity_original_full_odd_true_smooth_neighbor_Z_box_window_quarter434
    d L U V E K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta K hDyad Z hZ
  exact parity_original_true_smooth_neighbor_417_height_numeric_quarter434
    L K0 Cbox (Z:ℝ) hL hK0 hCbox hLarge hZrange.1 hZrange.2
end Green64Analytic.Parity

end

end

/-! ## QuarterTruePsiPhysicalSourceOuter -/

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
theorem parity_original_ungated_true_psi_physical_source_outer_exact_quarter434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox) (hUV : Real.exp L≤4*U*V)
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
  have hOld := parity_original_full_odd_actual_weight_global_smoothed_k_Z_outer_quarter434
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

/-! ## QuarterCauchyODSourceJoin -/

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
theorem parity_original_capfree_Cauchy_OD_eq_true_psi_global_source_quarter434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox) (hUV : Real.exp L≤4*U*V)
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
  have hPsi := parity_original_ungated_true_psi_physical_source_outer_exact_quarter434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta freq rho K alpha signed hDyad
  dsimp only at hReindex hPsi ⊢
  exact hReindex.trans hPsi
end Green64Analytic.Parity

end

end

/-! ## QuarterTruePsiOriginalTail -/

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
theorem parity_original_true_smooth_post_cauchy_eta_active_tail_le_diagonal_quarter434
    (d : ℕ) (L U V E K0 Cbox A R : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox) (hUV : Real.exp L≤4*U*V)
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
    (hLargeN : 32*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
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
    have hh := parity_original_full_odd_true_smooth_neighbor_Z_box_window_quarter434
      d L U V E K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
      band slot δ K hDyad Z hz
    have hPos : (0:ℝ)<(Z:ℝ) := by
      have hb : 0<(Real.exp L/256)*L^K0 := by positivity
      exact hb.trans hh.1
    have hBin := parity_original_full_odd_true_smooth_neighbor_Z_index_capacity_quarter434
      d L U V E K0 Cbox hL hK0 hCbox hU hV hUV hUVhi hE
      band slot δ K hDyad Z hz
    exact ⟨by exact_mod_cast hPos,hh.2.le,⟨hBin.choose,hBin.choose_spec.2⟩⟩
  have hSource := parity_original_ungated_true_psi_physical_source_outer_exact_quarter434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot δ ξ rho K alpha signed hDyad
  have hTail := parity_original_true_psi_eta_active_global_source_tail_le_diagonal_quarter434
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

/-! ## QuarterTruePsiTailAnyLog -/

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
theorem parity_eventually_original_true_psi_post_cauchy_eta_active_tail_any_log_quarter434
    (K0 Cbox A R : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
      ∀ (hL : 128≤L) (U V E : ℝ),
      0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
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
  let BN : ℝ := 32*A^2*(J1.factorial:ℝ)*(2:ℝ)^J1+(J1.factorial:ℝ)*A
  filter_upwards [parity_eventually_original_historical_ungated_box_diagonal_polylog434 Cbox hCbox,
    eventually_ge_atTop (128:ℝ),eventually_ge_atTop (6*Cbox),
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
  have hTail := parity_original_true_smooth_post_cauchy_eta_active_tail_le_diagonal_quarter434
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

/-! ## QuarterCauchyODTailAnyLog -/

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
theorem parity_eventually_original_capfree_Cauchy_OD_eta_active_ball_tail_any_log_quarter434
    (K0 Cbox A R : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
      ∀ (hL : 128≤L) (U V E : ℝ),
      0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
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
  have hTail := parity_eventually_original_true_psi_post_cauchy_eta_active_tail_any_log_quarter434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  filter_upwards [hTail] with L hTailL
  refine ⟨hTailL.1,hTailL.2.1,?_⟩
  intro hL U V E hU hV hUV hUVhi hE
    band slot delta freq rho K alpha signed Acoef hAcoef hAlpha hDyad
    Dgoal hD
  have hErr := hTailL.2.2 hL U V E hU hV hUV hUVhi hE
    band slot delta freq rho K alpha signed Acoef hAcoef hAlpha hDyad Dgoal hD
  have hEq := parity_original_capfree_Cauchy_OD_eq_true_psi_global_source_quarter434
    (sourceOriginalLiteralDepth 20 L) L U E V K0 Cbox hL hK0
    hU hV hCbox hUV hUVhi hE band slot delta freq rho K alpha signed hDyad
  have hPsi := parity_original_ungated_true_psi_physical_source_outer_exact_quarter434
    (sourceOriginalLiteralDepth 20 L) L U E V K0 Cbox hL hK0
    hU hV hCbox hUV hUVhi hE band slot delta freq rho K alpha signed hDyad
  dsimp only at hErr hEq hPsi ⊢
  rw [hPsi] at hErr
  rw [hEq]
  exact hErr
end Green64Analytic.Parity

end

end

/-! ## QuarterCauchyODFullBallTailAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Complete original capfree post-Cauchy OD minus the UNRESTRICTED
B633 physical lowfrequency Fourier ball is O_A(exp(L)L^-A) under
true quarter-UV dyad geometry, with both zero-eta spectral ghosts
paid by original source positive mass and a COMMON original T. -/
theorem parity_eventually_original_capfree_Cauchy_OD_full_ball_tail_any_log_quarter434
    (K0 Cbox A R : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
      ∀ (hL : 128≤L) (U V E : ℝ),
      0<U → 0<V → Real.exp L≤4*U*V → U*V≤Cbox*Real.exp L →
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
        parityOriginalActualTruePsiGlobalPhysicalBall434
          (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot delta
          freq rho alpha signed Y K KS ZS buf
          (-Real.log A) (Real.log A) T hSmooth hSupport‖ ≤
        24*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by
  have hActive := parity_eventually_original_capfree_Cauchy_OD_eta_active_ball_tail_any_log_quarter434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  have hGhost := parity_eventually_original_true_psi_zero_eta_full_active_ball_any_log_quarter434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  filter_upwards [hActive,hGhost] with L hActiveL hGhostL
  rcases hActiveL with ⟨h128,h6,hArest⟩
  rcases hGhostL with ⟨_,_,hGrest⟩
  refine ⟨h128,h6,?_⟩
  intro hL U V E hU hV hUV hUVhi hE band slot delta freq
    rho K alpha signed Acoef hAcoef hAlpha hDyad Dgoal hD
  have hA := hArest hL U V E hU hV hUV hUVhi hE band slot delta freq
    rho K alpha signed Acoef hAcoef hAlpha hDyad Dgoal hD
  have hG := hGrest hL U V E hU hV hUV hUVhi hE band slot delta freq
    rho K alpha signed Acoef hAcoef hAlpha hDyad Dgoal hD
  let hLw : 8≤L := by linarith
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
  let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
  let T : ℝ := L^((X+(K0+89)+M)+Dgoal)
  let d := sourceOriginalLiteralDepth 20 L
  let Y := Nat.ceil (6*U*V)
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K)
  let OD : ℂ := parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
    d L band slot delta freq rho K EF J alpha signed Y
    (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw)
  let Active : ℂ := parityOriginalActualTruePsiEtaActiveGlobalPhysicalBall434
    d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
    buf (-Real.log A) (Real.log A) T hSmooth hSupport
  let Full : ℂ := parityOriginalActualTruePsiGlobalPhysicalBall434
    d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
    buf (-Real.log A) (Real.log A) T hSmooth hSupport
  change ‖OD-Full‖ ≤ _
  have hNA : ‖OD-Active‖ ≤
      8*parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1*Acoef^2*Real.exp L*L^(-Dgoal) := by
    simpa only [OD,Active,T,KS,ZS,Y,EF,J,d,hLw] using hA
  have hNG : ‖Full-Active‖ ≤
      16*parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1*Acoef^2*Real.exp L*L^(-Dgoal) := by
    simpa only [Full,Active,T,KS,ZS,Y,d,hLw] using hG
  have hDecomp : OD-Full=(OD-Active)+(Active-Full) := by ring
  calc
    ‖OD-Full‖ ≤ ‖OD-Active‖+‖Full-Active‖ := by
      calc
        _ = ‖(OD-Active)+(Active-Full)‖ := by rw [hDecomp]
        _ ≤ ‖OD-Active‖+‖Active-Full‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev Active Full]
    _ ≤ 8*parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1*Acoef^2*Real.exp L*L^(-Dgoal) +
        16*parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1*Acoef^2*Real.exp L*L^(-Dgoal) :=
      add_le_add hNA hNG
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## QuarterTrueSmoothKZInputs -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The source-TRUE nonzero-weight Parity(4.13) k union, the actual
canonical post-Cauchy z dyadic Z union and BOTH smooth ψ neighboring
Z scales simultaneously satisfy EVERY numerical precondition of the
quantified B' global k/Z saving theorem. This is not an arbitrary
finite-set hypothesis: KSm and ZG are literally the full-odd B509
physical Q/P/H0 supports at Ybox=ceil(6UV), with all odd e.

The fixed exponents are Ck=K0+89 and CZ=K0+90. Signed Δ=2k is
small uniformly over the entire actual smooth Z carrier, the true
source z cap has logY<=2L, and there is NO #χ or #source event loss.
The requirement UV<=Cbox expL is original fixed-scale geometry. -/
theorem parity_eventually_original_actual_full_odd_smooth_source_kZ_inputs_quarter434
    (K0 Cbox : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, 128≤L ∧ 24*Cbox≤L ∧
    1≤parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox ∧
    ((parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox:ℕ):ℝ)≤
      25*Cbox*Real.exp L*L^(K0+88) ∧
    Real.log ((parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox:ℕ):ℝ)≤2*L ∧
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (hLw : 8≤L)
        (U V E : ℝ) (hU : 0<U) (hV : 0<V)
        (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
        (hE : E=U*L^(-K0)) (K : Finset ℕ)
        (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U),
        let Ybox := Nat.ceil (6*U*V)
        let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
          d L E V hLw band slot delta Ybox K
        let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Ybox K
        let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
        let N := Nat.ceil (L^(K0+89))
        let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
        (∀k∈KS, k≠0 ∧ k.natAbs≤N ∧ (k.natAbs:ℝ)≤L^(K0+89)) ∧
        (∀z∈ZG, 0<z ∧ z≤Y) ∧
        (∀Z∈ZSmooth,
          Real.exp L*L^(-(K0+90))≤(Z:ℝ) ∧
          (Z:ℝ)≤Real.exp L*L^(K0+90) ∧
          (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88)) ∧
        (∀k∈KS,∀Z∈ZSmooth, |((2*k:ℤ):ℝ)|≤(Z:ℝ)/128) := by
  have hS := parity_eventually_original_true_smooth_signed_shift_417434
    (K0+90) (K0+89) (by linarith) (by linarith)
  have hY := parity_eventually_original_actual_true_smooth_source_z_cap_log434
    K0 Cbox hK0 hCbox
  filter_upwards [hS,hY,eventually_ge_atTop (128:ℝ)] with L hSmall hCap h128
  refine ⟨h128,hCap.2.1,hCap.2.2.1,hCap.2.2.2.1,hCap.2.2.2.2,?_⟩
  intro d band slot delta hLw U V E hU hV hUV hUVhi hE K hDyad
  classical
  let Ybox := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Ybox K
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Ybox K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
  let N := Nat.ceil (L^(K0+89))
  let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
  have hK : ∀k∈KS,k≠0 ∧ k.natAbs≤N ∧
      (k.natAbs:ℝ)≤L^(K0+89) := by
    intro k hk
    have hh := parity_original_full_odd_smoothed_k_genuine_polylog434
      d L U E V K0 hLw hU hE band slot delta Ybox K hDyad k hk
    exact ⟨hh.1,hh.2.2,hh.2.1.le⟩
  have hZs : ∀z∈ZG,0<z ∧ z≤Y := by
    intro z hz
    have hBound := parity_original_full_odd_actual_nonzero_Z_union_box_window_quarter434
      d L U V E K0 Cbox (by linarith : 32≤L) band slot delta K hU hV
      (by linarith : 0<Cbox) hUV hUVhi hE hDyad z hz
    have hPos : (0:ℝ)<(z:ℝ) := by
      have hx : (0:ℝ)<(Real.exp L/64)*L^K0 := by positivity
      linarith
    have hZpos : 0<z := by exact_mod_cast hPos
    have hCeil : 24*Cbox*Real.exp L*L^(K0+88)≤(Y:ℝ) := Nat.le_ceil _
    have hZle : (z:ℝ)≤(Y:ℝ) := (hBound.2.trans_le hCeil).le
    exact ⟨hZpos,by exact_mod_cast hZle⟩
  have hH : ∀Z∈ZSmooth,
      Real.exp L*L^(-(K0+90))≤(Z:ℝ) ∧
      (Z:ℝ)≤Real.exp L*L^(K0+90) ∧
      (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88) := by
    intro Z hZ
    have hh := parity_original_full_odd_true_smooth_neighbor_Z_Parity417_legal_quarter434
      d L U V E K0 Cbox h128 hK0 hU hV hCbox hCap.2.1
      hUV hUVhi hE band slot delta K hDyad Z hZ
    have hb := parity_original_full_odd_true_smooth_neighbor_Z_box_window_quarter434
      d L U V E K0 Cbox h128 hK0 hU hV hCbox
      hUV hUVhi hE band slot delta K hDyad Z hZ
    exact ⟨hh.1,hh.2,hb.2.le⟩
  have hShift : ∀k∈KS,∀Z∈ZSmooth,
      |((2*k:ℤ):ℝ)|≤(Z:ℝ)/128 := by
    intro k hk Z hz
    exact hSmall.2 (Z:ℝ) k (hH Z hz).1 (hK k hk).2.2
  dsimp only
  exact ⟨hK,hZs,hH,hShift⟩
end Green64Analytic.Parity

end

end

/-! ## QuarterTruePhysicalKZAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- True global signed k × original C∞ ψ_Z source post-Cauchy B' Fourier
saving, with neither k nor Z nor the natural source height Y supplied
as arbitrary finite sets. Those carriers are the ACTUAL full-odd B509
physical nonzero η_eη_n source support with corrected cap-free Ybox.
The one fixed reserved-Q band/slot and one fine b629 interval remain
quantified; entire original TypeII and all external source families
are not claimed by this theorem. The fixed strict m<2U input is the
original source half-open cofactor dyad and requires source audit. -/
theorem parity_eventually_original_actual_Bprime_true_physical_kZ_any_log_quarter434
    (jQ : ℕ) (Agoal D C0 Cf beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D) (hPrecision : Agoal+(K0+89)+K0+90≤D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
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
          (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤4*U*V → E=U*L^(-K0) →
          T=L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
        U*V≤Cbox*Real.exp L →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let Ybox := Nat.ceil (6*U*V)
        let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
          d L E V hLw band slot delta Ybox K
        let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Ybox K
        let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖∑k∈KS,∑Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
          parityOriginalActualBprimeFineLowfreqSignal434
            d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
            rho xi1 xi2 xi3 T signed buf A hSmooth hSupport‖ ≤
          (250*Cbox*(1+2/Real.log 2)*(Cmoment+132*Cmoment1))*
            Real.exp L*L^(-Agoal) := by
  obtain ⟨J,B,S,hBS,hMain⟩ :=
    parity_eventually_original_actual_Bprime_fine_smooth_psi_neighbor_kZ_any_log_quarter434
      jQ Agoal D C0 Cf (K0+90) (K0+89) beta gamma K0 Cbox A R
      hD hPrecision hCf (by linarith) (by linarith)
      hbeta hgamma hK0 hCbox hA hR buf hSmooth hSupport hCube
  have hSource := parity_eventually_original_actual_full_odd_smooth_source_kZ_inputs_quarter434
    K0 Cbox hK0 hCbox
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hMain,hSource] with L hMainL hSourceL
  rcases hMainL with ⟨hL8,hL6,hFamily,hReserved,hMainRest⟩
  rcases hSourceL with ⟨hL32,hLarge,hYpos,hYhi,hYlog,hSourceRest⟩
  refine ⟨hL32,hL6,hFamily,hReserved,?_⟩
  intro hLw hFamily0 band hBand slot delta freq rho xi1 xi2 xi3
    U E V T signed hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyadStrict hUVhi
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let Ybox := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Ybox K
  let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Ybox K
  let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
  let N := Nat.ceil (L^(K0+89))
  have hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U := by
    intro m hm
    obtain ⟨hl,hr⟩ := hDyadStrict m hm
    exact ⟨hl,hr.le⟩
  have hGeo := hSourceRest d band slot delta hLw U V E
    hU hV hUV hUVhi hEscale K hDyadStrict
  dsimp only at hGeo
  rcases hGeo with ⟨hKS,hZS,hZwindow,hShift⟩
  have hMainBound := hMainRest hLw hFamily0 band hBand slot delta freq
    rho xi1 xi2 xi3 U E V T signed
    hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyad
    KS N Y ZS hKS hZS hZwindow hShift (le_refl N)
    hYhi hYpos hYlog
  dsimp only at hMainBound ⊢
  exact hMainBound
end Green64Analytic.Parity

end

end

/-! ## QuarterActualFullPsiBallSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- ACTUAL original Parity (4.10) FULL, UNFILTERED physical C∞ smooth-psi
3D Fourier ball has arbitrarily deep inverse-log saving after the
correct k/Z outer is summed for the actual b629 fine prime/rough
coefficient. It is the same BALL on the RHS of the true positive
Cauchy precursor with BOTH separately paid zero-eta ghosts.
The source no-u-cap Ybox=ceil(6UV), genuine signed k, both smooth
psi neighboring dyads, entire odd-e source including P-bearing e,
full projected modulus 2|k|, H0/W1/epsilon and actual 3D eta source
are retained. One reserved Q band/slot and one b629 fine interval
remain fixed but arbitrary. This is NOT yet the full original TypeII.
J,B,S are chosen before L with the inherited Parity(4.17) accuracy. -/
theorem parity_eventually_original_actual_true_full_psi_physical_ball_any_log_quarter434
    (jQ : ℕ) (Agoal D C0 Cf beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D) (hPrecision : Agoal+(K0+89)+K0+90≤D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
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
          (rho U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤4*U*V → E=U*L^(-K0) →
          T=L^Cf →
          |rho|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
        U*V≤Cbox*Real.exp L →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let Ybox := Nat.ceil (6*U*V)
        let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
          d L E V hLw band slot delta Ybox K
        let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Ybox K
        let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖parityOriginalActualTruePsiGlobalPhysicalBall434
          d L U E V hLw band slot delta freq rho alpha signed Ybox K KS
          (parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS)
          buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ ≤
          (250*Cbox*(1+2/Real.log 2)*(Cmoment+132*Cmoment1))*
            Real.exp L*L^(-Agoal) := by
  obtain ⟨J,B,S,hBS,hMain⟩ :=
    parity_eventually_original_actual_Bprime_true_physical_kZ_any_log_quarter434
      jQ Agoal D C0 Cf beta gamma K0 Cbox A R
      hD hPrecision hCf hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  have hSpos : 0<S := by linarith
  have hEq := parity_eventually_original_actual_fine_full_psi_global_ball_eq_Bprime434
    S beta gamma (K0+89) hSpos hbeta hgamma
  have hSource := parity_eventually_original_actual_full_odd_smooth_source_kZ_inputs_quarter434
    K0 Cbox hK0 hCbox
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hMain,hEq,hSource] with L hMainL hEqL hSourceL
  rcases hMainL with ⟨hL32,hL6,hFamily,hReserved,hMainRest⟩
  rcases hSourceL with ⟨hLcap,hLarge,hYpos,hYhi,hYlog,hSourceRest⟩
  refine ⟨hLcap,hL6,hFamily,hReserved,?_⟩
  intro hLw hFamily0 band hBand slot delta freq rho U E V T signed
    hU hEpos hV hUV hEscale hT hrho
    prime lFine uFine a b hFineLow hl hu huExp hDyadStrict hUVhi
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let Ybox := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Ybox K
  let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Ybox K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hGeo := hSourceRest d band slot delta hLw U V E
    hU hV hUV hUVhi hEscale K hDyadStrict
  dsimp only at hGeo
  rcases hGeo with ⟨hKS,hZS,hZwin,hShift⟩
  have hKS0 : ∀k∈KS,k≠0 ∧ (k.natAbs:ℝ)≤L^(K0+89) := by
    intro k hk
    exact ⟨(hKS k hk).1,(hKS k hk).2.2⟩
  have hFull := hEqL.2 hLw prime lFine uFine hl hFineLow K KS hKS0 ZSmooth
    d band slot delta freq U E V T rho A signed buf hSmooth hSupport
  have hZero : |(0:ℝ)|≤L^C0 := by
    simp only [abs_zero]
    exact (Real.rpow_pos_of_pos (by linarith : 0<L) _).le
  have hOld := hMainRest hLw hFamily0 band hBand slot delta freq
    rho 0 0 0 U E V T signed hU hEpos hV hUV hEscale hT
    hrho hZero hZero hZero
    prime lFine uFine a b hFineLow hl hu huExp hDyadStrict hUVhi
  dsimp only at hFull hOld ⊢
  rw [hFull]
  exact hOld
end Green64Analytic.Parity

end

end

/-! ## QuarterCauchyFullBallPrecision -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false

/-- A single source-ordered polynomial Fourier precision synchronizes
actual full B633 ball saving with full original Cauchy OD-to-ball error.
The fixed K0 and requested Agoal are chosen before Dghost, Dmain,Cf,
then Parity J,B,S and finally L. The same L/Q/P and T=L^Cf are used. -/
theorem parity_original_quarter_cauchy_full_ball_precision_compatible434
    (Agoal K0 : ℝ) (hA : 0≤Agoal) (hK0 : 0≤K0) :
    let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
    let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
    let CW : ℝ := parityOriginalW1PolylogExponent434
    let Dghost : ℝ := Agoal+K0+200
    let Dmain : ℝ := K0+315+Dghost
    let Cf : ℝ := X+Dmain+2*CW+30
    0≤Dghost ∧ 0<Dmain ∧
    Agoal+(K0+89)+K0+90≤Dmain ∧
    Cf = (5*(K0+90))*
        ((((1+P:ℕ):ℝ)+1))+(Dmain+2*CW+30) ∧
    Cf = (X+(K0+89)+(2*CW+256))+Dghost := by
  dsimp
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · push_cast
    ring
  · ring
end Green64Analytic.Parity

end

end

/-! ## QuarterActualFineODAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- True original full capfree post-Cauchy OD, not an abstract Fourier
signal, for one actual b629 fine prime/rough cell and reserved Q
band/slot. Source H0/W1, all odd e, character modulus 2|k|, signed
branch and full physical quarter-UV geometry are unchanged. One
source-ordered Fourier cutoff pays both ghosts and the Parity(4.17)
correlation, with no extra α bound assumed. This is still ONE fine
cell, NOT the full original TypeII or source §7.3 replacement. -/
theorem parity_eventually_original_actual_quarter_fine_postCauchy_OD_anylog434
    (jQ : ℕ) (Agoal C0 beta gamma K0 Cbox A R : ℝ)
    (hAgoal : 0≤Agoal) (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
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
  have hBall := parity_eventually_original_actual_true_full_psi_physical_ball_any_log_quarter434
    jQ Agoal Dmain C0 Cf beta gamma K0 Cbox A R
    hDmain hPrecision (by simpa only [Cf,X,CW,P] using hCfmain)
    hbeta hgamma hK0 hCbox hA hR buf hSmooth hSupport hCube
  have hTail := parity_eventually_original_capfree_Cauchy_OD_full_ball_tail_any_log_quarter434
    K0 Cbox A R hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  obtain ⟨J,B,S,hBS,hBallL⟩ := hBall
  have hS : 0<S := by linarith
  have hAlpha := parity_eventually_original_actual_b629_K_fine_alpha_norm_one434
    S beta gamma hS hbeta hgamma
  refine ⟨J,B,S,hBS,?_⟩
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
end Green64Analytic.Parity

end

end

/-! ## QuarterActualFineCauchySquare -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The ACTUAL original fine b629 capfree pre-Cauchy selected Q B'
squared norm, with genuine beta and selected-e Fourier gate,
controlled directly by the source physical diagonal and the
new quarter-UV fully paid original post-Cauchy offdiagonal.
No old stronger UV≥exp L geometry is imported. -/
theorem parity_eventually_original_actual_quarter_fine_Cauchy_square434
    (jQ : ℕ) (Agoal C0 beta gamma K0 Cbox A R : ℝ)
    (hAgoal : 0≤Agoal) (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
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
  have hOD := parity_eventually_original_actual_quarter_fine_postCauchy_OD_anylog434
    jQ Agoal C0 beta gamma K0 Cbox A R hAgoal hbeta hgamma hK0 hCbox
    hA hR buf hSmooth hSupport hOne4 hCube
  have hPre := parity_eventually_original_capfree_Bprime_Cauchy_box_precursor434
    Cbox hCbox
  have hW := parity_eventually_original_actual_cauchy_Wout_EV_all_log434
  have hSpos : ∀ S : ℝ, 2*((0:ℝ)+1)+3<S → 0<S := by intros; linarith
  obtain ⟨J,B,S,hBS,hODL⟩ := hOD
  have hS : 0<S := by linarith
  have hAlpha := parity_eventually_original_actual_b629_K_fine_alpha_norm_one434
    S beta gamma hS hbeta hgamma
  refine ⟨J,B,S,hBS,?_⟩
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
end Green64Analytic.Parity

end

end

/-! ## QuarterActualFinePreCauchyNorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Full original b629 prime/rough fine PRE-Cauchy selected Q
complex norm after original Gram, positive diagonal and Wout≤6EV
Fourier gate. Uses genuine original e/n,m, h=-2, Q/P source and
quarter dyad, exact source K0 payment; not the entire TypeII. -/
theorem parity_eventually_original_actual_quarter_fine_preCauchy_norm_anylog434
    (jQ : ℕ) (Agoal C0 beta gamma K0 Cbox A R : ℝ)
    (hAgoal : 0≤Agoal)
    (hK0Target : 2*Agoal+2*parityOriginalW1PolylogExponent434+344≤K0) (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
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
  have hSq := parity_eventually_original_actual_quarter_fine_Cauchy_square434
    jQ Agoal C0 beta gamma K0 Cbox A R hAgoal hbeta hgamma
    hK0 hCbox hA hR buf hSmooth hSupport hOne4 hCube
  obtain ⟨J,B,S,hBS,hSqL⟩ := hSq
  refine ⟨J,B,S,hBS,?_⟩
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
end Green64Analytic.Parity

end

end

