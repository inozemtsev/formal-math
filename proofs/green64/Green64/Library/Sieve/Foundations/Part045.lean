module

public import Green64.Library.Sieve.Foundations.Part044
public import Green64.Library.Sieve.Foundations.Part032
public import Green64.Library.Sieve.Foundations.Part037
public import Green64.Library.Sieve.Foundations.Part041
public import Green64.Library.Sieve.Foundations.Part038
public import Green64.Library.Sieve.Foundations.Part043
public import Green64.Library.Sieve.Foundations.Part016
public import Green64.Library.Sieve.Foundations.Part031
public import Green64.Library.Sieve.Foundations.Part040

@[expose] public section

/-!
# Sieve / Foundations / Part045

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## QuarterFourierMoment -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- The ORIGINAL source cap-free Parity(4.14) three-dimensional
Schwartz H-moment is uniformly ≤ C_H L^[5(K0+90)(H+P+1)]
for ALL true Z≤24Cbox expL L^(K0+88), Cbox fixed,
L≥6Cbox; C_H fixed before L,k,Z,e,χ and target Fourier
precision. All five source factors and true h=-2 term kept.
This repairs previously artificial Y0 Fourier moment theorem
without logarithmic exponent inflation. -/
theorem parity_original_historical_box_source_BH_uniform_polylog_quarter434
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
    (H : ℕ)
    (hLargeE : 2*A*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 32*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
       (2:ℝ)^(H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
       ((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀ t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    parityOriginal3DSourceMomentFiniteBudget434 H
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) ≤
    parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hBufSmooth hBufSupport H *
      L^((5*(K0+90))*(((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf (-Real.log A) (Real.log A)
    hBufSmooth hBufSupport
  let P := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let J := H+P
  let B := parityOriginalHistoricalFull3DSourceSeminormFixedK434
    A R buf hBufSmooth hBufSupport J
  let C := parityOriginal3DSourceGeometricConstant434
  let Q := L^((5*(K0+90))*((J:ℝ)+1))
  have hm0 := parity_original_historical_box_3d_finite_seminorm_budget_quarter434
    L U E V Z K0 Cbox A hL hK0 k hk hU hV hUV hE hZ
    hCbox hLargeC hZupper hA
    buf hBufSmooth hBufSupport J 0 (Nat.zero_le J)
    hLargeE hLargeN R hR hCubeR
  have hmJ := parity_original_historical_box_3d_finite_seminorm_budget_quarter434
    L U E V Z K0 Cbox A hL hK0 k hk hU hV hUV hE hZ
    hCbox hLargeC hZupper hA
    buf hBufSmooth hBufSupport J J le_rfl
    hLargeE hLargeN R hR hCubeR
  have hC : 0≤C := parity_original_3d_source_geometric_constant_nonneg434
  change C*(parityOriginal3DSourceFiniteSeminormBudget434 0 f+
      parityOriginal3DSourceFiniteSeminormBudget434 J f) ≤ (2*C*B)*Q
  calc
    _ ≤ C*((B*Q)+(B*Q)) :=
      mul_le_mul_of_nonneg_left (add_le_add hm0 hmJ) hC
    _ = (2*C*B)*Q := by ring
end Green64Analytic.Parity

end

end

/-! ## QuarterBprimeM0Normalization -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 3600000

/-- The REAL original cap-free Parity(4.14) smooth kernel is quantitatively
L1 in Fourier at H=0. This is source-derived from all 5 smooth
factors on the actual Ybox=ceil(6UV) physical z height, not an
independent Fourier-boundedness hypothesis. It is exactly the M0
needed in the new integrated Bprime -> signed Eq(4.17) theorem. -/
theorem parity_original_actual_capfree_Bprime_M0_uniform_polylog_quarter434
    (L U E V Z K0 Cbox A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤4*U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88))
    (hA : 0<A) (buf : ℝ → ℂ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ s : ℝ, buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (hLargeE : 2*A*((0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 32*A^2*((0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
      (2:ℝ)^(0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
      ((0+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    parityOriginal3DSourceMomentFiniteBudget434 0
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf (-Real.log A) (Real.log A)
        hBufSmooth hBufSupport) ≤
    parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hBufSmooth hBufSupport 0 *
      L^((5*(K0+90))*((((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) := by
  simpa only [Nat.zero_add] using
    (parity_original_historical_box_source_BH_uniform_polylog_quarter434
      L U E V Z K0 Cbox A hL hK0 k hk hU hV hUV hE hZ
      hCbox hLargeC hZupper hA buf hBufSmooth hBufSupport 0
      hLargeE hLargeN R hR hCubeR)
end Green64Analytic.Parity

end

end

/-! ## QuarterEtaActiveGlobalTail -/

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
theorem parity_original_true_psi_eta_active_global_source_tail_le_diagonal_quarter434
    (d : ℕ) (L U E V K0 Cbox A R : ℝ) (hL : 8≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤4*U*V) (hE : E=U*L^(-K0))
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
    (hLargeN : 32*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
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
    have hm := parity_original_historical_box_source_BH_uniform_polylog_quarter434
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

/-! ## QuarterFullPsiGhostMass -/

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
theorem parity_original_true_psi_full_global_ghost_mass_le_diagonal_quarter434
    (d : ℕ) (L U E V K0 Cbox A R : ℝ) (hL : 8≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤4*U*V) (hE : E=U*L^(-K0))
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
    (hLargeN : 32*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
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
    have hm := parity_original_historical_box_source_BH_uniform_polylog_quarter434
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

/-! ## QuarterGhostUniformMoment -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The TRUE corrected cap-free Parity(4.14) lowfrequency B-prime
2-ghost Schwartz moment budget, at ALL original physical dyadic
heights Z <= 24 Cbox exp L L^(K0+88). This is stronger in actual
source RANGE than the previously checked Sigma ghost moment restricted
to Z <= 4 exp L L^(K0+88). The positive source coefficient mass
factor remains exactly the B633 unrestricted 4th-divisor bound;
no fictitious source e-, character-, or m-multiplicity is charged. -/
theorem parity_original_Bprime_capfree_full_Z_two_ghost_uniform_moment_quarter434
    (H : ℕ) (L U E V Z K0 Cbox A : ℝ) (k : ℤ)
    (hL : 8≤L) (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤4*U*V) (hE : E=U*L^(-K0))
    (hk : k≠0) (hZ : 0<Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88)) (hA : 0<A)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀(s:ℝ), buf s≠0 →
      -(Real.log A) ≤ s ∧ s ≤ Real.log A)
    (hLargeE : 2*A*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 32*A^2*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
      (2:ℝ)^(H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
      ((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (T : ℝ) (hT : 0<T) :
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
    let Y := Nat.ceil (65*Z)
    (L^(2*parityOriginalW1PolylogExponent434)*(Y:ℝ)*
      (1+Real.log (Y:ℝ))^15) *
      (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) ≤
    (L^(2*parityOriginalW1PolylogExponent434)*(Y:ℝ)*
      (1+Real.log (Y:ℝ))^15) *
      ((parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport H *
        L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)))/T^H) := by
  dsimp only
  have hMoment := parity_original_historical_box_source_BH_uniform_polylog_quarter434
    L U E V Z K0 Cbox A hL hK0 k hk hU hV hUV hE hZ.le
    hCbox hLargeC hZupper hA buf hSmooth hSupport H hLargeE hLargeN
    R hR hCubeR
  have hY : 1≤Nat.ceil (65*Z) := by
    exact Nat.one_le_ceil_iff.mpr (by positivity)
  have hYReal : (1:ℝ)≤((Nat.ceil (65*Z):ℕ):ℝ) := by exact_mod_cast hY
  have hLog : 0≤1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ) := by
    have hx := Real.log_nonneg hYReal
    linarith
  have hFactor : 0≤L^(2*parityOriginalW1PolylogExponent434)*
      ((Nat.ceil (65*Z):ℕ):ℝ)*
      (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15 := by
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by linarith : 0≤L) _)
        (Nat.cast_nonneg _)) (pow_nonneg hLog _)
  have hTail := div_le_div_of_nonneg_right hMoment
    (pow_nonneg hT.le H)
  exact mul_le_mul_of_nonneg_left hTail hFactor
end Green64Analytic.Parity

end

end

/-! ## QuarterGhostPolynomialCanonical -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- At the exact corrected cap-free Parity dyadic Z height, choosing
ONE polynomial Fourier cutoff T=L^(5(K0+90)(1+P+1)+D)
gives an arbitrary inverse-log saving L^-D in BOTH source-paid
ghost errors, relative to their genuine positive 4th-divisor mass
Y_F(1+log Y_F)^15 and fixed 3D moment constant. The choice
is made before L and is valid uniformly in source k,Z. The mass
factor is NOT silently bounded by x; summing source k,Z and
fine families is a separate remaining Type II integration step. -/
theorem parity_original_Bprime_capfree_ghost_polynomial_T_any_precision_quarter_canonical434
    (D : ℝ) (L U E V Z K0 Cbox A : ℝ) (k : ℤ)
    (hL : 32≤L) (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤4*U*V) (hE : E=U*L^(-K0))
    (hk : k≠0) (hZ : 0<Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88)) (hA : 0<A)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀(s:ℝ), buf s≠0 →
      -(Real.log A) ≤ s ∧ s ≤ Real.log A)
    (hLargeE : 2*A*((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 32*A^2*((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
      (2:ℝ)^(1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
      ((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L)
    (R : ℝ) (hR : 1≤R)
    (hCubeR : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (hD : 0≤D) :
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L (by linarith : 8≤L) U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
    let Y := Nat.ceil (65*Z)
    let X : ℝ := (5*(K0+90))*(((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)
    let T : ℝ := L^(X+D)
    (L^(2*parityOriginalW1PolylogExponent434)*(Y:ℝ)*
      (1+Real.log (Y:ℝ))^15) *
      (parityOriginal3DSourceMomentFiniteBudget434 1 f/T) ≤
    (L^(2*parityOriginalW1PolylogExponent434)*(Y:ℝ)*
      (1+Real.log (Y:ℝ))^15) *
      (parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1 * L^(-D)) := by
  dsimp only
  let X : ℝ := (5*(K0+90))*
    (((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)
  let T : ℝ := L^(X+D)
  have hLp : 0<L := by linarith
  have hT : 0<T := Real.rpow_pos_of_pos hLp _
  have hSource := parity_original_Bprime_capfree_full_Z_two_ghost_uniform_moment_quarter434
    1 L U E V Z K0 Cbox A k (by linarith : 8≤L) hK0 hU hV hUV hE hk hZ
    hCbox hLargeC hZupper hA buf hSmooth hSupport hLargeE hLargeN
    R hR hCubeR T hT
  dsimp only at hSource
  have hPow : L^X/T=L^(-D) := by
    exact parity_original_ghost_polynomial_T_exact_power_cancel434 L X D hLp
  have hConst :
      (parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1 * L^X)/T =
      parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1 * L^(-D) := by
    rw [mul_div_assoc,hPow]
  calc
    _ ≤ (L^(2*parityOriginalW1PolylogExponent434)*((Nat.ceil (65*Z):ℕ):ℝ)*
      (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15) *
      ((parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1 * L^X)/T^1) := by
        simpa only [T,X,pow_one] using hSource
    _ = _ := by rw [pow_one,hConst]
end Green64Analytic.Parity

end

end

/-! ## QuarterGhostScaledCanonical -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The *actual* two-ghost source coefficient mass and 3D Fourier
moment, including ceil(65 Z) and the original five-factor Schwartz
kernel, have explicit fixed-(k,Z) inverse-log saving relative to Z.
No loss depends on the number of characters or e,n,m,m',z source
multiplicities. C_1 is the genuine fixed-buffer Schwartz constant,
which is retained rather than being silently bounded by one.
Polynomial Fourier precision D is chosen before L. -/
theorem parity_eventually_original_Bprime_two_ghost_scaled_tail_quarter_canonical434
    (CZ Ck : ℝ) (hCZ : 0≤CZ) :
    ∀ᶠ L : ℝ in atTop, 32≤L ∧
      ∀ (hLw : 8≤L) (Z : ℝ), Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
      ∀ k : ℤ, k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (D U E V K0 Cbox A : ℝ), 0≤D → 0≤K0 →
        0<U → 0<V → Real.exp L≤4*U*V → E=U*L^(-K0) →
        0≤Cbox → 6*Cbox≤L →
        Z≤24*Cbox*Real.exp L*L^(K0+88) → 0<A →
      ∀ (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀ (s : ℝ), buf s ≠ 0 → (-(Real.log A) ≤ s ∧ s ≤ Real.log A)),
        2*A*((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L →
        32*A^2*((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
          (2:ℝ)^(1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
          ((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L →
      ∀ R : ℝ, 1≤R →
        (∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) →
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf
          (-Real.log A) (Real.log A) hSmooth hSupport
      let Y := Nat.ceil (65*Z)
      let X : ℝ := (5*(K0+90))*
        (((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)
      let T : ℝ := L^(X+D)
      let C1 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      (L^(2*parityOriginalW1PolylogExponent434)*(Y:ℝ)*
        (1+Real.log (Y:ℝ))^15)*
        (parityOriginal3DSourceMomentFiniteBudget434 1 f/T) ≤
      66*Z*C1*L^(2*parityOriginalW1PolylogExponent434+30-D) := by
  filter_upwards [parity_eventually_original_Bprime_two_ghost_mass_normalized434
    CZ Ck hCZ,eventually_ge_atTop (32:ℝ)] with L hMass h32
  refine ⟨h32,?_⟩
  intro hLw Z hZlo hZhi k hk hkBound D U E V K0 Cbox A hD hK0 hU hV hUV hE
    hCbox hLargeC hZupper hA buf hSmooth hSupport hLargeE hLargeN
    R hR hCubeR
  have hLp : 0<L := by linarith [hMass.1]
  have hZ := (hMass.2 Z hZlo hZhi k hkBound).1
  have hZp : 0<Z := by linarith
  have hPoly := parity_original_Bprime_capfree_ghost_polynomial_T_any_precision_quarter_canonical434
    D L U E V Z K0 Cbox A k h32 hK0 hU hV hUV hE hk hZp
    hCbox hLargeC hZupper hA buf hSmooth hSupport hLargeE hLargeN
    R hR hCubeR hD
  dsimp only at hPoly
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hC1 : 0≤C1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hDfactor : 0≤C1*L^(-D) :=
    mul_nonneg hC1 (Real.rpow_nonneg hLp.le _)
  have hBound := (hMass.2 Z hZlo hZhi k hkBound).2.2.2.2
  have hMul := mul_le_mul_of_nonneg_right hBound hDfactor
  have hPower :
      L^(2*parityOriginalW1PolylogExponent434+30)*L^(-D) =
      L^(2*parityOriginalW1PolylogExponent434+30-D) := by
    rw [←Real.rpow_add hLp]
    congr 1
  have hAlgebra :
      (66*Z*L^(2*parityOriginalW1PolylogExponent434+30))*(C1*L^(-D)) =
      66*Z*C1*L^(2*parityOriginalW1PolylogExponent434+30-D) := by
    calc
      _ = (66*Z*C1)*
          (L^(2*parityOriginalW1PolylogExponent434+30)*L^(-D)) := by ring
      _ = _ := by rw [hPower]
  exact hPoly.trans (hMul.trans_eq hAlgebra)
end Green64Analytic.Parity

end

end

/-! ## QuarterBprimePrimaryTwoGhost -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4900000

/-- Actual ORIGINAL cap-free Bprime all-odd post-Cauchy 3D source
LOW-frequency ball, now with the MAIN signed Parity(4.17) saving
numerically normalized to C_0 Z L^-D (no remaining abstract M0).
The genuine source eta_e/n moment is proved from the exact five
smooth factors with original upper z-height, under UV~exp L and
E=U L^-K0; J,B,S are fixed with target D+p0 BEFORE L.

The TWO independently source-paid ghost errors remain EXPLICIT, with
no forbidden signed-subset monotonicity. Full global k/Z/branch/fine
summation and Parity TypeII(4.2), §§5-9 and Green64 are not asserted. -/
theorem parity_eventually_original_actual_Bprime_lowfreq_primary_normalized_two_ghost_quarter434
    (jQ : ℕ) (D C0 Cf CZ Ck beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D) (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
        ∀ (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤4*U*V →
          E=U*L^(-K0) → Z≤24*Cbox*Real.exp L*L^(K0+88) →
          0<T → T≤L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
          |((2*k:ℤ):ℝ)|≤Z/128 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        ∀ (H : ℕ),
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let d := sourceOriginalLiteralDepth 20 L
        let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
        let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
        let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
          (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
        let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
          L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
        let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
        let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
          parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
            d L E V band slot delta (Nat.ceil (6*U*V)) m K k
        let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
          parityOriginalHistoricalUngatedSourceToSigma434
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (∑m0∈K, ∑q∈sourceTerms m0,
                parityOriginalHistoricalDyadicSmoothPsi434
                  ((parityOriginalHistoricalCanonicalZ434 q.1 m0 q.2.1 q.2.2:ℝ)/Z) *
                alpha m0 * star (alpha q.2.1) *
                At (phi m0 q) *
                parityOriginal3DPhysicalLogFourierPhase434 ζ
                  (parityOriginalHistoricalRealLogTriple434 U Z
                    (phi m0 q).2.2 (phi m0 q).2.1 (phi m0 q).1))‖ ≤
        Cmoment*Z*L^(-D) +
          2*((L^(2*parityOriginalW1PolylogExponent434)*
            ((Nat.ceil (65*Z):ℕ):ℝ)*
            (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let p0 : ℝ := 5*(K0+90)*((P:ℝ)+1)
  have hp0 : 0≤p0 := by
    have hK : 0≤K0+90 := by linarith
    have hp : 0≤(P:ℝ) := Nat.cast_nonneg _
    dsimp [p0]
    positivity
  have hTarget : 0<D+p0 := by linarith
  obtain ⟨J,B,S,hBS,hMain⟩ :=
    parity_eventually_original_actual_Bprime_full_odd_lowfreq_le_integrated_417_plus_two_ghost434
      jQ (D+p0) C0 Cf CZ Ck beta gamma hTarget hCZ hCk hbeta hgamma
  let BE : ℝ := 2*A*(P.factorial:ℝ)
  let BN : ℝ := 32*A^2*(P.factorial:ℝ)*(2:ℝ)^P+(P.factorial:ℝ)*A
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hMain,eventually_ge_atTop (32:ℝ),eventually_ge_atTop (6*Cbox),
    eventually_ge_atTop BE,eventually_ge_atTop BN]
    with L hMainL h32 hC hBE hBN
  refine ⟨h32,hC,hMainL.2.1,hMainL.2.2.1,?_⟩
  intro hLw hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U E V T signed hU hEpos hV hUV hE hZupper
    hT hTCut hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad H
  classical
  let K := Finset.Icc a b
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let d := sourceOriginalLiteralDepth 20 L
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
    parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta (Nat.ceil (6*U*V)) m K k
  let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
    parityOriginalHistoricalUngatedSourceToSigma434
  have hZ0 : 0≤Z := by
    have hh : 0<Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos (by linarith : 0<L) _)
    exact (hh.trans_le hZlo).le
  have hMoment := parity_original_actual_capfree_Bprime_M0_uniform_polylog_quarter434
    L U E V Z K0 Cbox A hLw hK0 k hk hU hV hUV hE hZ0
    (by linarith : 0≤Cbox) hC hZupper hA buf hSmooth hSupport
    (by simpa only [Nat.zero_add] using hBE)
    (by simpa only [Nat.zero_add] using hBN) R hR hCube
  have hAbsorb := parity_original_actual_capfree_Bprime_primary_inverse_log_from_M0434
    L Z D K0 Cmoment (parityOriginal3DSourceMomentFiniteBudget434 0 f)
    hLw hZ0 hMoment
  have hOld := hMainL.2.2.2 hLw hFamily Z hZlo hZhi band hBand slot delta freq
    k hk hkBound rho xi1 xi2 xi3 U E V T signed hU hEpos hV hT hTCut
    hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad
    buf (-Real.log A) (Real.log A) hSmooth hSupport H
  dsimp only at hOld hAbsorb ⊢
  exact hOld.trans (add_le_add_left hAbsorb _)
end Green64Analytic.Parity

end

end

/-! ## QuarterFixedKZSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5900000

/-- Exact ORIGINAL all-odd actual cap-free Bprime lowfrequency Fourier
ball, for every fixed k,Z, fine b629 K, source reserved Q band and slot,
with FULL paid ghosts and actual original five-factor ηeηn Schwartz
kernel, satisfies an arbitrarily deep L^-D saving with fixed ORIGINAL
source constant C0+132*C1. A SINGLE Fourier T=L^Cf is chosen before
J,B,S,L, where Cf pays H=1 source derivatives and W1/corr mass.
All actual χ are projected before cutting frequencies; no omitted
physical e/n/m counts or fake P-free e selection. This is a per-k,Z
and fine-cell theorem, NOT the global Parity TypeII (4.2). -/
theorem parity_eventually_original_actual_Bprime_full_odd_fixed_KZ_any_log_saving_quarter434
    (jQ : ℕ) (D C0 Cf CZ Ck beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
        ∀ (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤4*U*V →
          E=U*L^(-K0) → Z≤24*Cbox*Real.exp L*L^(K0+88) →
          T=L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
          |((2*k:ℤ):ℝ)|≤Z/128 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let d := sourceOriginalLiteralDepth 20 L
        let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
        let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
        let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
          (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
        let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
          L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
        let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
        let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
          parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
            d L E V band slot delta (Nat.ceil (6*U*V)) m K k
        let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
          parityOriginalHistoricalUngatedSourceToSigma434
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (∑m0∈K, ∑q∈sourceTerms m0,
                parityOriginalHistoricalDyadicSmoothPsi434
                  ((parityOriginalHistoricalCanonicalZ434 q.1 m0 q.2.1 q.2.2:ℝ)/Z) *
                alpha m0 * star (alpha q.2.1) *
                At (phi m0 q) *
                parityOriginal3DPhysicalLogFourierPhase434 ζ
                  (parityOriginalHistoricalRealLogTriple434 U Z
                    (phi m0 q).2.2 (phi m0 q).2.1 (phi m0 q).1))‖ ≤
        (Cmoment+132*Cmoment1)*Z*L^(-D) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X : ℝ := (5*(K0+90))*(((1+P:ℕ):ℝ)+1)
  let Dghost : ℝ := D+2*parityOriginalW1PolylogExponent434+30
  have hCW : 0≤parityOriginalW1PolylogExponent434 :=
    parity_original_actual_W1_polylog_exponent_nonneg434
  have hDghost : 0≤Dghost := by dsimp [Dghost]; linarith
  have hCfX : Cf = X+Dghost := by simpa only [X,Dghost] using hCf
  obtain ⟨J,B,S,hBS,hMain⟩ :=
    parity_eventually_original_actual_Bprime_lowfreq_primary_normalized_two_ghost_quarter434
      jQ D C0 Cf CZ Ck beta gamma K0 Cbox A R
      hD hCZ hCk hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  have hGhost := parity_eventually_original_Bprime_two_ghost_scaled_tail_quarter_canonical434
    CZ Ck hCZ
  let J1 : ℕ := 1+P
  let BE1 : ℝ := 2*A*(J1.factorial:ℝ)
  let BN1 : ℝ := 32*A^2*(J1.factorial:ℝ)*(2:ℝ)^J1+(J1.factorial:ℝ)*A
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hMain,hGhost,eventually_ge_atTop BE1,
    eventually_ge_atTop BN1] with L hMainL hGhostL hBE1 hBN1
  refine ⟨hMainL.1,hMainL.2.1,hMainL.2.2.1,hMainL.2.2.2.1,?_⟩
  intro hLw hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U E V T signed hU hEpos hV hUV hE hZupper
    hTscale hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad
  classical
  let K := Finset.Icc a b
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let d := sourceOriginalLiteralDepth 20 L
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
    parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta (Nat.ceil (6*U*V)) m K k
  let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
    parityOriginalHistoricalUngatedSourceToSigma434
  have hLpos : 0<L := by linarith
  have hTpos : 0<T := by
    rw [hTscale]
    exact Real.rpow_pos_of_pos hLpos _
  have hTCut : T≤L^Cf := by rw [hTscale]
  have hTghost : T=L^(X+Dghost) := by rw [hTscale,hCfX]
  have hGhostBound := hGhostL.2 hLw Z hZlo hZhi k hk hkBound
    Dghost U E V K0 Cbox A hDghost hK0 hU hV hUV hE
    (by linarith : 0≤Cbox) hMainL.2.1 hZupper hA
    buf hSmooth hSupport
    (by simpa only [J1] using hBE1)
    (by simpa only [J1] using hBN1)
    R hR hCube
  let Err : ℝ :=
    (L^(2*parityOriginalW1PolylogExponent434)*
      ((Nat.ceil (65*Z):ℕ):ℝ)*
      (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
      (parityOriginal3DSourceMomentFiniteBudget434 1 f/T)
  have hErr : Err≤66*Z*Cmoment1*
      L^(2*parityOriginalW1PolylogExponent434+30-Dghost) := by
    dsimp only [Err]
    rw [hTghost]
    convert hGhostBound using 1
  have hTwoGhost : 2*Err≤132*Z*Cmoment1*L^(-D) :=
    parity_original_actual_two_ghost_precision_algebra434
      L Z D Cmoment1 Err hLw (by simpa only [Dghost] using hErr)
  have hMainBound := hMainL.2.2.2.2 hLw hFamily Z hZlo hZhi band hBand
    slot delta freq k hk hkBound rho xi1 xi2 xi3 U E V T signed
    hU hEpos hV hUV hE hZupper hTpos hTCut
    hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad 1
  dsimp only at hMainBound hTwoGhost ⊢
  calc
    _ ≤ Cmoment*Z*L^(-D)+2*Err := by
      simpa only [Err,pow_one] using hMainBound
    _ ≤ Cmoment*Z*L^(-D)+132*Z*Cmoment1*L^(-D) :=
      add_le_add_right hTwoGhost _
    _ = (Cmoment+132*Cmoment1)*Z*L^(-D) := by ring
end Green64Analytic.Parity

end

end

/-! ## QuarterBprimeKZNorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- This is the actual original B' source Fourier signal summed over
both dyadic scales permitted by its ORIGINAL C-infinity ψ(z/Z)
support 1<z/Z<4. The source coefficient, character projector, and
five-factor Schwartz kernel are unchanged; only the **index set**
is the proved complete smooth ψ neighbor envelope. Price: at most
2(2N+1)(floor(log2 Y)+1) per original fine family. -/
theorem parity_eventually_original_actual_Bprime_fine_smooth_psi_neighbor_kZ_norm_quarter434
    (jQ : ℕ) (D C0 Cf CZ Ck beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
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
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        ∀ (KS : Finset ℤ) (N Y : ℕ) (ZS : Finset ℕ),
          (∀k∈KS, k≠0 ∧ k.natAbs≤N ∧ (k.natAbs:ℝ)≤L^Ck) →
          (∀z∈ZS, 0<z ∧ z≤Y) →
          (∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
            Real.exp L*L^(-CZ)≤(Z:ℝ) ∧
            (Z:ℝ)≤Real.exp L*L^CZ ∧
            (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88)) →
          (∀k∈KS,∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
            |((2*k:ℤ):ℝ)|≤(Z:ℝ)/128) →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
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
          (((2*N+1:ℕ):ℝ)*((2*(Nat.log 2 Y+1):ℕ):ℝ))*
            (Cmoment+132*Cmoment1)*(Y:ℝ)*L^(-D) := by
  obtain ⟨J,B,S,hBS,hLocal⟩ :=
    parity_eventually_original_actual_Bprime_full_odd_fixed_KZ_any_log_saving_quarter434
      jQ D C0 Cf CZ Ck beta gamma K0 Cbox A R
      hD hCf hCZ hCk hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hC0 : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hC1 : 0≤Cmoment1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hC : 0≤Cmoment+132*Cmoment1 := by linarith
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hLocal] with L hL
  refine ⟨hL.1,hL.2.1,hL.2.2.1,hL.2.2.2.1,?_⟩
  intro hLw hFamily band hBand slot delta freq rho xi1 xi2 xi3
    U E V T signed hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyad
    KS N Y ZS hKS hZS hZwindow hkZwindow
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let F : ℤ → ℕ → ℂ := fun k Z =>
    parityOriginalActualBprimeFineLowfreqSignal434
      d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
      rho xi1 xi2 xi3 T signed buf A hSmooth hSupport
  have hKBound : ∀k∈KS,k.natAbs≤N := by
    intro k hk
    exact (hKS k hk).2.1
  have hZBound : ∀z∈ZS,z≤Y := by
    intro z hz
    exact (hZS z hz).2
  have hZPositive : ∀z∈ZS,0<z := by
    intro z hz
    exact (hZS z hz).1
  have hPosL : 0<L := by linarith
  have hCell : ∀k∈KS,∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
      ‖F k Z‖≤(Cmoment+132*Cmoment1)*(Z:ℝ)*L^(-D) := by
    intro k hk Z hz
    have hkk := hKS k hk
    have hzz := hZwindow Z hz
    have hkz := hkZwindow k hk Z hz
    have hOne := hL.2.2.2.2 hLw hFamily (Z:ℝ) hzz.1 hzz.2.1
      band hBand slot delta freq k hkk.1 hkk.2.2
      rho xi1 xi2 xi3 U E V T signed
      hU hEpos hV hUV hEscale hzz.2.2 hT
      hrho hxi1 hxi2 hxi3 hkz
      prime lFine uFine a b hFineLow hl hu huExp hDyad
    dsimp only at hOne ⊢
    change ‖F k Z‖ ≤ (Cmoment+132*Cmoment1)*(Z:ℝ)*L^(-D)
    simpa only [F,parityOriginalActualBprimeFineLowfreqSignal434] using hOne
  have hSum :=
    parity_original_actual_signed_k_smooth_psi_neighbor_global_norm_bound434
      L D (Cmoment+132*Cmoment1) hPosL hC KS N hKBound ZS Y hZBound
      hZPositive F hCell
  simpa only [F,d,K,alpha,Cmoment,Cmoment1] using hSum
end Green64Analytic.Parity

end

end

/-! ## QuarterBprimeKZAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- For one ORIGINAL Q band/slot, one fine b629 interval and fixed
allocation/frequency family, the entire real signed k × source-dyadic Z
post-Cauchy B' low-frequency complex sum has arbitrary source-log
saving O(exp(L)L^(-Agoal)). The precision D is chosen BEFORE the
spectral J,B,S and L. The only new hypotheses on the finite k/Z
carriers are the concrete original integer cap N<=ceil(L^Ck), the
real source z cap Y<=25 Cbox exp(L)L^(K0+88), and logY<=2L;
all are geometry, not a TypeII/correlation assumption. This does NOT
claim original Cauchy, high Fourier tail, or all fine-cell families. -/
theorem parity_eventually_original_actual_Bprime_fine_smooth_psi_neighbor_kZ_any_log_quarter434
    (jQ : ℕ) (Agoal D C0 Cf CZ Ck beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D) (hPrecision : Agoal+Ck+K0+90≤D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
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
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        ∀ (KS : Finset ℤ) (N Y : ℕ) (ZS : Finset ℕ),
          (∀k∈KS, k≠0 ∧ k.natAbs≤N ∧ (k.natAbs:ℝ)≤L^Ck) →
          (∀z∈ZS, 0<z ∧ z≤Y) →
          (∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
            Real.exp L*L^(-CZ)≤(Z:ℝ) ∧
            (Z:ℝ)≤Real.exp L*L^CZ ∧
            (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88)) →
          (∀k∈KS,∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
            |((2*k:ℤ):ℝ)|≤(Z:ℝ)/128) →
          N≤Nat.ceil (L^Ck) →
          (Y:ℝ)≤25*Cbox*Real.exp L*L^(K0+88) →
          1≤Y → Real.log (Y:ℝ)≤2*L →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
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
  obtain ⟨J,B,S,hBS,hGlobal⟩ :=
    parity_eventually_original_actual_Bprime_fine_smooth_psi_neighbor_kZ_norm_quarter434
      jQ D C0 Cf CZ Ck beta gamma K0 Cbox A R
      hD hCf hCZ hCk hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hC0 : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hC1 : 0≤Cmoment1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hC : 0≤Cmoment+132*Cmoment1 := by linarith
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hGlobal] with L hL
  refine ⟨hL.1,hL.2.1,hL.2.2.1,hL.2.2.2.1,?_⟩
  intro hLw hFamily band hBand slot delta freq rho xi1 xi2 xi3
    U E V T signed hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyad
    KS N Y ZS hKS hZS hZwindow hkZwindow hN hY hYpos hLogY
  have hBound := hL.2.2.2.2 hLw hFamily band hBand slot delta freq
    rho xi1 xi2 xi3 U E V T signed hU hEpos hV hUV hEscale
    hT hrho hxi1 hxi2 hxi3 prime lFine uFine a b
    hFineLow hl hu huExp hDyad KS N Y ZS hKS hZS hZwindow hkZwindow
  have hNumeric := parity_original_actual_kZ_counted_loss_absorbed434
    L Agoal D (Cmoment+132*Cmoment1) Ck K0 Cbox N Y
    (by linarith : 1≤L) hC hCk hK0 hCbox hN hY hYpos hLogY hPrecision
  let Q : ℝ := (((2*N+1:ℕ):ℝ)*((Nat.log 2 Y+1:ℕ):ℝ))*
     (Cmoment+132*Cmoment1)*(Y:ℝ)*L^(-D)
  have hTwice :
      (((2*N+1:ℕ):ℝ)*((2*(Nat.log 2 Y+1):ℕ):ℝ))*
        (Cmoment+132*Cmoment1)*(Y:ℝ)*L^(-D) = 2*Q := by
    dsimp [Q]; push_cast; ring
  have hTwiceBound :
      2*Q ≤ (250*Cbox*(1+2/Real.log 2)*(Cmoment+132*Cmoment1))*
        Real.exp L*L^(-Agoal) := by
    calc
      2*Q ≤ 2*((125*Cbox*(1+2/Real.log 2)*
          (Cmoment+132*Cmoment1))*Real.exp L*L^(-Agoal)) :=
        mul_le_mul_of_nonneg_left hNumeric (by norm_num)
      _ = _ := by ring
  dsimp only at hBound ⊢
  exact hBound.trans (hTwice ▸ hTwiceBound)
end Green64Analytic.Parity

end

end

/-! ## SecondProxyBetaNorm -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Literal original prime OR rough full-cell proxy B_I on a
restricted factor interval, with the original complete log-cell
normalizer. B_I is NOT recomputed on this interval. -/
def parityOriginalActualFullCellProxyBeta434
    (prime : Bool) (L S gamma : ℝ) (a b n : ℕ) : ℂ :=
  if n∈Finset.Icc a b then
    ((if prime then
       b627PrimeFullProxy434 (L^(-S)) (Real.exp (Real.sqrt L)) n
     else
       sourceD20FullProxy (L^(-S)) (Real.exp (Real.sqrt L))
         ((Real.exp L)^gamma) n : ℝ):ℂ)
  else 0

/-- Actual original sharp I on the SAME source factor interval. -/
def parityOriginalActualFullCellSharpTest434
    (prime : Bool) (L gamma : ℝ) (a b n : ℕ) : ℂ :=
  if n∈Finset.Icc a b then
    ((if prime then (if n.Prime then (1:ℝ) else 0)
      else sourceD19RoughTest ((Real.exp L)^gamma) n : ℝ):ℂ)
  else 0

/-- Exact Parity §7.1 identity I = B_I + (I-B_I) on the whole
original factor interval, including both cut endpoints. -/
theorem parity_original_actual_fullcell_proxy_plus_delta_eq_test434
    (prime : Bool) (L S gamma : ℝ) (a b n : ℕ) :
    parityOriginalActualFullCellProxyBeta434 prime L S gamma a b n +
    parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b n =
    parityOriginalActualFullCellSharpTest434 prime L gamma a b n := by
  classical
  by_cases hn : n∈Finset.Icc a b
  · cases prime
    · simp [parityOriginalActualFullCellProxyBeta434,
        parityOriginalActualFullCellSharpTest434,
        parityOriginalActualFullDyadProxyDifference434,hn,sub_eq_add_neg] <;> ring
    · simp [parityOriginalActualFullCellProxyBeta434,
        parityOriginalActualFullCellSharpTest434,
        parityOriginalActualFullDyadProxyDifference434,hn,sub_eq_add_neg] <;> ring
  · simp [parityOriginalActualFullCellProxyBeta434,
      parityOriginalActualFullCellSharpTest434,
      parityOriginalActualFullDyadProxyDifference434,hn]

/-- The original sharp test has literal complex modulus 0 or 1. -/
theorem parity_original_actual_fullcell_sharp_test_norm_le_one434
    (prime : Bool) (L gamma : ℝ) (a b n : ℕ) :
    ‖parityOriginalActualFullCellSharpTest434 prime L gamma a b n‖≤1 := by
  classical
  by_cases hn : n∈Finset.Icc a b
  · cases prime
    · by_cases ht : 2≤n ∧ (Real.exp L)^gamma<(n.minFac:ℝ)
      · simp [parityOriginalActualFullCellSharpTest434,
          sourceD19RoughTest,hn,ht]
      · simp [parityOriginalActualFullCellSharpTest434,
          sourceD19RoughTest,hn,ht]
    · by_cases hp : n.Prime
      · simp [parityOriginalActualFullCellSharpTest434,hn,hp]
      · simp [parityOriginalActualFullCellSharpTest434,hn,hp]
  · simp [parityOriginalActualFullCellSharpTest434,hn]

/-- Source mathematical second-replacement bridge: original full-cell
proxy B_I has modulus at most TWO, because the original sharp I has
modulus <=1 and the true full-cell discrepancy (I-B_I) has <=1.
We do not assume B_I<=1 or smoothness of the already replaced
factor. -/
theorem parity_original_actual_fullcell_proxy_beta_norm_le_two434
    (prime : Bool) (L S gamma : ℝ) (a b n : ℕ)
    (hAlpha : ‖parityOriginalActualFullDyadProxyDifference434
      prime L S gamma a b n‖≤1) :
    ‖parityOriginalActualFullCellProxyBeta434 prime L S gamma a b n‖≤2 := by
  have hId := parity_original_actual_fullcell_proxy_plus_delta_eq_test434
    prime L S gamma a b n
  have hT := parity_original_actual_fullcell_sharp_test_norm_le_one434
    prime L gamma a b n
  have hDiff :
      parityOriginalActualFullCellProxyBeta434 prime L S gamma a b n =
      parityOriginalActualFullCellSharpTest434 prime L gamma a b n -
        parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b n := by
    apply eq_sub_iff_add_eq.mpr
    exact hId
  rw [hDiff]
  exact (norm_sub_le _ _).trans (by linarith)

/-- The nonsmooth second proxy, normalized by 2, meets the EXACT
arbitrary beta norm <=1 gate of the original signed b629 Type II
estimate, uniformly on every original n, with no source-family
cardinality input. -/
theorem parity_original_actual_second_proxy_beta_half_norm_le_one434
    (prime : Bool) (L S gamma : ℝ) (a b n : ℕ)
    (hAlpha : ‖parityOriginalActualFullDyadProxyDifference434
      prime L S gamma a b n‖≤1) :
    ‖parityOriginalActualFullCellProxyBeta434 prime L S gamma a b n / (2:ℂ)‖≤1 := by
  have hp := parity_original_actual_fullcell_proxy_beta_norm_le_two434
    prime L S gamma a b n hAlpha
  rw [norm_div]
  norm_num at ⊢
  linarith
end Green64Analytic.Parity

end

end

/-! ## SecondProxyBetaUniform -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1900000

/-- Parity §7.3 second replacement: the ALREADY nonsmooth original
full-cell prime/rough proxy is uniformly bounded by 2, and its
normalization by two satisfies the true native beta ℓ∞≤1 gate.
Unlike a conditional β lemma, this is a complete eventual result
from the original source b629 full-cell discrepancy and sharp-test
bound; valid for all original n and both prime/rough cases. -/
theorem parity_eventually_original_actual_fullcell_second_proxy_beta_uniform434
    (S beta gamma : ℝ) (hS : 0<S)
    (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (prime : Bool) (a b : ℕ),
        Real.exp (beta*L)≤(a:ℝ) →
      ∀ n : ℕ,
        ‖parityOriginalActualFullCellProxyBeta434 prime L S gamma a b n‖≤2 ∧
        ‖parityOriginalActualFullCellProxyBeta434 prime L S gamma a b n/(2:ℂ)‖≤1 := by
  filter_upwards [parity_eventually_original_full_dyad_proxy_norm_rough434
      S beta gamma hS hbeta hgamma] with L hFull
  intro prime a b ha n
  have hAlpha := (hFull prime a b ha n).1
  exact ⟨parity_original_actual_fullcell_proxy_beta_norm_le_two434
      prime L S gamma a b n hAlpha,
    parity_original_actual_second_proxy_beta_half_norm_le_one434
      prime L S gamma a b n hAlpha⟩
end Green64Analytic.Parity

end

end

/-! ## SignedPhysicalPairSourceExact -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- The LITERAL original signed epsilon/factorial source, including
its Mellin phase, is exactly the finite physical shifted m*n=u+2
pair sum. This is not an identification with unsigned sourceOriginalA.
All native signed source coefficients parityOriginalSignedSourceA434
and phase sourceOriginalPureMellinPhase434 stay unchanged. -/
theorem parity_original_signed_source_eq_physical_pair_triple434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) :
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J alpha beta signed rho Y =
    ∑ z ∈ parityOriginalTypeIIPhysicalPairs434 K J Y,
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
          (sourceOriginalPureMellinPhase434 rho u *
            (((parityOriginalSignedSourceA434 d L signed u *
              Psi ((u:ℝ)/Real.exp L):ℝ):ℂ))) *
            (alpha z.1*beta z.2)
        else 0 := by
  classical
  let W : ℕ → ℂ := fun u =>
    sourceOriginalPureMellinPhase434 rho u *
      (((parityOriginalSignedSourceA434 d L signed u *
        Psi ((u:ℝ)/Real.exp L):ℝ):ℂ))
  let F : (ℕ×ℕ) → ℕ → ℂ := fun z u =>
    if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
      W u*(alpha z.1*beta z.2) else 0
  have hPsi0 : Psi 0=0 := by
    by_contra hNonzero
    have hmem : (0:ℝ)∈Function.support Psi := hNonzero
    have hh := Set.mem_Icc.mp (hPsi hmem)
    norm_num at hh
  have hW0 : W 0=0 := by simp [W,hPsi0]
  have hFibre (u : ℕ) :
      W u*(∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        alpha z.1*beta z.2) =
      ∑ z ∈ K.product J,F z u := by
    unfold parityOriginalShiftTwoPositivePairFibre434
    rw [Finset.mul_sum,Finset.sum_filter]
  have hRange (z : ℕ×ℕ) (T : ℕ) :
      (∑u∈Finset.range (T+1),F z u) =
      ∑u∈Finset.Ioc 0 T,F z u := by
    induction T with
    | zero => simp [F,hW0]
    | succ T ih =>
      rw [Finset.sum_range_succ]
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le T)]
      rw [ih]
  have hPhysical :
      (∑ z ∈ K.product J,∑ u ∈ Finset.Ioc 0 Y,F z u) =
      (∑ z ∈ parityOriginalTypeIIPhysicalPairs434 K J Y,
        ∑ u ∈ Finset.Ioc 0 Y,F z u) := by
    unfold parityOriginalTypeIIPhysicalPairs434
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases h : ∃u∈Finset.Ioc 0 Y,0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2
    · rw [if_pos h]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro u hu
      have hn : ¬(0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2) := by
        intro hc
        exact h ⟨u,hu,hc⟩
      simp [F,hn]
  change (∑u∈Finset.range (Y+1),
      W u*(∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        alpha z.1*beta z.2)) =
    ∑z∈parityOriginalTypeIIPhysicalPairs434 K J Y,
      ∑u∈Finset.Ioc 0 Y,F z u
  calc
    _ = ∑u∈Finset.range (Y+1),∑z∈K.product J,F z u := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hFibre u
    _ = ∑z∈K.product J,∑u∈Finset.range (Y+1),F z u :=
      Finset.sum_comm
    _ = ∑z∈K.product J,∑u∈Finset.Ioc 0 Y,F z u := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hRange z Y
    _ = _ := hPhysical
end Green64Analytic.Parity

end

end

/-! ## SignedQuarterPhysicalFibres -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2600000

/-- A TRUE signed factorial/epsilon Mellin source physical fibre is
ZERO outside the actual quarter product UV window, by original
Ψ(u/exp L) compact support; the sign and Mellin phase are untouched. -/
theorem parity_original_signed_nonquarter_physical_fibre_zero434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (hL : 0≤L) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (Y : ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (scale : ℕ×ℕ)
    (hOutside : ¬parityOriginalTypeIIQuarterProductGate434 L scale) :
    (∑ z ∈ (parityOriginalTypeIIPhysicalPairs434 K J Y).filter
      (fun z => (parityOriginalHistoricalActualZDyadicScale434 z.1,
        parityOriginalHistoricalActualZDyadicScale434 z.2) = scale),
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
          (sourceOriginalPureMellinPhase434 rho u *
            (((parityOriginalSignedSourceA434 d L signed u *
              Psi ((u:ℝ)/Real.exp L):ℝ):ℂ))) *
            (alpha z.1*beta z.2)
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
    have hPsiZero : Psi ((u:ℝ)/Real.exp L)=0 := by
      by_contra hNonzero
      exact hOutside (parity_original_TypeII_psi_physical_dyad_UV_true_bounds434
        L (scale.1:ℝ) (scale.2:ℝ) Psi hL hPsi z.1 z.2 u
        hEq.1 hEq.2.1 hEq.2.2 hNonzero
        hBounds.1 hBounds.2.1 hBounds.2.2.1 hBounds.2.2.2)
    simp [hEq,hPsiZero]
  · simp [hEq]

/-- Genuine source signed ε source equals the finite quarter-gated
sum of its actual physically attained m,n dyadic pair fibres. No
unsigned-to-signed identification, selected-band or χ assumption. -/
theorem parity_original_signed_source_eq_quarter_physical_fibres434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (hL : 0≤L) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (Y : ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) :
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J alpha beta signed rho Y =
    ∑ scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
      (parityOriginalTypeIIPhysicalPairs434 K J Y)).filter
        (parityOriginalTypeIIQuarterProductGate434 L),
      ∑ z ∈ (parityOriginalTypeIIPhysicalPairs434 K J Y).filter
        (fun z => (parityOriginalHistoricalActualZDyadicScale434 z.1,
          parityOriginalHistoricalActualZDyadicScale434 z.2) = scale),
        ∑ u ∈ Finset.Ioc 0 Y,
          if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
            (sourceOriginalPureMellinPhase434 rho u *
              (((parityOriginalSignedSourceA434 d L signed u *
                Psi ((u:ℝ)/Real.exp L):ℝ):ℂ))) *
              (alpha z.1*beta z.2)
          else 0 := by
  classical
  rw [parity_original_signed_source_eq_physical_pair_triple434
    d L Psi hPsi K J alpha beta signed rho Y]
  let S := parityOriginalTypeIIPhysicalPairs434 K J Y
  let f : ℕ×ℕ → ℕ×ℕ := fun z =>
    (parityOriginalHistoricalActualZDyadicScale434 z.1,
      parityOriginalHistoricalActualZDyadicScale434 z.2)
  let G : ℕ×ℕ → ℂ := fun z =>
    ∑ u ∈ Finset.Ioc 0 Y,
      if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
        (sourceOriginalPureMellinPhase434 rho u *
          (((parityOriginalSignedSourceA434 d L signed u *
            Psi ((u:ℝ)/Real.exp L):ℝ):ℂ))) *
          (alpha z.1*beta z.2)
      else 0
  have hMaps : ∀z∈S,f z∈S.image f := fun z hz => Finset.mem_image_of_mem f hz
  have hSplit : (∑ z∈S,G z) =
      ∑ scale ∈ S.image f,∑ z ∈ S.filter (fun z => f z=scale),G z :=
    (Finset.sum_fiberwise_of_maps_to hMaps G).symm
  change (∑z∈S,G z) =
    ∑scale∈(S.image f).filter (parityOriginalTypeIIQuarterProductGate434 L),
      ∑z∈S.filter (fun z => f z=scale),G z
  rw [hSplit,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro scale hs
  by_cases hQuarter : parityOriginalTypeIIQuarterProductGate434 L scale
  · simp [hQuarter]
  · simp only [if_neg hQuarter]
    exact parity_original_signed_nonquarter_physical_fibre_zero434
      d L Psi hL hPsi K J Y alpha beta signed rho scale hQuarter
end Green64Analytic.Parity

end

end

/-! ## SignedQuarterCutSources -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- One actual signed physical binary scale fibre is exactly the
same original signed factorial/epsilon source on the corresponding
literal factor K,J scale restrictions, with all signed source terms
and Mellin phase unchanged. -/
theorem parity_original_signed_physical_fibre_eq_scale_cut_source434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (Y : ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (scale : ℕ×ℕ) :
    (∑ z ∈ (parityOriginalTypeIIPhysicalPairs434 K J Y).filter
      (fun z => (parityOriginalHistoricalActualZDyadicScale434 z.1,
        parityOriginalHistoricalActualZDyadicScale434 z.2) = scale),
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
          (sourceOriginalPureMellinPhase434 rho u *
            (((parityOriginalSignedSourceA434 d L signed u *
              Psi ((u:ℝ)/Real.exp L):ℝ):ℂ))) *
            (alpha z.1*beta z.2)
        else 0) =
    parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
      (K.filter (fun m => parityOriginalHistoricalActualZDyadicScale434 m=scale.1))
      (J.filter (fun n => parityOriginalHistoricalActualZDyadicScale434 n=scale.2))
      alpha beta signed rho Y := by
  rw [parity_original_TypeII_fibre_eq_scale_filtered_pair_carrier434]
  exact (parity_original_signed_source_eq_physical_pair_triple434
    d L Psi hPsi _ _ alpha beta signed rho Y).symm

/-- The complete ORIGINAL signed source equals exact finite sum of
its genuinely attained quarter-UV signed sources on actual K/J
scale cuts, not an inferred unsigned correspondence. -/
theorem parity_original_signed_source_eq_quarter_scale_cut_sources434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (hL : 0≤L)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (Y : ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) :
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J alpha beta signed rho Y =
    ∑ scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
        (parityOriginalTypeIIPhysicalPairs434 K J Y)).filter
          (parityOriginalTypeIIQuarterProductGate434 L),
      parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
        (K.filter (fun m => parityOriginalHistoricalActualZDyadicScale434 m=scale.1))
        (J.filter (fun n => parityOriginalHistoricalActualZDyadicScale434 n=scale.2))
        alpha beta signed rho Y := by
  rw [parity_original_signed_source_eq_quarter_physical_fibres434
    d L Psi hL hPsi K J Y alpha beta signed rho]
  apply Finset.sum_congr rfl
  intro scale hs
  exact parity_original_signed_physical_fibre_eq_scale_cut_source434
    d L Psi hPsi K J Y alpha beta signed rho scale

/-- On literal positive original whole K,J intervals, the complete
signed h=-2 source is exactly the sum over actually attained
quarter-product binary nested Icc cuts, with NO signed/unsigned
Q-weight identification and no recomputation of full-cell B_I. -/
theorem parity_original_signed_positive_Icc_eq_quarter_nested_sources434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (hL : 0≤L)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (a b c e Y : ℕ) (ha : 0<a) (hc : 0<c)
    (alpha beta : ℕ → ℂ) (signed : Bool) (rho : ℝ) :
    parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
      (Finset.Icc a b) (Finset.Icc c e) alpha beta signed rho Y =
    ∑ scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
        (parityOriginalTypeIIPhysicalPairs434
          (Finset.Icc a b) (Finset.Icc c e) Y)).filter
          (parityOriginalTypeIIQuarterProductGate434 L),
      parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
        (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
        (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
        alpha beta signed rho Y := by
  rw [parity_original_signed_source_eq_quarter_scale_cut_sources434
    d L Psi hL hPsi (Finset.Icc a b) (Finset.Icc c e)
    Y alpha beta signed rho]
  apply Finset.sum_congr rfl
  intro scale hs
  have hPair := parity_original_TypeII_positive_Icc_scale_fibre_eq_nested434
    a b c e Y ha hc scale (Finset.mem_filter.mp hs).1
  rw [hPair.1,hPair.2]
end Green64Analytic.Parity

end

end

/-! ## SignedSourceSwapFactors -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Literal shifted mn=u+2 positive pair fibre is symmetric in
the two original factors, at the level of the COMPLETE finite
signed coefficient sum. No estimate, smoothing, character change
or ambiparityus multiplicity is inserted. -/
theorem parity_original_positive_shifted_fibre_swap_factors434
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (u : ℕ) :
    (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
      alpha z.1*beta z.2) =
    (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 J K u,
      beta z.1*alpha z.2) := by
  classical
  unfold parityOriginalShiftTwoPositivePairFibre434
  rw [Finset.sum_filter,Finset.sum_filter]
  have hLeft :
      (∑ a ∈ K.product J,
        if 0 < a.1 ∧ 0 < a.2 ∧ a.1*a.2=u+2 then
          alpha a.1*beta a.2 else 0) =
      ∑ m ∈ K, ∑ n ∈ J,
        if 0 < m ∧ 0 < n ∧ m*n=u+2 then
          alpha m*beta n else 0 :=
    Finset.sum_product K J (fun a : ℕ×ℕ =>
      if 0 < a.1 ∧ 0 < a.2 ∧ a.1*a.2=u+2 then
        alpha a.1*beta a.2 else 0)
  have hRight :
      (∑ a ∈ J.product K,
        if 0 < a.1 ∧ 0 < a.2 ∧ a.1*a.2=u+2 then
          beta a.1*alpha a.2 else 0) =
      ∑ n ∈ J, ∑ m ∈ K,
        if 0 < n ∧ 0 < m ∧ n*m=u+2 then
          beta n*alpha m else 0 :=
    Finset.sum_product J K (fun a : ℕ×ℕ =>
      if 0 < a.1 ∧ 0 < a.2 ∧ a.1*a.2=u+2 then
        beta a.1*alpha a.2 else 0)
  rw [hLeft,hRight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  have hCond : (0 < m ∧ 0 < n ∧ m*n=u+2) ↔
      (0 < n ∧ 0 < m ∧ n*m=u+2) := by
    constructor
    · rintro ⟨hm,hn,hprod⟩
      exact ⟨hn,hm,by simpa only [mul_comm] using hprod⟩
    · rintro ⟨hn,hm,hprod⟩
      exact ⟨hm,hn,by simpa only [mul_comm] using hprod⟩
  by_cases h : 0 < m ∧ 0 < n ∧ m*n=u+2
  · have h2 : 0 < n ∧ 0 < m ∧ n*m=u+2 := hCond.mp h
    simp only [if_pos h, if_pos h2]
    ring
  · have h2 : ¬(0 < n ∧ 0 < m ∧ n*m=u+2) := by
      intro hh
      exact h (hCond.mpr hh)
    simp only [if_neg h,if_neg h2]

/-- The original signed epsilon/factorial 20! Parity source itself
is EXACTLY invariant under exchanging both factor supports and
their complex coefficients. Crucial for applying first-factor TypeII
with the nonsmooth B_I on the *other* factor in §7.3. -/
theorem parity_original_signed_source_swap_factors434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) :
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J alpha beta signed rho Y =
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi J K beta alpha signed rho Y := by
  unfold parityOriginalShiftTwoSignedBilinearMellinSource434
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_original_positive_shifted_fibre_swap_factors434]

/-- The original unsigned Parity(4.2) literal triple source factor
exchange is separately formalized; not conflated with the signed
Q/P factorial source. -/
theorem parity_original_unsigned_TypeII_triple_swap_factors434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J alpha beta Y =
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi J K beta alpha Y := by
  classical
  unfold parityOriginalShiftTwoOriginalTypeIITripleSource434
  have hLeft :
      (∑ z ∈ K.product J,
        ∑ u ∈ Finset.Ioc 0 Y,
          if 0 < z.1 ∧ 0 < z.2 ∧ z.1*z.2=u+2 then
            (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
              (sourceOriginalPAllActualBands 20 L) u *
              Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
              (alpha z.1*beta z.2)) else 0) =
      ∑ m ∈ K, ∑ n ∈ J,
        ∑ u ∈ Finset.Ioc 0 Y,
          if 0 < m ∧ 0 < n ∧ m*n=u+2 then
            (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
              (sourceOriginalPAllActualBands 20 L) u *
              Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
              (alpha m*beta n)) else 0 :=
    Finset.sum_product K J (fun z : ℕ×ℕ =>
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0 < z.1 ∧ 0 < z.2 ∧ z.1*z.2=u+2 then
          (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
            (sourceOriginalPAllActualBands 20 L) u *
            Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
            (alpha z.1*beta z.2)) else 0)
  have hRight :
      (∑ z ∈ J.product K,
        ∑ u ∈ Finset.Ioc 0 Y,
          if 0 < z.1 ∧ 0 < z.2 ∧ z.1*z.2=u+2 then
            (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
              (sourceOriginalPAllActualBands 20 L) u *
              Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
              (beta z.1*alpha z.2)) else 0) =
      ∑ n ∈ J, ∑ m ∈ K,
        ∑ u ∈ Finset.Ioc 0 Y,
          if 0 < n ∧ 0 < m ∧ n*m=u+2 then
            (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
              (sourceOriginalPAllActualBands 20 L) u *
              Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
              (beta n*alpha m)) else 0 :=
    Finset.sum_product J K (fun z : ℕ×ℕ =>
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0 < z.1 ∧ 0 < z.2 ∧ z.1*z.2=u+2 then
          (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
            (sourceOriginalPAllActualBands 20 L) u *
            Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
            (beta z.1*alpha z.2)) else 0)
  rw [hLeft,hRight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro u hu
  have hCond : (0 < m ∧ 0 < n ∧ m*n=u+2) ↔
      (0 < n ∧ 0 < m ∧ n*m=u+2) := by
    constructor
    · rintro ⟨hm,hn,hprod⟩
      exact ⟨hn,hm,by simpa only [mul_comm] using hprod⟩
    · rintro ⟨hn,hm,hprod⟩
      exact ⟨hm,hn,by simpa only [mul_comm] using hprod⟩
  by_cases h : 0 < m ∧ 0 < n ∧ m*n=u+2
  · have h2 := hCond.mp h
    simp only [if_pos h,if_pos h2]
    ring
  · have h2 : ¬(0 < n ∧ 0 < m ∧ n*m=u+2) := by
      intro hh
      exact h (hCond.mpr hh)
    simp only [if_neg h,if_neg h2]
end Green64Analytic.Parity

end

end

/-! ## SignedTwoFactorProxyTelescoping -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1700000

/-- EXACT native original signed factorial Parity source two-factor
replacement: replacing both nonsmooth factor tests is the sum of
FIRST discrepancy (I1−B1) against the sharp second factor, and
SECOND discrepancy (I2−B2) against the ALREADY REPLACED first
nonsmooth B1. No smoothness on B1 or B2 and NO fabricated ∞-norm
bound; all u,m,n,rho,epsilon, Q/P and original shifted h=-2 weights
stay unchanged. The sum may be complex and signed, but this uses
only exact linearity, not a false comparison of signed subsums. -/
theorem parity_original_signed_two_factor_proxy_telescoping434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (sharpM proxyM sharpN proxyN : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) :
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J sharpM sharpN signed rho Y -
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J proxyM proxyN signed rho Y =
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J (fun m => sharpM m - proxyM m) sharpN signed rho Y +
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J proxyM (fun n => sharpN n - proxyN n) signed rho Y := by
  classical
  unfold parityOriginalShiftTwoSignedBilinearMellinSource434
  rw [←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Finset.mul_sum]
  rw [←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- The corresponding native two-factor replacement for the
UNSIGNED original shifted Parity(4.2) triple retains sourceOriginalA,
original smooth Psi and mn=u+2 exactly. The two source identities
are distinct, and are deliberately not conflated. -/
theorem parity_original_unsigned_two_factor_proxy_telescoping434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (sharpM proxyM sharpN proxyN : ℕ → ℂ)
    (Y : ℕ) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J sharpM sharpN Y -
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J proxyM proxyN Y =
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J (fun m => sharpM m - proxyM m) sharpN Y +
    parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J proxyM (fun n => sharpN n - proxyN n) Y := by
  classical
  unfold parityOriginalShiftTwoOriginalTypeIITripleSource434
  rw [←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rw [←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : 0 < z.1 ∧ 0 < z.2 ∧ z.1*z.2=u+2
  · simp only [if_pos h]
    ring
  · simp [h]
end Green64Analytic.Parity

end

end

/-! ## SourcePhysicalZScaleQuarter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- Original Parity(4.14) TRUE full-odd source z=m'*(mn−2)/e
under corrected CAP-FREE B'(4.7) containing source box:

   exp(L)/32 * L^K0 < z < 24*Cbox*exp(L)*L^(K0+88).

The lower support uses the true positive η_n window and
exp L≤4UV, not the stronger and false-on-some-dyads UV≥exp L. The upper uses m≤2U,n<3V,
UV≤Cbox expL and e>E L^-88/2, NOT old u≤floor(2expL).
This is the mathematically correct physical source Z window
for arbitrary fixed original UV≈expL, with no exponential
penalty and no false reuse of the previous gated Y0 proof.
The factor Cbox is fixed geometry; it can later be absorbed into
a fixed logarithmic exponent when L sufficiently large. -/
theorem parity_original_historical_ungated_source_box_smoothed_physical_z_scale_quarter434
    (L U V E K0 Cbox : ℝ) (e m mp n u z : ℕ)
    (hL : 32≤L) (hU : 0<U) (hV : 0<V) (hCbox : 0<Cbox)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V
      (by linarith : 8≤L) e n≠0)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)<2*U)
    (hmpLo : U≤(mp:ℝ))
    (hmpHi : (mp:ℝ)<2*U)
    (hu : u∈parityOriginalHistoricalFixedMNUSupport434
      (Nat.ceil (6*U*V)) m n)
    (hEz : e*z=mp*u) :
    (Real.exp L/32)*L^K0 < (z:ℝ) ∧
    (z:ℝ) < 24*Cbox*Real.exp L*L^(K0+88) := by
  have hL8 : 8≤L := by linarith
  have hLp : 0<L := by linarith
  have hKpos : 0<L^K0 := Real.rpow_pos_of_pos hLp _
  have hInvpos : 0<L^(-88:ℝ) := Real.rpow_pos_of_pos hLp _
  have hEpos : 0<E := by rw [hE];exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  obtain ⟨heLo,heHi,hnLo,hnHi⟩ :=
    parity_original_historical_full_odd_nonzero_smooth_e_n_ranges434
      L E V hL8 hEpos hV e n hw
  have hePos : 0<(e:ℝ) :=
    (by positivity : 0<E*L^(-88:ℝ)/2).trans heLo
  have hnPos : 0≤(n:ℝ) := Nat.cast_nonneg _
  have huNat := (Finset.mem_filter.mp hu).2.2.2
  have huReal : (m:ℝ)*(n:ℝ)=(u:ℝ)+2 := by exact_mod_cast huNat
  have hX8 : (32:ℝ)≤Real.exp L := by
    have hx := Real.add_one_le_exp L
    linarith
  have hMN : (Real.exp L)/8 < (m:ℝ)*(n:ℝ) := by
    have h1 : U*(V/2)<U*(n:ℝ) := mul_lt_mul_of_pos_left hnLo hU
    have h2 : U*(n:ℝ)≤(m:ℝ)*(n:ℝ) :=
      mul_le_mul_of_nonneg_right hmLo hnPos
    have h3 : (Real.exp L)/8≤U*(V/2) := by nlinarith [hUV]
    linarith
  have huLow : Real.exp L/16 < (u:ℝ) := by
    linarith [hMN,huReal,hX8]
  have huHi : (u:ℝ)≤6*Cbox*Real.exp L := by
    have hMNhi : (m:ℝ)*(n:ℝ)≤(2*U)*(3*V) :=
      mul_le_mul hmHi.le hnHi.le (by positivity) (by positivity)
    have hBound : (u:ℝ)≤6*U*V := by nlinarith [huReal,hMNhi]
    nlinarith [hBound,hUVhi]
  have hEzReal : (e:ℝ)*(z:ℝ)=(mp:ℝ)*(u:ℝ) := by exact_mod_cast hEz
  have hPair : E*L^K0=U := by
    calc
      _ = U*(L^(-K0)*L^K0) := by rw [hE];ring
      _ = U := by rw [←Real.rpow_add hLp]; simp
  have hTriple : (E*L^(-88:ℝ))*L^(K0+88)=U := by
    calc
      _ = U*(L^(-K0)*L^(-88:ℝ)*L^(K0+88)) := by rw [hE];ring
      _ = U*(L^((-K0)+(-88:ℝ)+(K0+88))) := by
        rw [←Real.rpow_add hLp,←Real.rpow_add hLp]
      _ = U := by
        have hh : (-K0)+(-88:ℝ)+(K0+88)=0 := by ring
        rw [hh,Real.rpow_zero,mul_one]
  have hProdLo : U*(Real.exp L/16) ≤ (mp:ℝ)*(u:ℝ) :=
    mul_le_mul hmpLo huLow.le (by positivity) (by positivity)
  have hLowerMul : ((Real.exp L/32)*L^K0)*(e:ℝ)<(e:ℝ)*(z:ℝ) := by
    calc
      _ < ((Real.exp L/32)*L^K0)*(2*E) :=
        mul_lt_mul_of_pos_left heHi (by positivity)
      _ = U*(Real.exp L/16) := by rw [show ((Real.exp L/32)*L^K0)*(2*E)=
          (Real.exp L/16)*(E*L^K0) by ring,hPair];ring
      _ ≤ (mp:ℝ)*(u:ℝ) := hProdLo
      _ = (e:ℝ)*(z:ℝ) := hEzReal.symm
  have hLower : (Real.exp L/32)*L^K0 < (z:ℝ) := by
    exact lt_of_mul_lt_mul_right (by simpa only [mul_comm] using hLowerMul) hePos.le
  have hProdHi : (mp:ℝ)*(u:ℝ) ≤ (2*U)*(6*Cbox*Real.exp L) :=
    mul_le_mul hmpHi.le huHi (by positivity) (by positivity)
  have hUpperMul : (e:ℝ)*(z:ℝ) <
      (e:ℝ)*(24*Cbox*Real.exp L*L^(K0+88)) := by
    calc
      _ = (mp:ℝ)*(u:ℝ) := hEzReal
      _ ≤ (2*U)*(6*Cbox*Real.exp L) := hProdHi
      _ = (E*L^(-88:ℝ)/2)*(24*Cbox*Real.exp L*L^(K0+88)) := by
        rw [show (E*L^(-88:ℝ)/2)*(24*Cbox*Real.exp L*L^(K0+88))=
          12*Cbox*Real.exp L*((E*L^(-88:ℝ))*L^(K0+88)) by ring,hTriple]
        ring
      _ < (e:ℝ)*(24*Cbox*Real.exp L*L^(K0+88)) :=
        mul_lt_mul_of_pos_right heLo (by positivity)
  have hUpper : (z:ℝ)<24*Cbox*Real.exp L*L^(K0+88) := by
    exact lt_of_mul_lt_mul_left hUpperMul hePos.le
  exact ⟨hLower,hUpper⟩
end Green64Analytic.Parity

end

end

/-! ## ActualDyadicZWindowQuarter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 24500000

/-- TRUE CAP-FREE Parity(4.14) original B509 physical dyadic z scale:
   (exp L/16)L^K0 < Z < 24 Cbox exp L L^(K0+88),
all odd e including Pgroup factors, with ηeηn≠0 and Ybox=ceil6UV.
Derives from the newly verified correct source-box physical z
bound and exact binary dyad containment, no reuse of old Y0≤2exp L. -/
theorem parity_original_historical_ungated_full_box_smoothed_actual_Z_window_quarter434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 32≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K J : Finset ℕ) (e m : ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (hU : 0<U) (hV : 0<V) (hCbox : 0<Cbox)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (hm : m∈K) (hDyad : ∀mp∈K,
      U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ (Nat.ceil (6*U*V)) e m K J k Z)
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V (by linarith : 8≤L) e q.2≠0) :
    (Real.exp L/64)*L^K0 < (Z:ℝ) ∧
    (Z:ℝ) < 24*Cbox*Real.exp L*L^(K0+88) := by
  let z := parityOriginalHistoricalCanonicalZ434 e m q.1 q.2
  have hMem := Finset.mem_filter.mp hq
  have hProd := Finset.mem_product.mp hMem.1
  have hMp := Finset.mem_filter.mp hProd.1
  have hMpK : q.1∈K := (Finset.mem_erase.mp hMp.1).2
  have hNe : m≠q.1 := (Finset.mem_erase.mp hMp.1).1.symm
  have hValid := hMem.2.1
  have hzPos : 0<z := hMem.2.2.1
  have hzScale : parityOriginalHistoricalActualZDyadicScale434 z=Z := hMem.2.2.2
  have hDy := parity_original_historical_actual_z_in_own_dyad434 z hzPos
  rw [hzScale] at hDy
  have hmD := hDyad m hm
  have hmpD := hDyad q.1 hMpK
  obtain ⟨u,hu,up,hup,hDiv,hDivp,hvs,hvps⟩ := hValid
  have hmn : m*q.2=u+2 := (Finset.mem_filter.mp hu).2.2.2
  have hUeq : u=e*(u/e) := (Nat.mul_div_cancel_left' hDiv).symm
  have hZexact : z=q.1*(u/e) := by
    dsimp [z,parityOriginalHistoricalCanonicalZ434,
      parityOriginalHistoricalCanonicalV434]
    have huN : m*q.2-2=u := by omega
    rw [huN]
  have hEz : e*z=q.1*u := by
    calc
      _ = e*(q.1*(u/e)) := by rw [hZexact]
      _ = q.1*(e*(u/e)) := by ring
      _ = q.1*u := by rw [←hUeq]
  have hL8 : 8≤L := by linarith
  have hZ := parity_original_historical_ungated_source_box_smoothed_physical_z_scale_quarter434
    L U V E K0 Cbox e m q.1 q.2 u z hL hU hV hCbox hUV hUVhi hE hw
    hmD.1 hmD.2 hmpD.1 hmpD.2 hu hEz
  have hzReal : (z:ℝ) < 2*(Z:ℝ) := by exact_mod_cast hDy.2.2
  have hZlo : (Real.exp L/64)*L^K0 < (Z:ℝ) := by
    have hLp : 0<L^K0 := Real.rpow_pos_of_pos (by linarith : 0<L) _
    nlinarith [hZ.1,hzReal,hLp]
  have hZR : (Z:ℝ)≤(z:ℝ) := by exact_mod_cast hDy.2.1
  exact ⟨hZlo,hZR.trans_lt hZ.2⟩
end Green64Analytic.Parity

end

end

/-! ## ActualZUnionWindowQuarter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4200000

/-- The FULL original post-Cauchy B' physically nonzero original
smooth-weight Z UNION, not one e,m,k cell, satisfies the corrected
cap-free Parity(4.14) lower/upper dyadic window. All odd e (including
P-group prime factors) and all actual physical Q/P/B509 endpoints
are retained in the finite union; no bound on the number of z or
complex-character subsums is assumed. -/
theorem parity_original_full_odd_actual_nonzero_Z_union_box_window_quarter434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 32≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ)
    (hU : 0<U) (hV : 0<V) (hCbox : 0<Cbox)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (Z : ℕ)
    (hZ : Z∈parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V (by linarith : 8≤L) band slot δ (Nat.ceil (6*U*V)) K) :
    (Real.exp L/64)*L^K0 < (Z:ℝ) ∧
    (Z:ℝ) < 24*Cbox*Real.exp L*L^(K0+88) := by
  have hz0 := hZ
  unfold parityOriginalHistoricalFullOddOriginalZUnion434 at hz0
  obtain ⟨e,he,hrest⟩ := Finset.mem_biUnion.mp hz0
  obtain ⟨m,hm,hrest⟩ := Finset.mem_biUnion.mp hrest
  obtain ⟨k,hk,hcell⟩ := Finset.mem_biUnion.mp hrest
  have hOdd : Odd e := (Finset.mem_filter.mp he).2
  obtain ⟨q,hq,hw⟩ := (Finset.mem_filter.mp hcell).2
  exact parity_original_historical_ungated_full_box_smoothed_actual_Z_window_quarter434
    d L U V E K0 Cbox hL band slot δ K
    (parityOriginalHistoricalFullNEnvelope434 V) e m k Z
    hOdd hU hV hCbox hUV hUVhi hE hm hDyad q hq hw
end Green64Analytic.Parity

end

end

/-! ## SmoothNeighborZWindowQuarter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6800000

/-- Every smooth psi scale that can actually occur in the original
cap-free, all-odd, physical Parity B' source, INCLUDING the preceding
half-dyad, satisfies a genuine two-sided original post-Cauchy
height window. No hard ψ mask or false singleton canonical Z is used.
The lower constant changes 1/16 to 1/64, costing only a fixed factor
4; upper 24*Cbox is unchanged. -/
theorem parity_original_full_odd_true_smooth_neighbor_Z_box_window_quarter434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ)
    (hDyad : ∀mp∈K, U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (Z : ℕ)
    (hZ : Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K)) :
    (Real.exp L/256)*L^K0 < (Z:ℝ) ∧
    (Z:ℝ) < 24*Cbox*Real.exp L*L^(K0+88) := by
  classical
  have hLw : 8≤L := by linarith
  let Y := Nat.ceil (6*U*V)
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Y K
  have hExact := parity_original_full_odd_actual_Z_union_smooth_neighbor_exact434
    d L E V hLw band slot delta Y K
  dsimp only at hExact
  have hMem : Z∈ZG ∪ ZG.image (fun Z => Z/2) := by
    change Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG at hZ
    rw [hExact] at hZ
    exact hZ
  have hCanon (z0 : ℕ) (hz0 : z0∈ZG) :
      (Real.exp L/64)*L^K0 < (z0:ℝ) ∧
      (z0:ℝ) < 24*Cbox*Real.exp L*L^(K0+88) := by
    exact parity_original_full_odd_actual_nonzero_Z_union_box_window_quarter434
      d L U V E K0 Cbox (by linarith : 32≤L) band slot delta K hU hV
      (by linarith : 0<Cbox) hUV hUVhi hE hDyad z0 hz0
  have hPow : 0<Real.exp L*L^K0 := by positivity
  rcases Finset.mem_union.mp hMem with hBase | hHalf
  · have hW := hCanon Z hBase
    constructor
    · nlinarith [hW.1,hPow.le]
    · exact hW.2
  · obtain ⟨z0,hz0,hEq⟩ := Finset.mem_image.mp hHalf
    subst Z
    have hW := hCanon z0 hz0
    have hExp : (128:ℝ) ≤ Real.exp L := by
      have h := Real.add_one_le_exp L
      linarith
    have hPowOne : (1:ℝ)≤L^K0 := Real.one_le_rpow (by linarith) hK0
    have hTwo : (2:ℝ)≤(Real.exp L/64)*L^K0 := by
      have hDiv : (2:ℝ)≤Real.exp L/64 := by linarith
      have hLe := mul_le_mul_of_nonneg_left hPowOne (by positivity : 0≤Real.exp L/64)
      nlinarith
    have hZ0ge : 2≤z0 := by
      have hZ0R : (2:ℝ)≤(z0:ℝ) := (hTwo.trans_lt hW.1).le
      exact_mod_cast hZ0R
    have hDivBound : z0≤4*(z0/2) := by omega
    have hDivReal : (z0:ℝ)≤4*((z0/2:ℕ):ℝ) := by exact_mod_cast hDivBound
    constructor
    · nlinarith [hW.1,hDivReal]
    · have hDivLe : (z0/2:ℕ)≤z0 := by omega
      have hDR : ((z0/2:ℕ):ℝ)≤(z0:ℝ) := by exact_mod_cast hDivLe
      exact hDR.trans_lt hW.2
end Green64Analytic.Parity

end

end

/-! ## QuarterZPower -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- On the corrected true cap-free Parity physical window, every
canonical original binary Z is >=2, hence its preceding half Z/2
is another TRUE integer power of two, never a fictitious 0 or a
fractional Z. No smooth ψ contribution can require an unlegal Z. -/
theorem parity_original_full_odd_nonzero_Z_union_two_or_more_quarter434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (Z : ℕ)
    (hZ : Z∈parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K) :
    2≤Z := by
  have hZR := parity_original_full_odd_actual_nonzero_Z_union_box_window_quarter434
    d L U V E K0 Cbox (by linarith : 32≤L) band slot delta K
    hU hV (by linarith : 0<Cbox) hUV hUVhi hE hDyad Z hZ
  have hexp : (128:ℝ)≤Real.exp L := by
    have h := Real.add_one_le_exp L
    linarith
  have hbase : (1:ℝ)≤L^K0 := Real.one_le_rpow (by linarith : 1≤L) hK0
  have hTwo : (2:ℝ)≤(Real.exp L/64)*L^K0 := by
    have hh : (2:ℝ)≤Real.exp L/64 := by linarith
    nlinarith
  have hcast : (2:ℝ)≤(Z:ℝ) := (hTwo.trans_lt hZR.1).le
  exact_mod_cast hcast

/-- Physical source smooth ψ-neighbor Z scales are likewise genuine
positive powers of two. The preceding half case uses the source
canonical Z>=2, not an artificial sharp mask or unproved divisibility. -/
theorem parity_original_full_odd_smooth_neighbor_Z_is_binary_power_quarter434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (Z : ℕ)
    (hZ : Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K)) :
    ∃j : ℕ, Z=(2:ℕ)^j := by
  classical
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K
  have hExact := parity_original_full_odd_actual_Z_union_smooth_neighbor_exact434
    d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K
  change Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG at hZ
  rw [hExact] at hZ
  rcases Finset.mem_union.mp hZ with hBase | hHalf
  · exact parity_original_full_odd_nonzero_Z_union_is_binary_power434
      d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K Z hBase
  · obtain ⟨z0,hz0,hEq⟩ := Finset.mem_image.mp hHalf
    obtain ⟨j,hPow⟩ := parity_original_full_odd_nonzero_Z_union_is_binary_power434
      d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K z0 hz0
    have h2 : 2≤z0 := parity_original_full_odd_nonzero_Z_union_two_or_more_quarter434
      d L U V E K0 Cbox hL hK0 hCbox hU hV hUV hUVhi hE
      band slot delta K hDyad z0 hz0
    have hj : 1≤j := by
      by_contra hh
      have j0 : j=0 := by omega
      simp [hPow,j0] at h2
    refine ⟨j-1,?_⟩
    rw [←hEq,hPow]
    have hSucc : (j-1)+1=j := by omega
    have hDivPow : (2:ℕ)^j/2=(2:ℕ)^(j-1) := by
      conv_lhs => rw [←hSucc,pow_succ]
      omega
    exact hDivPow
end Green64Analytic.Parity

end

end

/-! ## QuarterZRangeImage -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Real source smooth ψ-neighbor Z is a power of 2^j with a REAL
bounded exponent j≤the *explicit* source dyadic capacity N(L).
The original Z carries its true physical cap-free B509 source
support, so this uses neither an arbitrary Fourier truncation nor
a sharp dyadic substitute for smooth ψ. -/
theorem parity_original_full_odd_true_smooth_neighbor_Z_index_capacity_quarter434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (Z : ℕ)
    (hZ : Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K)) :
    ∃j : ℕ, j≤parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox ∧
      Z=(2:ℕ)^j := by
  obtain ⟨j,hPow⟩ := parity_original_full_odd_smooth_neighbor_Z_is_binary_power_quarter434
    d L U V E K0 Cbox hL hK0 hCbox hU hV hUV hUVhi hE
    band slot delta K hDyad Z hZ
  have hBox := parity_original_full_odd_true_smooth_neighbor_Z_box_window_quarter434
    d L U V E K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta K hDyad Z hZ
  let Y : ℕ := Nat.ceil (48*Cbox*Real.exp L*L^(K0+88))
  have hCeil : 48*Cbox*Real.exp L*L^(K0+88)≤(Y:ℝ) := Nat.le_ceil _
  have hZsmall : (Z:ℝ)≤(Y:ℝ) := by
    have hCapPos : 0≤Cbox*Real.exp L*L^(K0+88) := by positivity
    linarith [hBox.2,hCeil,hCapPos]
  have hNat : Z≤Y := by exact_mod_cast hZsmall
  have hLog : Nat.log 2 Z ≤ Nat.log 2 Y := Nat.log_mono_right hNat
  have hjLog : Nat.log 2 Z=j := by
    rw [hPow,Nat.log_pow (by norm_num : 1<2)]
  have hjCap : j≤parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox := by
    rw [hjLog] at hLog
    exact hLog
  exact ⟨j,hjCap,hPow⟩

/-- The REAL original smooth ψ source family, including both
original binary and preceding half-dyads, is exactly the image of
its already kernel-checked full dyadic range filter at the explicit
source capacity N(L); no unsupported j or Z and no missing
neighboring contribution to the physical B' Fourier outer. -/
theorem parity_original_full_odd_true_smooth_Z_image_exact_quarter434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 128≤L)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤4*U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K
    let S := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
    ((Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈S)).image
      (fun j => (2:ℕ)^j) = S := by
  dsimp only
  apply parity_original_finite_smooth_Z_power_image_exact434
  intro Z hZ
  exact parity_original_full_odd_true_smooth_neighbor_Z_index_capacity_quarter434
    d L U V E K0 Cbox hL hK0 hCbox hU hV hUV hUVhi hE
    band slot delta K hDyad Z hZ
end Green64Analytic.Parity

end

end

/-! ## QuarterZeroEtaAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Actual zero-η TWO ghost errors on the full original Parity (4.10)
physical C∞ ψ, all-odd e, signed k and both dyadic neighbors, are
unconditionally paid by a uniform O_D(exp(L)L^-D) original diagonal
bound. The single H=1 Fourier T and every source constant are chosen
before L. No invented hard eta/psi masks or χ-subsummand monotonicity.
This closes only the zero-η Fourier error, not TypeII(4.2). -/
theorem parity_eventually_original_true_psi_zero_eta_two_ghost_any_log_quarter434
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
      2*FullMass ≤ 16*C1*Acoef^2*Real.exp L*L^(-Dgoal) := by
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
  let d := sourceOriginalLiteralDepth 20 L
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    (sourceOriginalLiteralDepth 20 L) L E V hLw band slot delta Y K
  let ZS := parityOriginalActualSmoothPsiNeighborZEnvelope434
    (parityOriginalHistoricalFullOddOriginalZUnion434
      (sourceOriginalLiteralDepth 20 L) L E V hLw band slot delta Y K)
  let D0 := parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
    (sourceOriginalLiteralDepth 20 L) L band slot delta freq rho K EF J alpha signed Y
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
  let N := Nat.ceil (L^(K0+89))
  have hKShort : ∀k∈KS,k≠0 ∧ k.natAbs≤N := by
    intro k hk
    have hh := parity_original_full_odd_smoothed_k_genuine_polylog434
      d L U E V K0 hLw hU hE band slot delta Y K hDyad k hk
    exact ⟨hh.1,hh.2.2⟩
  have hZRange : ∀Z∈ZS,
      (0<Z) ∧ (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88) := by
    intro Z hz
    have hh := parity_original_full_odd_true_smooth_neighbor_Z_box_window_quarter434
      d L U V E K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
      band slot delta K hDyad Z hz
    have hp : (0:ℝ)<(Real.exp L/256)*L^K0 := by positivity
    have hpz : (0:ℝ)<(Z:ℝ) := hp.trans hh.1
    exact ⟨by exact_mod_cast hpz,hh.2.le⟩
  have hZPow : ∀Z∈ZS,∃j : ℕ,Z=(2:ℕ)^j := by
    intro Z hz
    exact parity_original_full_odd_smooth_neighbor_Z_is_binary_power_quarter434
      d L U V E K0 Cbox hL hK0 hCbox hU hV hUV hUVhi hE
      band slot delta K hDyad Z hz
  have hClosed : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U := by
    intro mp hm
    exact ⟨(hDyad mp hm).1,(hDyad mp hm).2.le⟩
  have hMass := parity_original_true_psi_full_global_ghost_mass_le_diagonal_quarter434
    d L U E V K0 Cbox A R hLw hK0 hU hV hUV hE (by linarith : 0≤Cbox) hLargeC
    band slot delta freq rho K alpha signed Y KS ZS N
    hKShort (fun Z hz => (hZRange Z hz).1)
    (fun Z hz => (hZRange Z hz).2) hZPow hClosed
    buf hA hSmooth hSupport hOne4 1
    (by simpa only [J1] using hBE)
    (by simpa only [J1] using hBN) hR hCube T hT
  dsimp only at hMass ⊢
  rw [←hX] at hMass
  have hBoundDiag : D0≤Acoef^2*Real.exp L*L^M := by
    simpa only [D0,M,EF,J,Y] using hD0
  have hMassBound : FullMass ≤
      (C1*L^X/T)*(2*(((2*N+1:ℕ):ℝ)*D0)) := by
    simpa only [pow_one,mul_assoc,FullMass,D0,C1,X,T,EF,J,d,Y,KS,ZS] using hMass
  have hFinal := parity_original_true_psi_two_ghost_power_absorption434
    L K0 X M Dgoal C1 Acoef FullMass D0 hLw hK0 hC1
    (by simpa only [T] using hMassBound) hBoundDiag
  exact hFinal
end Green64Analytic.Parity

end

end

