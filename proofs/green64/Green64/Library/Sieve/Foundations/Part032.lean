module

public import Green64.Library.Sieve.Foundations.Part031
public import Green64.Library.Sieve.Foundations.Part026
public import Green64.Library.Sieve.Foundations.Part030
public import Green64.Library.Sieve.Foundations.Part028
public import Green64.Library.Sieve.Foundations.Part019
public import Green64.Library.Sieve.Foundations.Part029
public import Green64.Library.Sieve.Foundations.Part018
public import Green64.Library.Sieve.Foundations.Part017
public import Green64.Library.Sieve.Foundations.Part024
public import Green64.Library.Sieve.Foundations.Part007
public import Green64.Library.Sieve.Foundations.Part013
public import Green64.Library.Analysis.Estimates.Part015

@[expose] public section

/-!
# Sieve / Foundations / Part032

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalLowfreqBox3DFiniteSeminorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- Source-correct original cap-free B'(4.7) full 3D Schwartz
FINITE seminorm B_H source budget for arbitrary H on
true Ybox physical Z≤24Cbox expL L^(K0+88), with exactly
original exponent 5(K0+90)(H+P+1) and fixed reference K_J.
Proof invokes rederived true source seminorm, not old cap Y0. -/
theorem parity_original_historical_box_3d_finite_seminorm_budget434
    (L U E V Z K0 Cbox A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J N : ℕ) (hNJ : N≤J)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
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
  have h0 (j : ℕ) (hj : j≤J) :
      (SchwartzMap.seminorm ℂ 0 j) f ≤ K j * Rpow := by
    have hLE := parity_original_eta_e_threshold_mono434
      A hA.le J j hj L hLargeE
    have hLN := parity_original_eta_n_threshold_mono434
      A hA.le J j hj L hLargeN
    have hs := parity_original_historical_box_full_3d_source_seminorm434
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
    have hLN := parity_original_eta_n_threshold_mono434
      A hA.le J j hj L hLargeN
    have hs := parity_original_historical_box_full_3d_source_seminorm434
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

/-! ## OriginalHistoricalLowfreqBox3DFourierMoment -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- The ORIGINAL source cap-free Parity(4.14) three-dimensional
Schwartz H-moment is uniformly ≤ C_H L^[5(K0+90)(H+P+1)]
for ALL true Z≤24Cbox expL L^(K0+88), Cbox fixed,
L≥6Cbox; C_H fixed before L,k,Z,e,χ and target Fourier
precision. All five source factors and true h=-2 term kept.
This repairs previously artificial Y0 Fourier moment theorem
without logarithmic exponent inflation. -/
theorem parity_original_historical_box_source_BH_uniform_polylog434
    (L U E V Z K0 Cbox A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 →
      -Real.log A ≤ s ∧ s ≤ Real.log A)
    (H : ℕ)
    (hLargeE : 2*A*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L)
    (hLargeN : 8*A^2*((H + (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
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
  have hm0 := parity_original_historical_box_3d_finite_seminorm_budget434
    L U E V Z K0 Cbox A hL hK0 k hk hU hV hUV hE hZ
    hCbox hLargeC hZupper hA
    buf hBufSmooth hBufSupport J 0 (Nat.zero_le J)
    hLargeE hLargeN R hR hCubeR
  have hmJ := parity_original_historical_box_3d_finite_seminorm_budget434
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

/-! ## OriginalHistoricalLowfreqBoxKZTailUniform -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 28000000

/-- Corrected cap-free original PARITY(4.16) physical k/Z/χ
FOURIER tail error ≤ actual SOURCE coefficient mass times the
FULL NEW source H-moment C_H L^[5(K0+90)(H+P+1)]/T^H,
for Ybox=ceil(6UV), UV∈[expL,Cbox expL], all odd e and the
true B509 H0 nonzero ηeηn physical source. Neither the old Y0
z bound nor any signed Parity4.17 cancellation is assumed. -/
theorem parity_eventually_original_ungated_full_box_k_z_416_tail_actual_mass_uniform434
    (K0 Cbox : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
      6*Cbox≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho U V E : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool),
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
      E=U*L^(-K0) →
      (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) →
      ∀ (e m : ℕ) (k : ℤ) (Z : ℕ) (he : Odd e),
      e∈parityOriginalHistoricalFullOddEEnvelope434 E → m∈K →
      ∀ (q : ℕ×ℕ),
      q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        (Nat.ceil (6*U*V)) e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k Z →
      parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2≠0 →
      ∀ (χ : DirichletCharacter ℂ (2*k.natAbs))
        (A R : ℝ) (hA : 0<A) (hR : 1≤R)
        (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀t : ℝ,buf t≠0 →
          -Real.log A≤t ∧ t≤Real.log A),
      (∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) →
      (∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) →
      ∀ (H : ℕ),
      2*A*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L →
      (8*A^2*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
        (2:ℝ)^(H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
        ((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L) →
      ∀ (T : ℝ),0<T →
      parityOriginalHistoricalUngatedActualKZ416FourierError434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw Z k band slot δ ξ
        rho α signed (Nat.ceil (6*U*V)) e m K
        (parityOriginalHistoricalFullNEnvelope434 V) χ
        buf (-Real.log A) (Real.log A) hSmooth hSupport T ≤
      parityOriginal3DPhysicalFiniteCoefficientMass434
        (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
          (sourceOriginalLiteralDepth 20 L) L band slot δ
          (Nat.ceil (6*U*V)) e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k Z)
        (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho α
          signed (Nat.ceil (6*U*V)) e m k χ) *
        (parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport H *
          L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H) := by
  filter_upwards [eventually_ge_atTop (max ((3:ℝ)^256)
    (max (8:ℝ) (6*Cbox)))] with L hLarge
  have hL : 8≤L := (le_max_left _ _).trans ((le_max_right _ _).trans hLarge)
  have hL3 : (3:ℝ)^256≤L := (le_max_left _ _).trans hLarge
  have hLargeC : 6*Cbox≤L := (le_max_right _ _).trans ((le_max_right _ _).trans hLarge)
  refine ⟨hL3,hL,hLargeC,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed hU hV hUV hUVhi hScale hDyad
    e m k Z he heMem hm q hq hw χ A R hA hR buf hSmooth hSupport
    hOne hCube H hLargeE hLargeN T hT
  let d := sourceOriginalLiteralDepth 20 L
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := (Nat.ceil (6*U*V))
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let mass := parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ)
  let C : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport H
  let Power : ℝ := L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))
  have hLp : 0<L := by linarith
  have hEpos : 0<E := by
    rw [hScale]
    exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  have hmDyad := hDyad m hm
  have hCpos : 0<Cbox := by linarith
  have hZrange := parity_original_historical_ungated_full_box_smoothed_actual_Z_window434
    d L U V E K0 Cbox hLw band slot δ K J e m k Z he hU hV hCpos
    hUV hUVhi hScale hm hDyad q hq hw
  have hLsq : 24*Cbox≤L^2 := by
    have hh : 24*Cbox≤4*L := by linarith
    have hh2 : 4*L≤L^2 := by nlinarith [hL]
    linarith
  have hZlegal := parity_original_historical_box_physical_Z_417_numeric434
    L K0 Cbox (Z:ℝ) hLw hK0 (by linarith : 0≤Cbox) hLsq hZrange.1 hZrange.2
  have hZreal : (0:ℝ)<(Z:ℝ) :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-(K0+90)))).trans_le hZlegal.1
  have hZ : 0<Z := by exact_mod_cast hZreal
  have hQ := Finset.mem_filter.mp hq
  have hQprod := Finset.mem_product.mp hQ.1
  have hMP := Finset.mem_filter.mp hQprod.1
  have hNe : m≠q.1 := (Finset.mem_erase.mp hMP.1).1.symm
  have hReal := parity_original_historical_ungated_physical_valid_k_z434
    d L band slot δ Y e m q.1 q.2 he hNe hQ.2.1
  dsimp only at hReal
  have hK : parityOriginalHistoricalOffdiagK434 e m q.1=k := hMP.2
  have hk : k≠0 := by
    rw [←hK]
    exact hReal.1
  have hBH := parity_original_historical_box_source_BH_uniform_polylog434
    L U E V (Z:ℝ) K0 Cbox A hLw hK0 k hk hU hV hUV hScale
    (by exact_mod_cast (Nat.zero_le Z)) (by linarith : 0≤Cbox) hLargeC hZrange.2.le
    hA buf hSmooth hSupport H hLargeE hLargeN R hR hCube
  have hTbound : parityOriginalHistoricalUngatedActualKZ416FourierError434
    d L U E V hLw Z k band slot δ ξ rho α signed Y e m K J χ
    buf (-Real.log A) (Real.log A) hSmooth hSupport T ≤
    mass*(parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) :=
    parity_original_historical_ungated_actual_k_z_416_error_le_mass434
      d L hLw band slot δ ξ rho α signed Y e m K J k Z χ he
      U E V hU hEpos hV hmDyad.1 hmDyad.2.le
      (by intro mp hmp; exact ⟨(hDyad mp hmp).1,(hDyad mp hmp).2.le⟩)
      buf (-Real.log A) (Real.log A) hSmooth hSupport hOne hZ H T hT
  have hDiv : parityOriginal3DSourceMomentFiniteBudget434 H f/T^H ≤
      C*Power/T^H :=
    div_le_div_of_nonneg_right hBH (pow_pos hT H).le
  have hM : 0 ≤ mass := parity_original_3d_physical_finite_coefficient_mass_nonneg434 _ _
  exact hTbound.trans (mul_le_mul_of_nonneg_left hDiv hM)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqBoxTailToMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 29000000

/-- Reproved FULL original true B509 UNGATED h=-2 Cauchy source
high-frequency 3D Fourier tail summed over every full-odd e,
all m, nonzero signed k, χ, and physically nonzero ηeηn Z,
at corrected CAP-FREE Ybox=ceil(6UV), UV≤Cbox expL fixed.
A global common source H moment C_H L^X/T^H factors out of
the actual original physical χ-weighted coefficient ℓ1 mass.
No old Y0 upper bound, no unrestricted Parity417 signed saving. -/
theorem parity_eventually_original_ungated_full_box_filtered_tail_le_coefficient_mass434
    (K0 Cbox : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧ 6*Cbox≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho U V E : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool),
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
      E=U*L^(-K0) →
      (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) →
      ∀ (A R : ℝ) (hA : 0<A) (hR : 1≤R)
        (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀t : ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A),
      (∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) →
      (∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) →
      ∀ (H : ℕ),
      2*A*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L →
      (8*A^2*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
        (2:ℝ)^(H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
        ((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L) →
      ∀ (T : ℝ),0<T →
      let Q : ℝ :=
        parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport H *
        L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H
      parityOriginalHistoricalUngatedFullOddFilteredB633TailMass434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed (Nat.ceil (6*U*V))
        buf (-Real.log A) (Real.log A) hSmooth hSupport T ≤
      Q * parityOriginalHistoricalUngatedFullOddFilteredCoefficientMass434
        (sourceOriginalLiteralDepth 20 L) L E V hLw band slot δ ξ rho
        α signed (Nat.ceil (6*U*V)) K := by
  filter_upwards [parity_eventually_original_ungated_full_box_k_z_416_tail_actual_mass_uniform434
    K0 Cbox hK0 hCbox] with L hSource
  refine ⟨hSource.1,hSource.2.1,hSource.2.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed hU hV hUV hUVhi hScale hDyad
    A R hA hR buf hSmooth hSupport hOne hCube H hLargeE hLargeN T hT
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := (Nat.ceil (6*U*V))
  let C : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport H
  let Q : ℝ := C *
    L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H
  let S : ℕ → ℕ → ℤ → Finset ℕ := fun e m k =>
    parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
      d L E V hLw band slot δ Y e m K J k
  let Mass (e m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ (2*k.natAbs))
      (Z : ℕ) : ℝ :=
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ)
  let Err (e m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ (2*k.natAbs))
      (Z : ℕ) : ℝ :=
    parityOriginalHistoricalUngatedActualKZ416FourierError434
      d L U E V hLw Z k band slot δ ξ rho α signed Y e m K J χ
      buf (-Real.log A) (Real.log A) hSmooth hSupport T
  have hC : 0≤C := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
    A R buf hSmooth hSupport H hR
  have hLp : 0<L := by linarith [hSource.2.1]
  have hQ : 0≤Q := by
    dsimp [Q]
    positivity
  have hCell (e m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ (2*k.natAbs))
      (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E)
      (hm : m∈K) (Z : ℕ) (hZ : Z∈S e m k) :
      Err e m k χ Z ≤ Mass e m k χ Z * Q := by
    have heOdd : Odd e := (Finset.mem_filter.mp he).2
    obtain ⟨q,hq,hw⟩ := (Finset.mem_filter.mp hZ).2
    have hStep := hSource.2.2.2 hLw band slot δ ξ rho U V E K α signed
      hU hV hUV hUVhi hScale hDyad e m k Z heOdd he hm q hq hw χ
      A R hA hR buf hSmooth hSupport hOne hCube H hLargeE hLargeN T hT
    exact hStep
  have hZ (e m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ (2*k.natAbs))
      (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E) (hm : m∈K) :
      (∑Z∈S e m k, Err e m k χ Z) ≤
        Q*(∑Z∈S e m k,Mass e m k χ Z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Z hz
    have hh := hCell e m k χ he hm Z hz
    simpa only [mul_comm] using hh
  have hχ (e m : ℕ) (k : ℤ)
      (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E) (hm : m∈K) :
      (∑χ : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (∑Z∈S e m k,Err e m k χ Z)) ≤
      Q*(∑χ : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (∑Z∈S e m k,Mass e m k χ Z)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ hχ
    have hh := mul_le_mul_of_nonneg_left
      (hZ e m k χ he hm)
      (norm_nonneg (parityShiftTwoMaskCoefficient434 k.natAbs χ))
    calc
      _ ≤ ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (Q*(∑Z∈S e m k,Mass e m k χ Z)) := hh
      _ = Q*(‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (∑Z∈S e m k,Mass e m k χ Z)) := by ring
  unfold parityOriginalHistoricalUngatedFullOddFilteredB633TailMass434
    parityOriginalHistoricalUngatedFullOddFilteredCoefficientMass434
  change (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
      ∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (∑Z∈S e m k,Err e m k χ Z)) ≤
      Q*(∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
        ∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
          ∑χ : DirichletCharacter ℂ (2*k.natAbs),
            ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
            (∑Z∈S e m k,Mass e m k χ Z))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact hχ e m k he hm
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSmoothReverseBox -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 27000000

/-- The REAL remaining source-boundary obligation in Parity(4.17)
can be discharged for a true B633 unrestricted two-prime-slot
pair, after FIRST choosing the geometrically CORRECT u cap
Ybox=ceil(6UV), provided its recovered shared n carries the
actual nonzero η_e(e/E)η_n(n/V) smoothing weight.

Original B633 nonzero ⇒ BOTH H0 reserved B509 slots (PROVED),
reverse ordinary-P divisors and shifted k recover ONE common n,
η_n≠0 ⇒ n∈Nfull, and full m,m'∈[U,2U) with η_n support
implies BOTH e*v and e*v'≤Ybox automatically. Hence the
unrestricted pair then belongs to the EXACT true ungated B509
physical k/Z source. All e including P-prime factors allowed.

The property hEta is only a SOURCE weight-nonzero hypothesis,
NOT a new analytic estimate or cancellation assumption. The
theorem is conditional on the corrected Ybox SOURCE model;
the prior Y0=floor(2exp L) selected input still requires a
separate SOURCE comparison. -/
theorem parity_original_historical_lowfreq_nonzero_B633_smooth_pair_in_full_box434
    (d : ℕ) (L E U V rho xi1 xi2 xi3 : ℝ)
    (hL : 8≤L) (hE : 0<E) (hU : 0<U) (hV : 0<V)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (k : ℤ) (chi : DirichletCharacter ℂ (2*k.natAbs))
    (signed : Bool) (e m mp z zp : ℕ)
    (he : Odd e) (hm : 0 < m) (hmp : 0 < mp)
    (hz : 0 < z) (hzp : 0 < zp)
    (hmDyad : (m:ℝ)≤2*U) (hmpDyad : (mp:ℝ)≤2*U)
    (hmpMem : mp ∈ K) (hNe : m ≠ mp)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hShift : (z:ℤ)+2*k=(zp:ℤ))
    (hCop : m.Coprime k.natAbs)
    (hDivMp : mp∣sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z)
    (hDivM : m∣sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp)
    (hNonzero :
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).residual
        (2*k.natAbs) chi
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).lo
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).hi
        m mp z zp ≠ 0)
    (hEta : ∀n : ℕ,
      m*n=e*(z/mp)+2 → mp*n=e*(zp/m)+2 →
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n≠0) :
    ∃n : ℕ,
      n∈parityOriginalHistoricalFullNEnvelope434 V ∧
      (mp,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ (Nat.ceil (6*U*V)) e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k
        (parityOriginalHistoricalActualZDyadicScale434 z) ∧
      parityOriginalHistoricalCanonicalZ434 e m mp n=z := by
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  obtain ⟨v,vp,n,hv,hvp,hZ,hZp,hMN,hMpN⟩ :=
    parity_original_historical_reverse_417_divisor_pair_to_source_n434
      P m mp e z zp k hm hmp hz hzp hDet hShift hCop hDivMp hDivM
  have hVQuot : z/mp=v := by
    rw [hZ]
    exact Nat.mul_div_cancel_left v hmp
  have hVPQuot : zp/m=vp := by
    rw [hZp]
    exact Nat.mul_div_cancel_left vp hm
  have hEtaActual : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n≠0 := by
    apply hEta n
    · rw [hVQuot]; exact hMN
    · rw [hVPQuot]; exact hMpN
  have hNRange := (parity_original_historical_full_odd_nonzero_smooth_e_n_ranges434
    L E V hL hE hV e n hEtaActual).2.2
  have hnHi : (n:ℝ)≤3*V := hNRange.2.le
  have hJ : n∈parityOriginalHistoricalFullNEnvelope434 V :=
    parity_original_historical_ungated_nonzero_eta_n_in_full_envelope434
      L E V hL hE hV e n hEtaActual
  have hCaps := parity_original_historical_ungated_box_both_natural_u_caps434
    U V hU.le hV.le m mp n e v vp hmDyad hmpDyad hnHi hMN hMpN
  have hSlots := parity_original_historical_B633_pair_nonzero_requires_both_H0_slots434
    d L band slot δ ξ K alpha (2*k.natAbs) chi
    rho xi1 xi2 xi3 signed m mp z zp
    (by rw [hVQuot]; exact hv) (by rw [hVPQuot]; exact hvp) hNonzero
  have hVS : sourceOriginalOrdinaryPart P v ∈
      parityOriginalReservedCartesianVStarSupport434 d L band slot δ := by
    rw [←hVQuot]
    exact hSlots.1
  have hVPS : sourceOriginalOrdinaryPart P vp ∈
      parityOriginalReservedCartesianVStarSupport434 d L band slot δ := by
    rw [←hVPQuot]
    exact hSlots.2
  have hPosN : 0 < n := by
    have hh : 0 < m*n := by rw [hMN]; omega
    exact Nat.pos_of_mul_pos_left hh
  have hSource : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ (Nat.ceil (6*U*V)) e m mp n :=
    (parity_original_historical_ungated_full_box_physical_iff_no_u_cap434
      d L U V hU.le hV.le band slot δ e m mp n he.pos
      hmDyad hmpDyad hnHi).mpr
      ⟨v,vp,hm,hmp,hPosN,hv,hvp,hMN,hMpN,hVS,hVPS⟩
  have hK : parityOriginalHistoricalOffdiagK434 e m mp=k :=
    parity_original_historical_physical_k_eq_quotient434 e m mp he.pos k hDet
  have hMPK : mp∈parityOriginalHistoricalKPrimeFibre434 e m K k := by
    unfold parityOriginalHistoricalKPrimeFibre434
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hNe.symm,hmpMem⟩,hK⟩
  have hZCan : parityOriginalHistoricalCanonicalZ434 e m mp n=z := by
    have hh : m*n-2=e*v := by omega
    unfold parityOriginalHistoricalCanonicalZ434
      parityOriginalHistoricalCanonicalV434
    rw [hh,Nat.mul_div_cancel_left v he.pos]
    exact hZ.symm
  have hEvent : (mp,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ (Nat.ceil (6*U*V)) e m K
      (parityOriginalHistoricalFullNEnvelope434 V) k
      (parityOriginalHistoricalActualZDyadicScale434 z) := by
    unfold parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hMPK,hJ⟩,
       ⟨hSource,by rw [hZCan]; exact hz,by rw [hZCan]⟩⟩
  exact ⟨n,hJ,hEvent,hZCan⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqBoxShiftedMoment -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- FIXING the SOURCE u-capping mismatch: Parity(4.10) requires the
complete physical box u≤ ceil(6UV) for original cofactor K⊂[U,2U),
nonzero ηn on [V/2,3V]. If UV≤C·exp L for ANY fixed C≥1, the
same ORIGINAL shifted tau(u)^3 tau(u+2) moment exponent 256
remains unconditionally valid over this LARGER true source box.

  Σ_{0<u≤ ceil(6UV)} τ(u)^3τ(u+2) ≤ exp(L) L^256.

Proof: native uniform shifted-divisor moment ≤(Y+2)(1+log(Y+2))^255;
Y+2≤(6C+3)exp L, log(Y+2)≤log(6C+3)+L,
and the extra FIXED factor (6C+3)*2^255 is absorbed by one
more power of L eventually. The large-L threshold depends on C,
not the target Fourier precision, the physical cells or K0.

No change to signs, actual B509 residual, fine alpha, or n/u
finite SOURCE support; only a positive divisor moment is bounded.
This theorem is the mathematical prerequisite to using a SOURCE-
correct cap in the ungated positive Cauchy diagonal. -/
theorem parity_eventually_original_historical_box_shift_two_tau_cube_moment434
    (C : ℝ) (hC : 1≤C) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0≤U → 0≤V → U*V≤C*Real.exp L →
      (∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
        (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) ≤
      Real.exp L*L^256 := by
  let B : ℝ := 6*C+3
  have hB : 0<B := by dsimp [B]; linarith
  let threshold : ℝ := B*((2:ℝ)^255)+B+2
  filter_upwards [eventually_ge_atTop threshold] with L hLarge
  have hL : 1≤L := by dsimp [threshold,B] at hLarge; nlinarith [pow_pos (by norm_num : (0:ℝ)<2) 255]
  refine ⟨hL,?_⟩
  intro U V hU hV hUV
  let Y : ℕ := Nat.ceil (6*U*V)
  have hExp : 0<Real.exp L := Real.exp_pos _
  have hExpOne : (1:ℝ)≤Real.exp L := by
    have hh := Real.add_one_le_exp L
    linarith
  have hY : ((Y+2:ℕ):ℝ)≤B*Real.exp L := by
    have hNonneg : 0≤6*U*V := by positivity
    have hCeil : (Y:ℝ)<6*U*V+1 := Nat.ceil_lt_add_one hNonneg
    dsimp [B]
    push_cast
    nlinarith [hCeil,hUV,hExpOne]
  have hYPos : (0:ℝ)<((Y+2:ℕ):ℝ) := by exact_mod_cast (show 0<Y+2 by omega)
  have hYOne : (1:ℝ)≤((Y+2:ℕ):ℝ) := by exact_mod_cast (show 1≤Y+2 by omega)
  have hLog : Real.log ((Y+2:ℕ):ℝ)≤Real.log B+L := by
    have hh := Real.log_le_log hYPos hY
    rw [Real.log_mul hB.ne' (Real.exp_ne_zero L),Real.log_exp] at hh
    exact hh
  have hLogB : Real.log B≤B-1 := Real.log_le_sub_one_of_pos hB
  have hLBound : B≤L := by
    dsimp [threshold] at hLarge
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) 255]
  have hLogBound : 1+Real.log ((Y+2:ℕ):ℝ)≤2*L := by linarith
  have hBase : 0≤1+Real.log ((Y+2:ℕ):ℝ) := by
    have hh := Real.log_nonneg hYOne
    linarith
  have hCFull : B*((2:ℝ)^255)≤L := by
    dsimp [threshold] at hLarge
    linarith [hB]
  have hMoment := parity_original_shift_two_tau_cube_times_shift_tau_moment434 Y
  change (∑u∈Finset.Ioc 0 Y,
      (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) ≤
      Real.exp L*L^256
  calc
    _ ≤ ((Y+2:ℕ):ℝ)*(1+Real.log ((Y+2:ℕ):ℝ))^255 := hMoment
    _ ≤ (B*Real.exp L)*(2*L)^255 :=
      mul_le_mul hY (pow_le_pow_left₀ hBase hLogBound 255)
        (pow_nonneg (by positivity) _) (by positivity)
    _ = (B*(2:ℝ)^255)*(Real.exp L*L^255) := by rw [mul_pow]; ring
    _ ≤ L*(Real.exp L*L^255) :=
      mul_le_mul_of_nonneg_right hCFull (mul_nonneg hExp.le (pow_nonneg (by linarith : (0:ℝ)≤L) 255))
    _ = Real.exp L*L^256 := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqBoxDiagonal -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 27000000

/-- Genuine Parity(4.10)--(4.11) original UNGATED B509/Cauchy
unweighted diagonal, enlarged to the mathematically COMPLETE
u≤Ybox=ceil(6UV) source after selected-Q e positive-square
extension. Original H0 reserved prime, W1, signed ε and α are
unchanged; no old artificial u≤floor(2exp L) restriction.

For ANY fixed Cbox≥1, for UV≤Cbox exp(L), the diagonal still has
the ORIGINAL unconditional exponent

  D_full_ungated(Ybox) ≤ Acoef² exp(L) L^(2*C_W1+256).

This follows from the newly proved SOURCE-correct extended shifted
τ(u)^3τ(u+2) moment at Ybox and genuine original all-e intrinsic
H0 pointwise norm. The threshold may depend on fixed Cbox, not
on U,V, the true e/m/n source, or the desired Fourier precision.
The signed low-frequency Parity4.17 saving remains OPEN. -/
theorem parity_eventually_original_historical_ungated_box_diagonal_polylog434
    (Cbox : ℝ) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0≤U → 0≤V → U*V≤Cbox*Real.exp L →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K Eenv Nenv α signed (Nat.ceil (6*U*V)) ≤
        Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+256) := by
  filter_upwards [parity_eventually_original_historical_ungated_fixed_e_u_norm_le_tau434,
    parity_eventually_original_historical_box_shift_two_tau_cube_moment434 Cbox hCbox]
    with L hPhys hMoment
  refine ⟨hMoment.1,?_⟩
  intro U V hU hV hUV band slot δ ξ rho K Eenv Nenv α signed Acoef hAcoef hα
  let Y := Nat.ceil (6*U*V)
  let C : ℝ := L^parityOriginalW1PolylogExponent434
  have hLp : 0<L := by linarith [hMoment.1]
  have hC : 0≤C := Real.rpow_nonneg hLp.le _
  have hFixed (e u : ℕ) (hu : 0<u) (he : 0<e) :
      ‖parityOriginalHistoricalUngatedFixedEU434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho signed e u‖ ≤
        C*(u.divisors.card:ℝ) := by
    simpa only [parityOriginalHistoricalUngatedFixedEU434,C] using
      (hPhys.2 band slot δ ξ rho signed e u he hu)
  have hFinite := parity_original_historical_ungated_extended_diagonal_finite_tau_moment434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
    K Eenv Nenv α signed Y
    Acoef C hAcoef hC hα hFixed
  have hMomentBox := hMoment.2 U V hU hV hUV
  change parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
      (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
      K Eenv Nenv α signed Y ≤
    Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+256)
  calc
    _ ≤ Acoef^2*C^2*(∑u∈Finset.Ioc 0 Y,
      (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) := hFinite
    _ ≤ Acoef^2*C^2*(Real.exp L*L^256) :=
      mul_le_mul_of_nonneg_left hMomentBox (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+256) := by
      have hPower : C^2*L^256 = L^(2*parityOriginalW1PolylogExponent434+256) := by
        dsimp [C]
        simp only [pow_two,←Real.rpow_add hLp]
        rw [←Real.rpow_natCast L 256]
        rw [←Real.rpow_add hLp]
        congr 1
        ring
      rw [←hPower]
      ring

/-- The TRUE corrected original full all-odd-e,n majorant
diagonal with η_e,L(e/E)η_n(n/V) and natural a_v(u/e)
over Ybox=ceil(6UV) has the SAME formerly established fixed
logarithmic loss +88:

 D_ungated_eta(Ybox) ≤ 2 Acoef² exp(L) L^(2CW1+344).

Unlike the previous rev64 proof at artificially capped Y0,
this now contains every physical pair under the true [U,2U),
η_n supported (V/2,3V) rectangle. Positive-square enlargement
from original selected-Q e remains legal. The original signed
Cauchy TypeII reduction with this new Y still needs a native
source-to-model input identity; not claimed automatically. -/
theorem parity_eventually_original_historical_ungated_box_weighted_diagonal_polylog434
    (Cbox : ℝ) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L) (U V E : ℝ),
      0≤U → 0≤V → U*V≤Cbox*Real.exp L →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      parityOriginalHistoricalUngatedWeightedExtendedDiagonal434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E)
          (parityOriginalHistoricalFullNEnvelope434 V)
          α signed (Nat.ceil (6*U*V))
          (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw) ≤
      2*Acoef^2*Real.exp L*
        L^(2*parityOriginalW1PolylogExponent434+344) := by
  filter_upwards [parity_eventually_original_historical_ungated_box_diagonal_polylog434 Cbox hCbox,
    eventually_ge_atTop (8:ℝ)] with L hDiag hLw
  refine ⟨hDiag.1,hLw,?_⟩
  intro hL U V E hU hV hUV band slot δ ξ rho K α signed Acoef hA hα
  let Y := Nat.ceil (6*U*V)
  have hLp : 0<L := by linarith
  let D := parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
      (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V) α signed Y
  have hBound := parity_original_historical_ungated_extended_diagonal_weight_le434
      (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V) α signed Y
      (parityOriginalHistoricalDyadicEtaWeight434 L E V hL) (2*L^(88:ℝ))
      (by intro e he n hn; exact (parity_original_historical_dyadic_eta_weight_polylog434 L E V hL e n).2)
  have hD := hDiag.2 U V hU hV hUV band slot δ ξ rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E)
    (parityOriginalHistoricalFullNEnvelope434 V)
    α signed Acoef hA hα
  have hC : 0≤2*L^(88:ℝ) := by positivity
  have hMultiply := mul_le_mul_of_nonneg_left hD hC
  have hPower : L^(88:ℝ)*L^(2*parityOriginalW1PolylogExponent434+256)=
      L^(2*parityOriginalW1PolylogExponent434+344) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  calc
    _ ≤ (2*L^(88:ℝ))*D := hBound
    _ ≤ (2*L^(88:ℝ)) * (Acoef^2*Real.exp L*
       L^(2*parityOriginalW1PolylogExponent434+256)) := hMultiply
    _ = 2*Acoef^2*Real.exp L*
       L^(2*parityOriginalW1PolylogExponent434+344) := by
         rw [←hPower]
         ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqBoxGlobalTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 29000000

/-- GENUINE original Parity (4.15)--(4.16) cap-free B' Fourier
GLOBAL physical B633 high-frequency tail at Ybox=ceil(6UV),
U V∈[expL,Cbox expL] original fixed-geometry box:

 ||full_ungated_B633_Fourier(Ybox)-BALL(T,Ybox)|| ≤
  [C_H L^[5(K0+90)(H+P+1)]/T^H]
   × [2ceil L^(K0+89)+1]
   × [Acoef² exp(L) L^(2CW1+256)].

The per-cell SOURCE 3D Schwartz H moment and true η_n physical
Z bound have been REPROVED at corrected Ybox; all subsequent
positive χ k Z mass-to-diagonal estimates are genuinely
parameterized by arbitrary Y and remain valid unchanged.
No old Y0 theorem or full Parity417 signed spectral saving used. -/
theorem parity_eventually_original_ungated_full_box_global_B633_fourier_tail_polylog434
    (K0 Cbox : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧ 6*Cbox≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho U V E : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
      E=U*L^(-K0) →
      (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) →
      ∀ (A R : ℝ) (hA : 0<A) (hR : 1≤R)
        (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀t : ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A),
      (∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) →
      (∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) →
      ∀ (H : ℕ),
      2*A*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L →
      (8*A^2*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
        (2:ℝ)^(H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
        ((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L) →
      ∀ (T : ℝ),0<T →
      let Q : ℝ :=
        parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport H *
        L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H
      let degree : ℝ := (2*Nat.ceil (L^(K0+89))+1:ℕ)
      ‖parityOriginalHistoricalUngatedFullOddFilteredB633FourierOuter434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed (Nat.ceil (6*U*V))
        buf (-Real.log A) (Real.log A) hSmooth hSupport -
       parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed (Nat.ceil (6*U*V))
        buf (-Real.log A) (Real.log A) hSmooth hSupport T‖ ≤
      Q * (degree * (Acoef^2*Real.exp L*
        L^(2*parityOriginalW1PolylogExponent434+256))) := by
  filter_upwards [parity_eventually_original_ungated_full_box_filtered_tail_le_coefficient_mass434
      K0 Cbox hK0 hCbox,
    parity_eventually_original_historical_ungated_box_diagonal_polylog434 Cbox hCbox] with
      L hFour hDiag
  refine ⟨hFour.1,hFour.2.1,hFour.2.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed Acoef hAcoef hAlpha
    hU hV hUV hUVhi hScale hDyad A R hA hR buf hSmooth hSupport hOne hCube
    H hLargeE hLargeN T hT
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let Y := Nat.ceil (6*U*V)
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let M := parityOriginalHistoricalUngatedFullOddFilteredCoefficientMass434
    d L E V hLw band slot δ ξ rho α signed Y K
  let D := parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
    d L band slot δ ξ rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E) J α signed Y
  let X := Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+256)
  let degree : ℝ := (2*Nat.ceil (L^(K0+89))+1:ℕ)
  let Q : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport H *
    L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H
  have hUpos : 0<U := hU
  have hRk : 0≤Q := by
    have hc := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport H hR
    dsimp [Q]
    have hLp : 0<L := by linarith [hFour.2.1]
    positivity
  have hDg : 0≤degree := by dsimp [degree]; positivity
  have hEpos : 0<E := by
    rw [hScale]
    exact mul_pos hU (Real.rpow_pos_of_pos (by linarith : 0<L) _)
  have hFirst := parity_original_historical_ungated_full_odd_filtered_B633_ball_error_le_mass434
    d L U E V hLw band slot δ ξ rho K α signed Y
    hU hEpos hV hDyad buf (-Real.log A) (Real.log A)
    hSmooth hSupport hOne T hT
  have hFourMass := hFour.2.2.2 hLw band slot δ ξ rho U V E K α signed
    hU hV hUV hUVhi hScale hDyad A R hA hR buf hSmooth hSupport hOne hCube
    H hLargeE hLargeN T hT
  have hMass : M≤degree*D :=
    parity_original_historical_ungated_full_odd_filtered_coefficient_mass_le_diagonal434
      d L U E V K0 hLw band slot δ ξ rho α signed Y K hU hScale hDyad
  have hDiagActual : D≤X := hDiag.2 U V hU.le hV.le hUVhi band slot δ ξ rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E) J α signed Acoef
    hAcoef hAlpha
  have hTotal : parityOriginalHistoricalUngatedFullOddFilteredB633TailMass434
      d L U E V hLw band slot δ ξ rho K α signed Y
      buf (-Real.log A) (Real.log A) hSmooth hSupport T ≤ Q*(degree*X) := by
    calc
      _ ≤ Q*M := hFourMass
      _ ≤ Q*(degree*D) := mul_le_mul_of_nonneg_left hMass hRk
      _ ≤ Q*(degree*X) := by
        have hh := mul_le_mul_of_nonneg_left hDiagActual hDg
        exact mul_le_mul_of_nonneg_left hh hRk
  exact hFirst.trans hTotal
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqBoxGlobalTailAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 30000000

/-- For EVERY real D≥0, full true original r20 h=-2 B509
UNGATED cap-free B' source at Ybox=ceil(6UV), UV in fixed
[expL,Cbox expL] geometric box has a COMMON fixed polynomial
3D Fourier truncation T=L^[5(K0+90)(P+2)+K0+89+2CW1+256+D]
with GLOBAL high-frequency B633 outer error
  ≤ 4 C1 Acoef² exp(L) L^-D.
Source H moment, physical Z bounds, χ mass and positive
diagonal were all REPROVED for Ybox; neither old Y0 cap nor
unrestricted Parity4.17 LOW frequency signed cancellation is used. -/
theorem parity_eventually_original_ungated_full_box_global_B633_fourier_tail_any_log434
    (K0 Cbox : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (A R : ℝ) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧ 6*Cbox≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho U V E : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
      E=U*L^(-K0) →
      (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) →
      ∀ (D : ℝ),0≤D →
      let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
      let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
      let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
      let T : ℝ := L^((X+(K0+89)+M)+D)
      let C1 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      ‖parityOriginalHistoricalUngatedFullOddFilteredB633FourierOuter434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed (Nat.ceil (6*U*V))
        buf (-Real.log A) (Real.log A) hSmooth hSupport -
       parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed (Nat.ceil (6*U*V))
        buf (-Real.log A) (Real.log A) hSmooth hSupport T‖ ≤
      4*C1*Acoef^2*Real.exp L*L^(-D) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let J : ℕ := 1+P
  let Bfixed : ℝ := max
    (2*A*(J.factorial:ℝ))
    (8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+(J.factorial:ℝ)*A)
  filter_upwards [parity_eventually_original_ungated_full_box_global_B633_fourier_tail_polylog434
      K0 Cbox hK0 hCbox, eventually_ge_atTop Bfixed] with L hGlobal hLarge
  refine ⟨hGlobal.1,hGlobal.2.1,hGlobal.2.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed Acoef hAcoef hAlpha
    hU hV hUV hUVhi hScale hDyad D hD
  dsimp only
  let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
  let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
  let T : ℝ := L^((X+(K0+89)+M)+D)
  let C1 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hLp : 0<L := by linarith [hGlobal.2.1]
  have hT : 0<T := Real.rpow_pos_of_pos hLp _
  have hLargeE : 2*A*((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L :=
    (le_max_left _ _).trans hLarge
  have hLargeN :
      8*A^2*((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
        (2:ℝ)^(1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
        ((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L :=
    (le_max_right _ _).trans hLarge
  have hTail := hGlobal.2.2.2 hLw band slot δ ξ rho U V E K α signed Acoef
    hAcoef hAlpha hU hV hUV hUVhi hScale hDyad
    A R hA hR buf hSmooth hSupport hOne hCube
    1 hLargeE hLargeN T hT
  dsimp only at hTail
  have hConst : 0≤C1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hNumeric := parity_original_historical_ungated_full_odd_global_tail_power_numeric434
    L K0 X M D C1 Acoef hLw hK0 hConst
  have hX : X=(5*(K0+90))*(((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1) := by
    dsimp [X,P]
    push_cast
    ring
  rw [←hX] at hTail
  have hNumeric' :
      parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 1 *
        L^X/T^1 *
        (((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ) *
          (Acoef^2*Real.exp L*L^M)) ≤
      4*C1*Acoef^2*Real.exp L*L^(-D) := by
    simpa only [pow_one, T] using hNumeric
  exact hTail.trans hNumeric'
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqBoxTypeIIPrecursor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- **SOURCE-CORRECTED ORIGINAL PARITY (4.10) PRECURSOR AT ITS
FULL PHYSICAL U-WINDOW**: the selected-Q e source is bounded by
its exact positive Cauchy mass times the original diagonal and
one true all-odd-e, all-n natural UNGATED B509 signed offdiagonal,

  |A_source(Ybox)|² ≤ (Σ selected-Q e,n |a_e β_n|²) ×
    [2 Acoef² exp L L^(2CW1+344) + ||OD_ungated(Ybox)||],

where Ybox=ceil(6UV), U V ≤ Cbox exp L for fixed Cbox≥1,
m∈[U,2U), n∈[V,2V] and η_n supports n<3V. This fixes the
artificial earlier cutoff Y0=floor(2exp L) without any loss of
logarithmic exponent in the genuine POSITIVE diagonal.

All selected-Q Pfree e source-to-natural a_v(u/e) identities,
actual B509 H0/fine alpha, signed epsilon, m prime roughness,
and the PRE-GRAM positive enlargement remain exact. No spectral
Parity(4.17) cancellation, hard signed subset comparison, final
TypeII4.2 or `Green64.green_64` is asserted. The identification
of the *original paper's B'* with this cap-complete Cauchy
input remains an explicit source-joining condition. -/
theorem parity_eventually_original_ungated_full_box_Cauchy_diag_offdiag434
    (Cbox : ℝ) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L) (U V E : ℝ),
      0<U → 0<V → U*V≤Cbox*Real.exp L → 0<E →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      let Y : ℕ := Nat.ceil (6*U*V)
      let Efull := parityOriginalHistoricalFullOddEEnvelope434 E
      let Nfull := parityOriginalHistoricalFullNEnvelope434 V
      let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
      let OD := parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K Efull Nfull α signed Y w
      ‖parityOriginalHistoricalCauchyAtDelta434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α β signed Y‖^2 ≤
      (∑e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*β n‖^2) *
        (2*Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+344) +‖OD‖) := by
  filter_upwards [parity_eventually_original_real_410_ungated_full_odd_eta_Cauchy434,
    parity_eventually_original_historical_ungated_box_weighted_diagonal_polylog434
      Cbox hCbox] with L hCauchy hDiagonal
  refine ⟨hDiagonal.1,hDiagonal.2.1,?_⟩
  intro hLw U V E hU hV hUV hE band slot δ ξ rho K J α β signed Acoef
    hDyad hNRange hAcoef hα
  dsimp only
  let Y : ℕ := Nat.ceil (6*U*V)
  let d := sourceOriginalLiteralDepth 20 L
  let Efull := parityOriginalHistoricalFullOddEEnvelope434 E
  let Nfull := parityOriginalHistoricalFullNEnvelope434 V
  let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
  let OD := parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
    d L band slot δ ξ rho K Efull Nfull α signed Y w
  let Diag := parityOriginalHistoricalUngatedWeightedExtendedDiagonal434
    d L band slot δ ξ rho K Efull Nfull α signed Y w
  let Sq := parityOriginalHistoricalUngatedWeightedExtendedSquare434
    d L band slot δ ξ rho K Efull Nfull α signed Y w
  let Mass : ℝ := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
    d L E band slot δ,
    ∑n∈J,‖parityOriginalHistoricalWindowAE434
      d L E band slot δ ξ rho e*β n‖^2
  let B : ℝ := 2*Acoef^2*Real.exp L*
      L^(2*parityOriginalW1PolylogExponent434+344)
  have hOld :
      ‖parityOriginalHistoricalCauchyAtDelta434 d L E band slot δ ξ rho
        K J α β signed Y‖^2 ≤ Mass*Sq :=
    hCauchy.2 hLw band slot δ ξ E V rho K J α β signed Y
      hE hV hNRange
  have hGram : ((Sq:ℝ):ℂ) = ((Diag:ℝ):ℂ)+OD :=
    parity_original_historical_ungated_weighted_extended_square_diag_offdiag434
      d L band slot δ ξ rho K Efull Nfull α signed Y w
  have hDiag : Diag ≤ B :=
    hDiagonal.2.2 hLw U V E hU.le hV.le hUV band slot δ ξ rho K
      α signed Acoef hAcoef hα
  have hMass : 0≤Mass := by
    dsimp [Mass]
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro n hn
    exact sq_nonneg _
  exact parity_original_physical_cauchy_gram_diagonal_and_offdiag_le434
    _ Mass Sq Diag B OD hMass hOld hGram hDiag
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqAllYCharacterMask -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Fix the source's previous artificial Y0 hardcode in the ACTUAL
original Parity(2.6) χ mask: the true odd-e, W-rough cofactor
orthogonality and physical determinant are valid for ALL
source cutoff Y, including the geometrically complete Ybox.
This is a genuinely UNCONDITIONAL original arithmetic theorem;
no Fourier/4.17 saving is assumed or unproven mask axiom added. -/
theorem parity_eventually_original_ungated_all_Y_smooth_fine_mask434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hL : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (U E : ℝ) (K : Finset ℕ)
        (prime : Bool) (lFine uFine : ℕ),
      0<U → E=U*L^(-K0) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      ∀ (e m mp n Y : ℕ),
      Odd e → m≠mp →
      U≤(m:ℝ) → (m:ℝ)<2*U →
      U≤(mp:ℝ) → (mp:ℝ)<2*U →
      parityOriginalHistoricalDyadicEtaEAtLReal434 L hL ((e:ℝ)/E)≠0 →
      parityOriginalHistoricalUngatedPhysicalValidN434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        Y e m mp n →
      restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) m≠0 →
      restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) mp≠0 →
      let k := parityOriginalHistoricalOffdiagK434 e m mp
      k≠0 ∧ (k.natAbs:ℝ)<L^(K0+89) ∧ Even k ∧
        (∑χ : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs χ *
          χ (mp : ZMod (2*k.natAbs)) *
          star (χ (m : ZMod (2*k.natAbs))))=1 := by
  filter_upwards [parity_actual_fine_K_restricted_rough434 S beta gamma hS hbeta hgamma,
    b638_eventually_poly_exp434 2 (K0+89) (1/2) (by norm_num) (by norm_num),
    eventually_ge_atTop (8:ℝ)] with L hRough hPoly hL8
  refine ⟨hL8,?_⟩
  intro hL band slot δ U E K prime lFine uFine hU hScale hl hFineLow
    e m mp n Y he hNe hmLo hmHi hmpLo hmpHi hEta hValid hAm hAmp
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  have hRoughM : sourceD20Rough (Real.exp (Real.sqrt L)) m :=
    hRough prime lFine uFine hl hFineLow K m hAm
  have hRoughMp : sourceD20Rough (Real.exp (Real.sqrt L)) mp :=
    hRough prime lFine uFine hl hFineLow K mp hAmp
  have hPhysical := parity_original_historical_ungated_physical_valid_k_z434
    (sourceOriginalLiteralDepth 20 L) L band slot δ
    Y e m mp n he hNe hValid
  dsimp only at hPhysical
  have hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k := hPhysical.2.2.2.1
  have hNonzero : k≠0 := hPhysical.1
  have hBound : (k.natAbs:ℝ)<L^(K0+89) :=
    parity_original_historical_full_odd_k_bound_polylog434
      L U E K0 e m mp k hL hU hScale hEta
      hmLo hmHi hmpLo hmpHi hDet
  have hW : (2:ℝ)≤Real.exp (Real.sqrt L) :=
    parity_rough_cutoff_at_least_two434 L (by linarith)
  have hmOdd : Odd m := parity_original_rough_cofactor_odd434
    (Real.exp (Real.sqrt L)) m hW hRoughM
  have hmpOdd : Odd mp := parity_original_rough_cofactor_odd434
    (Real.exp (Real.sqrt L)) mp hW hRoughMp
  have hPoly' : 2*L^(K0+89)≤Real.exp (Real.sqrt L) := by
    simpa only [Real.sqrt_eq_rpow] using hPoly
  have hq : ((2*k.natAbs : ℕ):ℝ)≤Real.exp (Real.sqrt L) := by
    calc
      _ = 2*(k.natAbs:ℝ) := by push_cast; ring
      _ ≤ 2*L^(K0+89) := mul_le_mul_of_nonneg_left hBound.le (by norm_num)
      _ ≤ Real.exp (Real.sqrt L) := hPoly'
  have hMask := parity_original_bilinear_shift_mask_fourier_one434
    e m mp he hmOdd hmpOdd k hNonzero hDet
    (Real.exp (Real.sqrt L)) hRoughM hq
  exact ⟨hNonzero,hBound,hMask.1,hMask.2⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqAllYMaskInsert -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Extend the SOURCE-true Parity(2.6) fine α character identity
to the actual physical supported signed z sum for ANY u cutoff Y,
including Ybox=ceil(6UV). This preserves the genuine η_e η_n
B509 support and proves no χ count or cancellation estimate. -/
theorem parity_eventually_original_ungated_all_Y_supported_z_mask_insert434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E V rho : ℝ) (K Nenv : Finset ℕ)
        (signed prime : Bool) (lFine uFine e m mp z Y : ℕ),
      0<U → E=U*L^(-K0) →
      U≤(m:ℝ) → (m:ℝ)<2*U →
      U≤(mp:ℝ) → (mp:ℝ)<2*U →
      e∈parityOriginalHistoricalFullOddEEnvelope434 E →
      m∈K → mp∈K.erase m →
      z∈parityOriginalHistoricalUngatedPhysicalValidZSupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        Y e m mp Nenv →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let k := parityOriginalHistoricalOffdiagK434 e m mp
      let W := ∑n∈(parityOriginalHistoricalCanonicalZNFibre434
        e m mp Nenv z).filter
          (parityOriginalHistoricalUngatedPhysicalValidN434
            (sourceOriginalLiteralDepth 20 L) L band slot δ
            Y e m mp),
        ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e n:ℝ):ℂ) *
          parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho alpha signed
            Y e n m mp
      W = ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        (parityShiftTwoMaskCoefficient434 k.natAbs χ *
          χ (mp : ZMod (2*k.natAbs)) *
          star (χ (m : ZMod (2*k.natAbs)))) * W := by
  filter_upwards [parity_eventually_original_ungated_all_Y_smooth_fine_mask434
    S beta gamma K0 hS hbeta hgamma] with L hMask
  refine ⟨hMask.1,?_⟩
  intro hLw band slot δ ξ U E V rho K Nenv signed prime lFine uFine
    e m mp z Y hU hScale hmLo hmHi hmpLo hmpHi he hm hmp hz
    hl hFineLow
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  let N := (parityOriginalHistoricalCanonicalZNFibre434 e m mp Nenv z).filter
    (parityOriginalHistoricalUngatedPhysicalValidN434
      (sourceOriginalLiteralDepth 20 L) L band slot δ
      Y e m mp)
  let W : ℂ := ∑n∈N,
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e n:ℝ):ℂ) *
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho alpha signed
        Y e n m mp
  change W = ∑χ : DirichletCharacter ℂ (2*k.natAbs),
    (parityShiftTwoMaskCoefficient434 k.natAbs χ *
      χ (mp : ZMod (2*k.natAbs)) *
      star (χ (m : ZMod (2*k.natAbs)))) * W
  by_cases hW : W=0
  · rw [hW]
    simp
  have hAm : alpha m ≠ 0 := by
    intro ham
    have hZero : W=0 := by
      dsimp [W]
      apply Finset.sum_eq_zero
      intro n hn
      unfold parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      simp [ham]
    exact hW hZero
  have hAmp : alpha mp ≠ 0 := by
    intro hamp
    have hZero : W=0 := by
      dsimp [W]
      apply Finset.sum_eq_zero
      intro n hn
      unfold parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      simp [hamp]
    exact hW hZero
  obtain ⟨n,hn,hTerm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hW
  have hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      (sourceOriginalLiteralDepth 20 L) L band slot δ
      Y e m mp n := (Finset.mem_filter.mp hn).2
  have hWeight : parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e n ≠ 0 := by
    intro hw0
    apply hTerm
    rw [hw0]
    simp
  have hEta : parityOriginalHistoricalDyadicEtaEAtLReal434 L hLw ((e:ℝ)/E) ≠ 0 := by
    unfold parityOriginalHistoricalDyadicEtaWeight434 at hWeight
    intro h0
    exact hWeight (by rw [h0,zero_mul])
  have heOdd : Odd e := (Finset.mem_filter.mp he).2
  have hNe : m≠mp := (Finset.mem_erase.mp hmp).1.symm
  have hFull := hMask.2 hLw band slot δ U E K prime lFine uFine
    hU hScale hl hFineLow e m mp n Y heOdd hNe
    hmLo hmHi hmpLo hmpHi hEta hValid hAm hAmp
  dsimp only at hFull
  exact parity_original_exact_mask_insert_complex434 k m mp W hFull.2.2.2
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqAllYCharacterJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 28000000

/-- Arbitrary-Y source-correct original Parity2.6 fine-character
B509 nonzero-η physical k/z reindex. Crucial to pass from the
former artificial u≤floor(2e^L) to natural Ybox=ceil(6UV) in
the corrected B' signed offdiagonal BEFORE 3D Fourier;
all e with original group P factors remain supported. -/
theorem parity_eventually_original_ungated_all_Y_full_odd_offdiag_masked434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E V rho : ℝ) (K Nenv : Finset ℕ)
        (prime signed : Bool) (lFine uFine Y : ℕ),
      0<U → E=U*L^(-K0) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
      parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
        alpha signed Y w =
      parityOriginalHistoricalUngatedFullOddWeightedMaskedKZ434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
        alpha signed Y w := by
  filter_upwards [parity_eventually_original_ungated_all_Y_supported_z_mask_insert434
      S beta gamma K0 hS hbeta hgamma] with L hMask
  refine ⟨hMask.1,?_⟩
  intro hLw band slot δ ξ U E V rho K Nenv prime signed lFine uFine Y
    hU hScale hDyad hl hFineLow
  dsimp only
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
  have hOdd : ∀e∈parityOriginalHistoricalFullOddEEnvelope434 E,Odd e := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  rw [parity_original_historical_ungated_weighted_full_odd_offdiag_k_z_exact434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
    alpha signed Y w hOdd]
  unfold parityOriginalHistoricalUngatedWeightedExtendedPhysicalKZ434
    parityOriginalHistoricalUngatedFullOddWeightedMaskedKZ434
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro mp hmp
  apply Finset.sum_congr rfl
  intro z hz
  have hmpMem : mp∈K.erase m := (Finset.mem_filter.mp hmp).1
  have hkCanon : parityOriginalHistoricalOffdiagK434 e m mp=k :=
    (Finset.mem_filter.mp hmp).2
  have hmD := hDyad m hm
  have hmpD := hDyad mp (Finset.mem_erase.mp hmpMem).2
  have hPoint := hMask.2 hLw band slot δ ξ U E V rho K Nenv signed prime
    lFine uFine e m mp z Y hU hScale hmD.1 hmD.2 hmpD.1 hmpD.2
    he hm hmpMem hz hl hFineLow
  dsimp only at hPoint
  rw [hkCanon] at hPoint
  exact hPoint


theorem parity_eventually_original_ungated_all_Y_full_odd_character_outer434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E V rho : ℝ) (K Nenv : Finset ℕ)
        (prime signed : Bool) (lFine uFine Y : ℕ),
      0<U → E=U*L^(-K0) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
      parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
        alpha signed Y w =
      parityOriginalHistoricalUngatedFullOddCharacterOuter434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
        alpha signed Y w := by
  filter_upwards [parity_eventually_original_ungated_all_Y_full_odd_offdiag_masked434
      S beta gamma K0 hS hbeta hgamma] with L hMask
  refine ⟨hMask.1,?_⟩
  intro hLw band slot δ ξ U E V rho K Nenv prime signed lFine uFine Y
    hU hScale hDyad hl hFineLow
  dsimp only
  rw [hMask.2 hLw band slot δ ξ U E V rho K Nenv prime signed
    lFine uFine Y hU hScale hDyad hl hFineLow]
  exact parity_original_historical_ungated_full_odd_masked_k_z_eq_character_outer434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E) Nenv
    (restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine))
    signed Y
    (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqNoSharpUSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Any true ORIGINAL h=-2 source u with u+2=m*n is ≤ m*n.
Therefore the finite physical singleton-u carrier has the SAME
set of terms for EVERY outer cutoff Y≥m*n, as for its canonical
mathematically unlimited cap m*n. This is an exact equality of
source finite sets (not a comparison of complex signed sums). -/
theorem parity_original_historical_fixed_mn_source_unchanged_above_product434
    (Y m n : ℕ) (hY : m*n≤Y) :
    parityOriginalHistoricalFixedMNUSupport434 Y m n =
      parityOriginalHistoricalFixedMNUSupport434 (m*n) m n := by
  ext u
  simp only [parityOriginalHistoricalFixedMNUSupport434,
    Finset.mem_filter,Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hu0,huY⟩,hm,hn,hmn⟩
    exact ⟨⟨hu0,by omega⟩,hm,hn,hmn⟩
  · rintro ⟨⟨hu0,hum⟩,hm,hn,hmn⟩
    exact ⟨⟨hu0,hum.trans hY⟩,hm,hn,hmn⟩

/-- The FULL original physical m,n dyadic source satisfies
m*n≤Ybox=ceil(6UV) for EVERY m≤2U and n≤3V, *even when mn≤2*
and the natural a_v(v) source is zero. No e, v, η or H0 premise.
This stronger geometric upper bound is used to remove the actual
finite source u cap before signed Cauchy and Fourier. -/
theorem parity_original_historical_full_mn_box_product_cap434
    (U V : ℝ) (hU : 0≤U) (hV : 0≤V)
    (m n : ℕ)
    (hm : (m:ℝ)≤2*U) (hn : (n:ℝ)≤3*V) :
    m*n≤Nat.ceil (6*U*V) := by
  have hn0 : 0≤(n:ℝ) := Nat.cast_nonneg _
  have h2U : 0≤2*U := by positivity
  have hMul : (m:ℝ)*(n:ℝ)≤(2*U)*(3*V) :=
    mul_le_mul hm hn hn0 h2U
  have hUV : (m*n:ℝ)≤6*U*V := by
    push_cast
    nlinarith [hMul]
  have hCeil : (6*U*V:ℝ)≤(Nat.ceil (6*U*V):ℝ) := Nat.le_ceil _
  exact_mod_cast hUV.trans hCeil

/-- Natural ORIGINAL Parity(4.7) a_v((mn−2)/e) physical Cauchy
coefficient with NO externally chosen sharp u≤Y cutoff.
Using Y=m*n only enumerates the unique positive arithmetic
u satisfying m*n=u+2. It is not an analytic window parameter.
This is valid for source odd or even e and keeps full B509 H0,
W1 and signed ε with exact inherited prime-power multiplicities. -/
def parityOriginalHistoricalUngatedCauchyPhysicalNoUCap434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (e n m : ℕ) : ℂ :=
  parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
    d L band slot δ ξ rho signed (m*n) e n m

/-- On every TRUE physical post-Cauchy box m≤2U, n≤3V,
the natural B509 SOURCE coefficient at the large containing
Ybox equals literally the cap-FREE Parity(4.7) one. This is exact
for COMPLEX values; no signed subset positivity assumption,
no smooth majorant error, no restriction on e and no extra
factor |K|. -/
theorem parity_original_historical_ungated_Cauchy_physical_box_eq_no_u_cap434
    (d : ℕ) (L U V : ℝ) (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (e n m : ℕ)
    (hm : (m:ℝ)≤2*U) (hn : (n:ℝ)≤3*V) :
    parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed (Nat.ceil (6*U*V)) e n m =
    parityOriginalHistoricalUngatedCauchyPhysicalNoUCap434
      d L band slot δ ξ rho signed e n m := by
  rw [parity_original_historical_ungated_Cauchy_ENM_eq_fixed_EU434]
  unfold parityOriginalHistoricalUngatedCauchyPhysicalNoUCap434
  rw [parity_original_historical_ungated_Cauchy_ENM_eq_fixed_EU434]
  rw [parity_original_historical_fixed_mn_source_unchanged_above_product434
    (Nat.ceil (6*U*V)) m n
    (parity_original_historical_full_mn_box_product_cap434
      U V hU hV m n hm hn)]

/-- CAP-FREE ORIGINAL Parity(4.7) selected-e input B' after its
smooth allocation/Fourier separation. There is NO artificial
u≤floor(2exp L) cutoff: each singleton u is exactly m*n−2.
The original selected-Q e outer coefficient and β_n are kept
unaltered, and the natural H0 a_v(u/e) is used inside.
This is the appropriate physical source formula for Parity(4.10).
Identification to the original pre-allocation bilinear remains
the independent earlier source-joining obligation. -/
def parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) : ℂ :=
  ∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑n∈J,
      (parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e*β n)*
      (∑m∈K,α m*parityOriginalHistoricalUngatedCauchyPhysicalNoUCap434
        d L band slot δ ξ rho signed e n m)

/-- The PRE-GRAM source Cauchy with the honest containing
Ybox=ceil(6UV) agrees EXACTLY with the CAP-FREE original
Parity(4.7) natural a_v((mn-2)/e) coefficient B' on every original
cofactor K and n-dyad J inside m≤2U,n≤3V, even with signed
ε and complex original allocation phases. No extra error term.
It is the missing SOURCE-model identification at the enlarged
Ybox, not a claim that prior Y0=2x is sufficient. -/
theorem parity_original_historical_ungated_selected_Cauchy_box_eq_no_u_cap434
    (d : ℕ) (L E U V : ℝ) (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool)
    (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V) :
    parityOriginalHistoricalUngatedCauchyAtDelta434
      d L E band slot δ ξ rho K J α β signed (Nat.ceil (6*U*V)) =
    parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
      d L E band slot δ ξ rho K J α β signed := by
  unfold parityOriginalHistoricalUngatedCauchyAtDelta434
    parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [parity_original_historical_ungated_Cauchy_physical_box_eq_no_u_cap434
    d L U V hU hV band slot δ ξ rho signed e n m (hK m hm) (hJ n hn)]

/-- The earlier allocated-Q original historical Cauchy coefficient
is ALSO EXACTLY the new cap-free Parity(4.7) source if e on the
selected Q carrier is P-prime-free. This is proved before Gram
and before extending e to all odd rows. It is NOT a signed
subset comparison of B633 correlations. -/
theorem parity_original_historical_selected_Q_Cauchy_box_eq_no_u_cap434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L) (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool)
    (hSelected : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,0<e)
    (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V) :
    parityOriginalHistoricalCauchyAtDelta434
      d L E band slot δ ξ rho K J α β signed (Nat.ceil (6*U*V)) =
    parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
      d L E band slot δ ξ rho K J α β signed := by
  calc
    _ = parityOriginalHistoricalUngatedCauchyAtDelta434
      d L E band slot δ ξ rho K J α β signed (Nat.ceil (6*U*V)) :=
        parity_original_historical_selected_Cauchy_eq_ungated434
          d L E hL band slot δ ξ rho K J α β signed
          (Nat.ceil (6*U*V)) hSelected
    _ = _ := parity_original_historical_ungated_selected_Cauchy_box_eq_no_u_cap434
      d L E U V hU hV band slot δ ξ rho K J α β signed hK hJ
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqNoCapTypeIIPrecursor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 28000000

/-- FULL SOURCE-CORRECT ORIGINAL PARITY (4.7)--(4.13) CAUCHY
PRECURSOR FOR THE ACTUAL **CAP-FREE** NATURAL a_v((mn−2)/e)
POST-ALLOCATION B' COEFFICIENT, not for the earlier artificial
Y0=floor(2exp L) Cauchy input:

 ‖B'_no_u_cap‖² ≤ (Σ source selected-Q e,n |a_e β_n|²) ×
  [2 Acoef² exp L L^(2CW1+344) + ‖OD_full_ungated(Ybox)‖]

with Ybox=ceil(6UV), UV≤Cbox exp L fixed Cbox≥1,
K⊆[U,2U), J⊆[V,2V]. The equality from cap-free selected-Q
B' to source Ybox is PROVED pointwise before Cauchy, so the
full positive diagonal with Ybox is mathematically legitimate.
The original h=-2 B509 Q/P/H0 signed epsilon, all original
factorials, real original ψ/fine α, repeated prime factors and
a_e exterior selected-Q source are intact. No cancellation from
Parity(4.17) is assumed or claimed here. -/
theorem parity_eventually_original_capfree_Bprime_Cauchy_box_precursor434
    (Cbox : ℝ) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L) (U V E : ℝ),
      0<U → 0<V → U*V≤Cbox*Real.exp L → 0<E →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      let Y : ℕ := Nat.ceil (6*U*V)
      let Efull := parityOriginalHistoricalFullOddEEnvelope434 E
      let Nfull := parityOriginalHistoricalFullNEnvelope434 V
      let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
      let OD := parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K Efull Nfull α signed Y w
      ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α β signed‖^2 ≤
      (∑e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*β n‖^2) *
        (2*Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+344) +‖OD‖) := by
  filter_upwards [parity_eventually_original_ungated_full_box_Cauchy_diag_offdiag434
      Cbox hCbox,parity_eventually_original_cartesian_selected_e_odd_unit434]
    with L hPrec hOdd
  refine ⟨hPrec.1,hPrec.2.1,?_⟩
  intro hLw U V E hU hV hUV hE band slot δ ξ rho K J α β signed Acoef
    hK hJ hA hα
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let Y : ℕ := Nat.ceil (6*U*V)
  have hSource :
      parityOriginalHistoricalCauchyAtDelta434
        d L E band slot δ ξ rho K J α β signed Y =
      parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
        d L E band slot δ ξ rho K J α β signed := by
    apply parity_original_historical_selected_Q_Cauchy_box_eq_no_u_cap434
      d L E U V (by linarith [hPrec.1] : 0<L) hU.le hV.le
      band slot δ ξ rho K J α β signed
    · intro e he
      exact ((hOdd.2 band slot δ e (Finset.mem_filter.mp he).1).1).pos
    · intro m hm
      exact (hK m hm).2.le
    · intro n hn
      linarith [(hJ n hn).2]
  have hBound := hPrec.2.2 hLw U V E hU hV hUV hE band slot δ ξ rho K J
    α β signed Acoef hK hJ hA hα
  dsimp only at hBound
  rw [hSource] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqNoCapB633FullJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 28500000

/-- SOURCE-CORRECT ORIGINAL PARITY (4.7)--(4.16) PHYSICAL B' to
FULL B633 Fourier Cauchy reduction with NO artificial Y0 u cap:

 |B'_no_u_cap|² ≤ (Σ TRUE selected-Q e,n |a_e β_n|²) ×
   [ 2Acoef² expL L^(2CW1+344)
     + ||FULL TRUE UNGATED B633 FOURIER(Ybox)|| ],

Ybox=ceil(6UV), UV≤Cbox expL, Cbox≥1 fixed. This exact
SOURCE join proceeds in legal order: selected-Q gated source
identical to natural a_v((mn−2)/e) with no sharp cap; enlarge
its POSITIVE Cauchy square to all odd e≤2E, n≤3V; prove true
corrected shifted-divisor diagonal for complete u≤Ybox; open
complex Gram; insert the ACTUAL original fine-alpha Parity2.6 χ
mask at arbitrary Ybox; reindex k/z into one literal physical
signed B633 Fourier 3D outer using exact native source residual.

No Parity4.17 LOW-FREQUENCY spectral saving or unjustified signed
sub-sum comparison is assumed. This is the mathematically
corrected B' Fourier interface needed before the final original
Parity TypeII(4.2), proxies, sieve and Green64.green_64. -/
theorem parity_eventually_original_capfree_Bprime_Cauchy_to_full_B633_3D434
    (Cbox S beta gamma K0 : ℝ) (hCbox : 1≤Cbox)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma)
    (A : ℝ) (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ, buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (U E V rho : ℝ) (K J : Finset ℕ) (βseq : ℕ → ℂ)
        (prime signed : Bool) (lFine uFine : ℕ) (Acoef : ℝ),
      0<U → 0<V → U*V≤Cbox*Real.exp L → E=U*L^(-K0) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      0≤Acoef → (∀m∈K,‖alpha m‖≤Acoef) →
      let Y : ℕ := Nat.ceil (6*U*V)
      let Amass := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*βseq n‖^2
      ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha βseq signed‖^2 ≤
      Amass *
        (2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)+
          ‖parityOriginalHistoricalUngatedFullOddB633FourierOuter434
            (sourceOriginalLiteralDepth 20 L) L U E V hLw
            band slot δ ξ rho K alpha signed Y
            buf (-Real.log A) (Real.log A) hSmooth hSupport‖) := by
  filter_upwards [parity_eventually_original_capfree_Bprime_Cauchy_box_precursor434
      Cbox hCbox,
    parity_eventually_original_ungated_all_Y_full_odd_character_outer434
      S beta gamma K0 hS hbeta hgamma] with L hC hMask
  refine ⟨hC.1,hC.2.1,?_⟩
  intro hLw band slot δ ξ U E V rho K J betaSeq prime signed lFine uFine Acoef
    hU hV hUV hScale hDyad hNRange hl hFineLow
  dsimp only
  intro hAcoef hAlpha
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let Y : ℕ := Nat.ceil (6*U*V)
  have hLp : 0<L := by linarith [hC.2.1]
  have hE : 0<E := by
    rw [hScale]
    exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  have hOriginal := hC.2.2 hLw U V E hU hV hUV hE band slot δ ξ rho K J
    alpha betaSeq signed Acoef hDyad hNRange hAcoef hAlpha
  have hMasked := hMask.2 hLw band slot δ ξ U E V rho K
    (parityOriginalHistoricalFullNEnvelope434 V) prime signed lFine uFine Y
    hU hScale hDyad hl hFineLow
  have hB633 := parity_original_historical_ungated_full_odd_character_outer_eq_B633_fourier434
    (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
    K alpha signed Y hU hE hV hDyad
    buf (-Real.log A) (Real.log A) hSmooth hSupport hOne
  dsimp only at hOriginal
  rw [hMasked,hB633] at hOriginal
  exact hOriginal
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqNoCapFinalReduction -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 30000000

/-- END-TO-END corrected original Parity(4.7)--(4.16)
cap-FREE natural selected-Q B' Cauchy TypeII source reduced to
one TRUE physically source-filtered B633 LOW-FREQUENCY 3D ball,
with the exact original χ, B509 H0, signed ε and fine α, plus
unconditional unchanged positive diagonal and the global
Fourier error 4 C1 Acoef² expL L^-D for any requested D≥0.
Geometric source cap Ybox=ceil(6UV) was proven identical to the
natural no-u-cap B', with UV∈[expL,Cbox expL] and Cbox fixed,
not the old artificially truncated Y0=2expL.

The low-frequency signed subset is still NOT shown bounded by
the unrestricted Parity4.17 correlation; this remains the genuine
separate analytic support-transfer debt. No final TypeII4.2,
positive prime mass or Green64.green_64 is assumed. -/
theorem parity_eventually_original_capfree_Bprime_low_frequency_typeII_reduction434
    (Cbox S beta gamma K0 : ℝ) (hCbox : 1≤Cbox) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) (hK0 : 0≤K0)
    (A R : ℝ) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧ 8≤L ∧ 6*Cbox≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho U V E : ℝ) (K J : Finset ℕ) (β : ℕ → ℂ)
        (prime signed : Bool) (lFine uFine : ℕ) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,
        ‖(restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)) m‖≤Acoef) →
      0<U → 0<V → Real.exp L≤U*V → U*V≤Cbox*Real.exp L →
      E=U*L^(-K0) →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      2≤lFine → Real.exp (beta*L)≤(lFine:ℝ) →
      ∀ (D : ℝ),0≤D →
      let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
      let X : ℝ := 5*(K0+90)*((P:ℝ)+2)
      let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
      let T : ℝ := L^((X+(K0+89)+M)+D)
      let C1 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
        A R buf hSmooth hSupport 1
      let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      let Amass : ℝ := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*β n‖^2
      ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha β signed‖^2 ≤
      Amass * (2*Acoef^2*Real.exp L*
        L^(2*parityOriginalW1PolylogExponent434+344) +
        ‖parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
          (sourceOriginalLiteralDepth 20 L) L U E V hLw
          band slot δ ξ rho K alpha signed (Nat.ceil (6*U*V))
          buf (-Real.log A) (Real.log A) hSmooth hSupport T‖ +
        4*C1*Acoef^2*Real.exp L*L^(-D)) := by
  filter_upwards [parity_eventually_original_capfree_Bprime_Cauchy_to_full_B633_3D434
    Cbox S beta gamma K0 hCbox hS hbeta hgamma A buf hSmooth hSupport hOne,
    parity_eventually_original_ungated_full_box_global_B633_fourier_tail_any_log434
      K0 Cbox hK0 hCbox A R hA hR buf hSmooth hSupport hOne hCube] with
    L hParent hTail
  refine ⟨hParent.1,hParent.2.1,hTail.2.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K J betaSeq prime signed
    lFine uFine Acoef hAcoef hAlpha hU hV hUV hUVhi hScale hDyad hNRange
    hl hFineLow D hD
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let Y := Nat.ceil (6*U*V)
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let M : ℝ := 2*parityOriginalW1PolylogExponent434+256
  let X : ℝ := 5*(K0+90)*(((volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℝ)+2)
  let T : ℝ := L^((X+(K0+89)+M)+D)
  let C1 : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Amass : ℝ := ∑e∈parityOriginalHistoricalCauchyActiveESupport434
    d L E band slot δ,
      ∑n∈J,‖parityOriginalHistoricalWindowAE434
        d L E band slot δ ξ rho e*betaSeq n‖^2
  let B : ℝ := 2*Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+344)
  let Err : ℝ := 4*C1*Acoef^2*Real.exp L*L^(-D)
  let Full := parityOriginalHistoricalUngatedFullOddB633FourierOuter434
    d L U E V hLw band slot δ ξ rho K alpha signed Y
    buf (-Real.log A) (Real.log A) hSmooth hSupport
  let Filtered := parityOriginalHistoricalUngatedFullOddFilteredB633FourierOuter434
    d L U E V hLw band slot δ ξ rho K alpha signed Y
    buf (-Real.log A) (Real.log A) hSmooth hSupport
  let Ball := parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
    d L U E V hLw band slot δ ξ rho K alpha signed Y
    buf (-Real.log A) (Real.log A) hSmooth hSupport T
  have hEpos : 0<E := by
    rw [hScale]
    exact mul_pos hU (Real.rpow_pos_of_pos (by linarith [hParent.2.1] : 0<L) _)
  have hParent' := hParent.2.2 hLw band slot δ ξ U E V rho K J betaSeq
    prime signed lFine uFine Acoef
    hU hV hUVhi hScale hDyad hNRange hl hFineLow hAcoef hAlpha
  have hTail' := hTail.2.2.2 hLw band slot δ ξ rho U V E K alpha signed Acoef
    hAcoef hAlpha hU hV hUV hUVhi hScale hDyad D hD
  have hEq : Full=Filtered :=
    parity_original_historical_ungated_full_odd_B633_outer_eq_nonzero_weight434
      d L U E V hLw band slot δ ξ rho K alpha signed Y
      hU hEpos hV hDyad buf (-Real.log A) (Real.log A)
      hSmooth hSupport hOne
  have hMassNonneg : 0≤Amass := by
    dsimp [Amass]
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro n hn
    exact sq_nonneg _
  have hTriangle : ‖Full‖≤‖Ball‖+‖Filtered-Ball‖ := by
    rw [hEq]
    have hh := norm_add_le Ball (Filtered-Ball)
    have hx : Ball+(Filtered-Ball)=Filtered := by ring
    rw [hx] at hh
    exact hh
  have hFourBound : ‖Full‖≤‖Ball‖+Err :=
    hTriangle.trans (add_le_add (le_refl ‖Ball‖) hTail')
  have hParentBound :
      ‖parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
        d L E band slot δ ξ rho K J alpha betaSeq signed‖^2 ≤
      Amass*(B+‖Full‖) := hParent'
  calc
    _ ≤ Amass*(B+‖Full‖) := hParentBound
    _ ≤ Amass*(B+(‖Ball‖+Err)) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl B) hFourBound) hMassNonneg
    _ = Amass*(B+‖Ball‖+Err) := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalIntrinsicEq417Source -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Actual Parity (4.17) full two-endpoint h=-2 cofactor expression
on the original physical source carrier, now using the INTRINSIC
B509 skipped-Q c_r from the source coefficient a_v(v), rather than
the old PrimeSlotCore API whose residual signature exposed alpha.
The full signed W1/E pair is still present through the original pair. -/
def parityOriginalIntrinsicEq417Cofactors434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (alpha : ℕ → ℂ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (lo hi : ℕ) (rho xi1 xi2 xi3 sigma Z : ℝ)
    (k : ℤ) (N : Finset ℕ) (signed : Bool) (psi : ℝ → ℂ) : ℂ :=
  parityOriginalEq417PhysicalCofactors434 L rho xi1 xi2 xi3 sigma Z k N
    alpha (parityOriginalIntrinsicResidual434 d L band slot δ ξ)
    q χ lo hi signed psi

/-- The true source H(vStar) from Parity (4.7) is EXACTLY the prime
rest used in Parity (4.16), for either sign, source sigma=0 and any
real rho, without introducing a nonzero source reserved-prime phase. -/
theorem parity_original_intrinsic_signed_av_eq_actual_eq417_core434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ rho : ℝ) (signed : Bool) (vStar v : ℕ)
    (hvStar : 0 < vStar) (hv : 0 < v) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
    parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vStar v =
    imaginaryPower v rho *
      (((sourceMarkedWeight (1/2:ℝ) 1
          (sourceOriginalPAllActualBands 20 L) v *
        groupSign (sourceOriginalPAllActualBands 20 L) signed v):ℝ):ℂ) *
      b633PrimeRest434 F.lo F.hi 0 F.residual vStar := by
  dsimp only
  rw [←parity_original_signed_physical_AV_is_intrinsic434
    d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 rho signed vStar v]
  exact parity_original_signed_aV_source_zero_sigma_eq417434
    d L band slot δ ξ K alpha q χ σ₀ σ₁ rho signed vStar v hvStar hv

/-- Literal full physical (4.17) special-source cofactor sum equals
the same sum with genuine intrinsic c_r; no change in selected fine
alpha_m, original h=-2 shift 2k, character or signed endpoint. -/
theorem parity_original_actual_eq417_native_residual_eq_intrinsic434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (lo hi : ℕ) (rho xi1 xi2 xi3 sigma Z : ℝ)
    (k : ℤ) (N : Finset ℕ) (signed : Bool) (psi : ℝ → ℂ) :
    parityOriginalEq417PhysicalCofactors434 L rho xi1 xi2 xi3 sigma Z k N
      (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).alpha
      (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).residual
      q χ lo hi signed psi =
    parityOriginalIntrinsicEq417Cofactors434 d L band slot δ ξ
      (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).alpha
      q χ lo hi rho xi1 xi2 xi3 sigma Z k N signed psi := by
  rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalIntrinsicEq417Saving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Actual original Parity (4.17) UNGATED physical cofactor source has
arbitrary inverse-log saving, for EACH original signed epsilon=1/E,
for the genuine b629 fine-cell alpha, original shifted h=-2 physical
2*k endpoints, character modulo 2|k|, actual original 20! Q B509
intrinsic residual c_r and reserved H_0. In contrast to generic
H_sigma, sigma=0 here is obtained from the ACTUAL source.
This is a specialized signed single-character summand only: NOT the
beta/4-Ppart-gated correlation, original complete Cauchy square,
full k/character/Fourier sums, general E4.1, TypeII or Green64. -/
theorem parity_eventually_intrinsic_signed_original_Parity417_ungated_saving434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi beta gamma : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
            band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (signed : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L
          band slot delta freq (Finset.Icc a b)
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let original := parityOriginalIntrinsicEq417Cofactors434
          (sourceOriginalLiteralDepth 20 L) L band slot delta freq F.alpha
          (2*k.natAbs) chi F.lo F.hi rho xi1 xi2 xi3 0 Z k
          (Finset.Icc 1 ⌊64*Z⌋₊) signed psi
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hOld⟩ :=
    parity_eventually_actual_original_Parity417_physical_cofactor_saving434 jQ target
      Cfreq CZ Ck Cpsi beta gamma Kpsi
      hTarget hCZ hCk hCpsi hKpsi hbeta hgamma
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hOld,eventually_gt_atTop (0:ℝ)] with L hOldL hL
  refine ⟨hOldL.1,hOldL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed psi hSmooth hSupport hReg
  dsimp only
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L
    band slot delta freq (Finset.Icc a b)
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  have h0 : |(0:ℝ)| ≤ L^Cfreq := by
    simpa only [abs_zero] using (Real.rpow_nonneg hL.le Cfreq)
  have hBound := hOldL.2.2 hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 0 hrho hxi1 hxi2 hxi3 h0
    prime lFine uFine a b hFineLow hl hu hub signed psi hSmooth hSupport hReg
  change ‖parityOriginalEq417PhysicalCofactors434 L rho xi1 xi2 xi3 0 Z k
    (Finset.Icc 1 ⌊64*Z⌋₊) F.alpha F.residual
    (2*k.natAbs) chi F.lo F.hi signed psi‖ ≤ Z*L^(-target) at hBound
  rw [parity_original_actual_eq417_native_residual_eq_intrinsic434
    (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0 F.lo F.hi rho xi1 xi2 xi3 0 Z k
    (Finset.Icc 1 ⌊64*Z⌋₊) signed psi] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalEq417BetaSummand -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The literal full original Parity(4.17) single-z summand,
including both original P-W1 weights, E-signs, physical z+2k,
all phases, and unchanged separate prime-slot cores. -/
def parityOriginalEq417FullTerm434
    (L rho xi3 Z : ℝ) (k : ℤ) (F G : PrimeSlotCore)
    (signed : Bool) (psi : ℝ → ℂ) (z : ℕ) : ℂ :=
  if 0 < (z:ℤ)+2*k then
    let zp := ((z:ℤ)+2*k).toNat
    psi ((z:ℝ)/Z) * imaginaryPower z (rho+xi3) *
      imaginaryPower zp (-rho) *
      primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F z *
      primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G zp *
      ((groupSign (sourceOriginalPAllActualBands 20 L) signed z *
        groupSign (sourceOriginalPAllActualBands 20 L) signed zp : ℝ):ℂ) *
      ((sourceMarkedWeight (1/2:ℝ) 1 (sourceOriginalPAllActualBands 20 L) z *
        sourceMarkedWeight (1/2:ℝ) 1 (sourceOriginalPAllActualBands 20 L) zp : ℝ):ℂ)
  else 0

/-- FULL Parity (4.17) with actual original beta/4 Ppart caps at
BOTH physical endpoints, not a one-sided or old 1/44 cap. -/
def parityOriginalEq417BetaCapped434
    (beta L rho xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (F G : PrimeSlotCore) (signed : Bool) (psi : ℝ → ℂ) : ℂ :=
  ∑ z ∈ N, parityOriginalPhysicalPairPcapBeta434 beta L z
    (((z:ℤ)+2*k).toNat) *
    parityOriginalEq417FullTerm434 L rho xi3 Z k F G signed psi z

/-- Literal difference of original UNGATED and true physical
beta/4-Pcap-gated Parity 4.17; no correlation loss postulated. -/
theorem parity_original_eq417_beta_capped_exact_complement434
    (beta L rho xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (F G : PrimeSlotCore) (signed : Bool) (psi : ℝ → ℂ) :
    parityOriginalEq417WithFirstCore434 L rho xi3 Z k N F G signed psi -
      parityOriginalEq417BetaCapped434 beta L rho xi3 Z k N F G signed psi =
    ∑ z ∈ N, (1 - parityOriginalPhysicalPairPcapBeta434 beta L z
      (((z:ℤ)+2*k).toNat)) *
      parityOriginalEq417FullTerm434 L rho xi3 Z k F G signed psi z := by
  unfold parityOriginalEq417WithFirstCore434 parityOriginalEq417BetaCapped434
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  change parityOriginalEq417FullTerm434 L rho xi3 Z k F G signed psi z -
    parityOriginalPhysicalPairPcapBeta434 beta L z (((z:ℤ)+2*k).toNat) *
      parityOriginalEq417FullTerm434 L rho xi3 Z k F G signed psi z = _
  ring

/-- The actual signed P/parity factor has norm precisely 1, for
both epsilon=1 and epsilon=E, including multiplicity-counted P parity. -/
theorem parity_original_eq417_signed_pair_abs_one434
    (L : ℝ) (signed : Bool) (z zp : ℕ) :
    ‖(((groupSign (sourceOriginalPAllActualBands 20 L) signed z *
      groupSign (sourceOriginalPAllActualBands 20 L) signed zp):ℝ):ℂ)‖ = 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  rw [←parity_original_signed_epsilon_eq_eq417_groupSign434,
      ←parity_original_signed_epsilon_eq_eq417_groupSign434]
  simp only [parity_original_P_signed_epsilon_abs_one434, one_mul]

/-- Full real original marked weights have exactly their original
source W1 norms at BOTH physical endpoints, not at stripped cores. -/
theorem parity_original_eq417_marked_pair_norm434
    (L : ℝ) (z zp : ℕ) :
    ‖(((sourceMarkedWeight (1/2:ℝ) 1
          (sourceOriginalPAllActualBands 20 L) z *
        sourceMarkedWeight (1/2:ℝ) 1
          (sourceOriginalPAllActualBands 20 L) zp):ℝ):ℂ)‖ =
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) z *
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) zp := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  rw [←parity_original_W1_eq_eq417_one_marked434,
      ←parity_original_W1_eq_eq417_one_marked434]
  rw [abs_mul,abs_of_nonneg (source_original_W1_nonneg _ _),
    abs_of_nonneg (source_original_W1_nonneg _ _)]

/-- Actual source Parity(4.17) complex cofactor integrand, with arbitrary
fixed rho,xi3 and genuine physical sign, is dominated pointwise by
TWO prime-core divisor squares times original W1(z)W1(z+2k).
The only parameter in front is the actual physical cutoff norm.
No source divisor count is evaluated at an invented endpoint. -/
theorem parity_original_eq417_full_term_tau2_pointwise434
    (L rho xi3 Z : ℝ) (k : ℤ) (F G : PrimeSlotCore)
    (signed : Bool) (psi : ℝ → ℂ) (z : ℕ)
    (hz : 0<z) (hzp : 0 < (z:ℤ)+2*k)
    (hF : ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F z‖ ≤
       (z.divisors.card:ℝ)^2)
    (hG : ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G
        (((z:ℤ)+2*k).toNat)‖ ≤
       ((((z:ℤ)+2*k).toNat.divisors.card:ℝ)^2)) :
    ‖parityOriginalEq417FullTerm434 L rho xi3 Z k F G signed psi z‖ ≤
      ‖psi ((z:ℝ)/Z)‖ * (z.divisors.card:ℝ)^2 *
      ((((z:ℤ)+2*k).toNat.divisors.card:ℝ)^2) *
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) z *
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L)
        (((z:ℤ)+2*k).toNat) := by
  let zp := (((z:ℤ)+2*k).toNat)
  have hzpNat : 0<zp := by dsimp [zp]; omega
  have hphasez := b656_imaginary_power_norm434 z hz (rho+xi3)
  have hphasezp := b656_imaginary_power_norm434 zp hzpNat (-rho)
  have hsign := parity_original_eq417_signed_pair_abs_one434 L signed z zp
  have hmark := parity_original_eq417_marked_pair_norm434 L z zp
  dsimp only [zp] at hphasezp hsign hmark
  unfold parityOriginalEq417FullTerm434
  simp only [hzp,ite_true]
  simp only [norm_mul,hphasez,hphasezp,hsign,hmark,mul_one]
  have hWz := source_original_W1_nonneg (sourceOriginalPAllActualBands 20 L) z
  have hWp := source_original_W1_nonneg (sourceOriginalPAllActualBands 20 L) zp
  have hpsi : 0 ≤ ‖psi ((z:ℝ)/Z)‖ := norm_nonneg _
  have hzN : 0 ≤ (z.divisors.card:ℝ)^2 := sq_nonneg _
  have hzpN : 0 ≤ (zp.divisors.card:ℝ)^2 := sq_nonneg _
  have hcore :
      ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F z‖ *
        ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G zp‖ ≤
        (z.divisors.card:ℝ)^2 * (zp.divisors.card:ℝ)^2 := by
    calc
      _ ≤ (z.divisors.card:ℝ)^2 *
          ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G zp‖ :=
        mul_le_mul_of_nonneg_right hF (norm_nonneg _)
      _ ≤ (z.divisors.card:ℝ)^2 * (zp.divisors.card:ℝ)^2 :=
        mul_le_mul_of_nonneg_left hG hzN
  calc
    _ = ‖psi ((z:ℝ)/Z)‖ *
        (‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F z‖ *
        ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G zp‖) *
        (sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) z *
         sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) zp) := by ring
    _ ≤ ‖psi ((z:ℝ)/Z)‖ *
        ((z.divisors.card:ℝ)^2 * (zp.divisors.card:ℝ)^2) *
        (sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) z *
         sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) zp) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcore hpsi) (mul_nonneg hWz hWp)
    _ = _ := by dsimp only [zp];ring
end Green64Analytic.Parity

end

end

/-! ## OriginalEq417BetaCoreBounds -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Actual original Parity (4.16) first/nonconjugated F and second G,
for the genuine b629 fine alpha and full B509 residual, EACH obey a
source-verified tau(n)^2 bound at the COMPLETE physical integer n.
Uses B656 physical arithmetic and the genuine F/E conjugation, with
D=1 only AFTER B656 and no weakened abstract core-size premise. -/
theorem parity_eventually_original_eq417_actual_two_core_tau2_bounds434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (prime : Bool) (lFine uFine : ℕ), Real.exp (beta*L)≤(lFine:ℝ) →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q)
        (xi1 xi2 rho sigma : ℝ) (n : ℕ),
      0<n → (n:ℝ)≤Real.exp (2*L) →
      let F := sourceNativePrimeCore 20 d L band slot delta freq K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine) q chi 0 0
      ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L)
         (b633ParityFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma) n‖ ≤
        (n.divisors.card:ℝ)^2 ∧
      ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L)
         (b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma) n‖ ≤
        (n.divisors.card:ℝ)^2 := by
  filter_upwards [b656_actual_parity_arithmetic_bounds434 S beta gamma hS hbeta hgamma]
    with L hActual
  intro prime lFine uFine hFineLow d band slot delta freq K q chi xi1 xi2 rho sigma n hn hN
  let F := sourceNativePrimeCore 20 d L band slot delta freq K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine) q chi 0 0
  have hSrc := hActual prime lFine uFine hFineLow 20 d (by omega)
    band slot delta freq K q chi 0 0 xi1 xi2 rho sigma
    (sourceOriginalPAllActualBands 20 L) n hn hN
  have hUnit : ∀ p : ℕ, p ∈ (1:ℕ).primeFactors →
      p ∈ Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L) := by
    intro p hp
    simp at hp
  have hBound := hSrc.2.2 1 (by decide) (one_dvd _) hUnit
  have hConj := b633_parity_E_first_literal_conjugate434
    (sourceOriginalPAllActualBands 20 L) F.alpha F.residual q chi
    F.lo F.hi xi2 rho sigma n
  have hNorm := congrArg (fun a : ℂ => ‖a‖) hConj
  rw [norm_star] at hNorm
  dsimp only
  constructor
  · rw [←hNorm]
    simpa only [Nat.div_one] using hBound.1
  · simpa only [Nat.div_one] using hBound.2
end Green64Analytic.Parity

end

end

