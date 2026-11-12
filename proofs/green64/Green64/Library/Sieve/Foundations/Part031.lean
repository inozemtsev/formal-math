module

public import Green64.Library.Sieve.Foundations.Part030
public import Green64.Library.Sieve.Foundations.Part028
public import Green64.Library.Sieve.Foundations.Part027
public import Green64.Library.Sieve.Foundations.Part029
public import Green64.Library.Sieve.Foundations.Part017
public import Green64.Library.Sieve.Foundations.Part018
public import Green64.Library.Weights.Part113
public import Green64.Library.Sieve.Foundations.Part024
public import Green64.Library.Sieve.Foundations.Part021
public import Green64.Library.Weights.Part033
public import Green64.Library.Sieve.Foundations.Part007
public import Green64.Library.Sieve.Foundations.Part026

@[expose] public section

/-!
# Sieve / Foundations / Part031

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalUngatedGlobalTailPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 29000000

/-- **FULL TRUE UNGATED SOURCE Parity4.15-4.16 GLOBAL Fourier TAIL**
for all original full-odd e,m, nonzero signed k, χ and genuine
physical binary Z with nonzero η_eη_n source weight, including e
with original P-group prime factors, the literal B633 FULL vs BALL
complex norm is bounded by
 [C_H L^[5(K0+90)(H+P+1)] / T^H]
 × [2ceil(L^(K0+89))+1]
 × [Acoef² exp L L^(2CW1+256)].

The three factors come from independently Lean-proven original
moving-η 3D Schwartz source moment, true nonzero k cofactor graph
degree (no #K/χ/Z), and original genuine NATURAL UNGATED H0
positive diagonal shifted τ moment. This is NOT the old gated
source bound and uses no spectral Parity4.17 estimate. -/
theorem parity_eventually_original_ungated_full_odd_global_B633_fourier_tail_polylog434
    (K0 : ℝ) (hK0 : 0≤K0) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
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
      0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
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
        K α signed ⌊2*Real.exp L⌋₊
        buf (-Real.log A) (Real.log A) hSmooth hSupport -
       parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed ⌊2*Real.exp L⌋₊
        buf (-Real.log A) (Real.log A) hSmooth hSupport T‖ ≤
      Q * (degree * (Acoef^2*Real.exp L*
        L^(2*parityOriginalW1PolylogExponent434+256))) := by
  filter_upwards [parity_eventually_original_ungated_full_odd_filtered_tail_le_coefficient_mass434
      K0 hK0,
    parity_eventually_original_historical_ungated_extended_diagonal_polylog434] with
      L hFour hDiag
  refine ⟨hFour.1,hFour.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed Acoef hAcoef hAlpha
    hU hV hUV hScale hDyad A R hA hR buf hSmooth hSupport hOne hCube
    H hLargeE hLargeN T hT
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
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
  have hFourMass := hFour.2.2 hLw band slot δ ξ rho U V E K α signed
    hU hV hUV hScale hDyad A R hA hR buf hSmooth hSupport hOne hCube
    H hLargeE hLargeN T hT
  have hMass : M≤degree*D :=
    parity_original_historical_ungated_full_odd_filtered_coefficient_mass_le_diagonal434
      d L U E V K0 hLw band slot δ ξ rho α signed Y K hU hScale hDyad
  have hDiagActual : D≤X := hDiag.2 band slot δ ξ rho K
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

/-! ## OriginalHistoricalUngatedGlobalTailAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 30000000

/-- **UNCONDITIONAL CORRECTED original Parity(4.15-4.16) GLOBAL
high-frequency Fourier tail** of ARBITRARY inverse-log accuracy
for the TRUE natural UNGATED full odd-e H0/B509 source with e
possibly divisible by original group P primes:
for each chosen D≥0 one polynomial T=L^[5(K0+90)(P+2)+
(K0+89)+(2CW1+256)+D] gives
  ||full corrected ungated B633 R³ Fourier - source-filtered
      true low-frequency B633 Fourier BALL(T)||
   ≤ 4*C1*Acoef²*exp(L)*L^(-D),
with one fixed verified original source C∞ H=1 Fourier moment
C1 independent of physical e,m,k,χ,Z,L and D. Proved native from
actual corrected B509 real physical coefficient mass, original
uniform Schwartz B_H, true η_eη_n nonzero-Z before truncation,
original character mask l1≤1 and symmetric polynomial k graph
without #e,#m,#chi,#Z factor. No Parity4.17 spectral saving assumed. -/
theorem parity_original_historical_ungated_full_odd_global_tail_power_numeric434
    (L K0 X M D C Acoef : ℝ)
    (hL : 8≤L) (hK0 : 0≤K0) (hC : 0≤C) :
    (C*L^X/L^((X+(K0+89)+M)+D)) *
      (((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ) *
        (Acoef^2*Real.exp L*L^M)) ≤
    4*C*Acoef^2*Real.exp L*L^(-D) := by
  have hLp : 0<L := by linarith
  have hDeg := parity_original_full_odd_actual_degree_le_four_power434 L K0 hL hK0
  have hPos := show 0≤C*L^X/L^((X+(K0+89)+M)+D) by positivity
  have hMass : 0≤Acoef^2*Real.exp L*L^M := by positivity
  have hBound :
      (((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ) *
        (Acoef^2*Real.exp L*L^M)) ≤
      (4*L^(K0+89)) * (Acoef^2*Real.exp L*L^M) :=
    mul_le_mul_of_nonneg_right hDeg hMass
  have hRatio := parity_original_three_source_power_cutoff_ratio434
    L X (K0+89) M D hLp
  calc
    _ ≤ (C*L^X/L^((X+(K0+89)+M)+D)) *
        ((4*L^(K0+89)) * (Acoef^2*Real.exp L*L^M)) :=
      mul_le_mul_of_nonneg_left hBound hPos
    _ = 4*C*Acoef^2*Real.exp L *
        (L^X*L^(K0+89)*L^M/L^((X+(K0+89)+M)+D)) := by ring
    _ = _ := by rw [hRatio]

/-- COMPLETE ORIGINAL Parity (4.15)--(4.16) high-frequency Fourier
TAIL OF ARBITRARY INVERSE-LOGARITHMIC ORDER, after summing ALL
source full-odd e,n,m, signed k, Dirichlet χ and genuine binary Z:

For EVERY requested D≥0, one globally fixed polynomial frequency
radius
  T=L^([5(K0+90)(P+2)] + [K0+89] + [2*C_W1+256] + D)
leaves error
  ||FULL h=-2 B633 physical 3D Fourier outer
      - SAME genuine source physically-filtered BALL||
    ≤ 4*C_1*Acoef²*exp(L)*L^(-D).

C_1 is the proved fixed original C∞ Euclidean 3D Schwartz moment
constant for H=1 and the SINGLE fixed real log buffer; independent
of physical L,k,Z,χ,e,n and requested D. The large-L threshold
is likewise independent of D. All original r0=20/Q/P/B509,
signed epsilon=1/E, b629 fine-cofactor and Ω multiplicities
survive without any guessed e,chi,Z cardinality bound.

PROOF: native uniform original η_eη_n 3D derivative budget;
original actual source per k/Z/χ Fourier error ≤ true χ ℓ1
physical source coefficient mass × C_1 L^X/T; exact nonzero-η
cell filtering BEFORE truncation; χ mask mass ≤1; exact physical
finite e,n,m,k,Z reindex; original bounded-k neighbor graph degree
≤2ceil(L^(K0+89))+1; original unconditional diagonal
Acoef² expL L^(2*C_W1+256); and elementary exact frequency powers.

This proves GLOBAL high-frequency tail saving only. The truncated
LOW-FREQUENCY B633/Parity(4.17) signed two-prime-slot correlation
still needs a new support-sensitive saving. Therefore Parity Type II
(4.2), final sieve and Green64.green_64 remain OPEN. -/
theorem parity_eventually_original_ungated_full_odd_global_B633_fourier_tail_any_log434
    (K0 : ℝ) (hK0 : 0≤K0)
    (A R : ℝ) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
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
      0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
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
        K α signed ⌊2*Real.exp L⌋₊
        buf (-Real.log A) (Real.log A) hSmooth hSupport -
       parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed ⌊2*Real.exp L⌋₊
        buf (-Real.log A) (Real.log A) hSmooth hSupport T‖ ≤
      4*C1*Acoef^2*Real.exp L*L^(-D) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let J : ℕ := 1+P
  let Bfixed : ℝ := max
    (2*A*(J.factorial:ℝ))
    (8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+(J.factorial:ℝ)*A)
  filter_upwards [parity_eventually_original_ungated_full_odd_global_B633_fourier_tail_polylog434
      K0 hK0, eventually_ge_atTop Bfixed] with L hGlobal hLarge
  refine ⟨hGlobal.1,hGlobal.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed Acoef hAcoef hAlpha
    hU hV hUV hScale hDyad D hD
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
  have hTail := hGlobal.2.2 hLw band slot δ ξ rho U V E K α signed Acoef
    hAcoef hAlpha hU hV hUV hScale hDyad
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

/-! ## OriginalHistoricalUngatedLowFrequencyReduction -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 30000000

/-- **CORRECTED ORIGINAL Parity (4.10)--(4.16) END-TO-END
LOW-FREQUENCY TYPEII REDUCTION** with actual source Q-selected
Cauchy a_e beta_n L², positive genuine full all-odd-e NATURAL
UNGATED a_v(u/e) B509/H0 shifted-divisor diagonal, and exactly
ONE literal B633/Parity4.16 two-prime-slot source-filtered
LOW-FREQUENCY Euclidean R³ Fourier ball correlation.

For every required D≥0, with one polynomial frequency radius
T=L^[5(K0+90)(P+2)+(K0+89)+2CW1+256+D], original source:

 ||A_selected_Q||² ≤ [Σ_original |a_e beta_n|²] × [
   2*Acoef² expL L^(2CW1+344)
   + ||B633_TRUE_UNGATED_LOWFREQ_BALL(T)||
   + 4*C1*Acoef² expL L^(-D) ].

The global high-frequency error is native PROVED for the NEW
un-gated full-odd source from real physical η_eη_n k/Z events,
not falsely inherited from the old P-free-e-gated branch. The
original H0 B509, W1, epsilon 1/E, fine b629 alpha, chi and
full P-factor multiplicities are preserved. No full Parity4.17
LOW-FREQUENCY spectral cancellation or TypeII(4.2) saving is
assumed or asserted; Parity(4.17) is the remaining analytic barrier. -/
theorem parity_eventually_original_ungated_full_odd_low_frequency_typeII_reduction434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) (hK0 : 0≤K0)
    (A R : ℝ) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
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
      0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
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
      ‖parityOriginalHistoricalCauchyAtDelta434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J alpha β signed ⌊2*Real.exp L⌋₊‖^2 ≤
      Amass * (2*Acoef^2*Real.exp L*
        L^(2*parityOriginalW1PolylogExponent434+344) +
        ‖parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
          (sourceOriginalLiteralDepth 20 L) L U E V hLw
          band slot δ ξ rho K alpha signed ⌊2*Real.exp L⌋₊
          buf (-Real.log A) (Real.log A) hSmooth hSupport T‖ +
        4*C1*Acoef^2*Real.exp L*L^(-D)) := by
  filter_upwards [parity_eventually_original_ungated_full_odd_Cauchy_diag_B633_fourier434
    S beta gamma K0 hS hbeta hgamma A buf hSmooth hSupport hOne,
    parity_eventually_original_ungated_full_odd_global_B633_fourier_tail_any_log434
      K0 hK0 A R hA hR buf hSmooth hSupport hOne hCube] with
    L hParent hTail
  refine ⟨hParent.1,hParent.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K J betaSeq prime signed
    lFine uFine Acoef hAcoef hAlpha hU hV hUV hScale hDyad hNRange
    hl hFineLow D hD
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
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
    hU hV hScale hDyad hNRange hl hFineLow hAcoef hAlpha
  have hTail' := hTail.2.2 hLw band slot δ ξ rho U V E K alpha signed Acoef
    hAcoef hAlpha hU hV hUV hScale hDyad D hD
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
      ‖parityOriginalHistoricalCauchyAtDelta434
        d L E band slot δ ξ rho K J alpha betaSeq signed Y‖^2 ≤
      Amass*(B+‖Full‖) := hParent'
  calc
    _ ≤ Amass*(B+‖Full‖) := hParentBound
    _ ≤ Amass*(B+(‖Ball‖+Err)) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl B) hFourBound) hMassNonneg
    _ = Amass*(B+‖Ball‖+Err) := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqH0ExactSupport -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The ACTUAL original Parity(4.8) reserved H0 prime product carrier
is EXACTLY the true B509 Cartesian vStar support used by the natural
ungated all-odd e Cauchy source. Each prime p is from the original
FULL reserved Q band and each r from the full ordered skipped Q
product support; no arbitrary positive vStar or invented factors.
This is an exact finite equality of carriers, not a support-size
upper bound or a signed analytic cancellation statement. -/
theorem parity_original_historical_H0_support_eq_reserved_VStar434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) :
    parityOriginalReservedHSupport434 d L band slot δ =
    parityOriginalReservedCartesianVStarSupport434 d L band slot δ := by
  let P := sourceOriginalQActualBands 20 d L band
  let S := paritySourceB509SkipEndpointSupport434
    (Q := sourceActualSortedQ 20 d L band slot) δ
  ext t
  constructor
  · intro ht
    unfold parityOriginalReservedHSupport434
      parityOriginalReservedHCarrier434 at ht
    obtain ⟨⟨p,r⟩,hpr,hEq⟩ := Finset.mem_image.mp ht
    have hp := (Finset.mem_product.mp hpr).1
    have hr := (Finset.mem_product.mp hpr).2
    obtain ⟨skip,hSkip,hR⟩ := Finset.mem_image.mp hr
    unfold parityOriginalReservedCartesianVStarSupport434
    apply Finset.mem_image.mpr
    refine ⟨(⟨p,hp⟩,skip),Finset.mem_univ _,?_⟩
    dsimp only
    calc
      p * orderedSkipProduct skip = p*r := by rw [hR]
      _ = t := hEq
  · intro ht
    unfold parityOriginalReservedCartesianVStarSupport434 at ht
    obtain ⟨⟨p,skip⟩,hps,hEq⟩ := Finset.mem_image.mp ht
    unfold parityOriginalReservedHSupport434 parityOriginalReservedHCarrier434
    apply Finset.mem_image.mpr
    refine ⟨(p.val,orderedSkipProduct skip),?_,?_⟩
    · apply Finset.mem_product.mpr
      constructor
      · exact p.property
      · exact Finset.mem_image.mpr ⟨skip,Finset.mem_univ _,rfl⟩
    · exact hEq

/-- The true original B509 H0 source convolution literally vanishes
outside the Cartesian reserved Q prime-slot support, at EVERY real
power/fine allocation frequency and arbitrary complex coefficients.
This is a pointwise statement on H0 itself, not a fake restriction
of a complex signed full Parity(4.17) correlation. -/
theorem parity_original_historical_intrinsic_H0_zero_outside_VStar434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (sigma : ℝ) (t : ℕ)
    (hOutside : t ∉ parityOriginalReservedCartesianVStarSupport434
      d L band slot δ) :
    parityOriginalIntrinsicH434 d L band slot δ ξ sigma t = 0 := by
  let P := sourceOriginalQActualBands 20 d L band
  let S := paritySourceB509SkipEndpointSupport434
    (Q := sourceActualSortedQ 20 d L band slot) δ
  have hNo : ∀p∈P, ∀r∈S, p*r≠t := by
    intro p hp r hr heq
    apply hOutside
    rw [←parity_original_historical_H0_support_eq_reserved_VStar434]
    unfold parityOriginalReservedHSupport434 parityOriginalReservedHCarrier434
    exact Finset.mem_image.mpr
      ⟨(p,r),Finset.mem_product.mpr ⟨hp,hr⟩,heq⟩
  unfold parityOriginalIntrinsicH434 sourceEndpointFibre
  apply Finset.sum_eq_zero
  intro a ha
  have hPr := (Finset.mem_product.mp (Finset.mem_filter.mp ha).1)
  have hEq : a.1*a.2=t := (Finset.mem_filter.mp ha).2
  exact (hNo a.1 hPr.1 a.2 hPr.2 hEq).elim
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqB633Support -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- The ORIGINAL frozen B509 skipped-prime residual c_r vanishes
exactly when r is not a product of actually skipped labelled Q
primes. All multiplicities, factorials and Fourier phases are kept;
the residual is a genuine sourceEndpointFibre, not arbitrary data. -/
theorem parity_original_historical_intrinsic_residual_zero_outside_skip434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (r : ℕ)
    (hOutside : r ∉ paritySourceB509SkipEndpointSupport434
      (Q := sourceActualSortedQ 20 d L band slot) δ) :
    parityOriginalIntrinsicResidual434 d L band slot δ ξ r=0 := by
  unfold parityOriginalIntrinsicResidual434 sourceEndpointFibre
  apply Finset.sum_eq_zero
  intro a ha
  have heq : orderedSkipProduct a = r := (Finset.mem_filter.mp ha).2
  have hImage : r ∈ paritySourceB509SkipEndpointSupport434
      (Q := sourceActualSortedQ 20 d L band slot) δ := by
    unfold paritySourceB509SkipEndpointSupport434
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,heq⟩
  exact (hOutside hImage).elim

/-- Every positive integer t with NONZERO original source B633
reserved-prime/skip-prime convolution is in the exact ORIGINAL
B509 H0 carrier. Equivalently, for positive t outside the B509
prime-slot set, b633PrimeRest434(F.lo,F.hi,0,F.residual,t)=0.

This closes the first missing *low-frequency support* implication
for the literal unrestricted Parity(4.17) two-prime-slot B633 core.
The prime interval is precisely sourceOriginalQActualBands via
native `parity_native_core_prime_slot434`; the residual is precisely
original intrinsic frozen B509 c_r. The result has NO e Pfree
assumption, no signed-subset dominance, no spectral saving.

The remaining source mismatch concerns the reconstructed shared n,
actual u/n finite windows, smooth psi_Z cutoff and full signed
outer-sum equality, not H0 prime-slot support. -/
theorem parity_original_historical_B633_prime_rest_zero_outside_H0_carrier434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (t : ℕ) (ht : 0<t)
    (hOutside : t ∉ parityOriginalReservedCartesianVStarSupport434
      d L band slot δ) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
    b633PrimeRest434 F.lo F.hi 0 F.residual t=0 := by
  dsimp only
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
  have hBand := parity_native_core_prime_slot434
    20 d L band slot δ ξ K alpha q chi 0 0
  dsimp only at hBand
  have hResidual (r : ℕ)
      (hR : r ∉ paritySourceB509SkipEndpointSupport434
        (Q := sourceActualSortedQ 20 d L band slot) δ) :
      F.residual r=0 := by
    rw [parity_original_native_B509_residual_is_intrinsic434]
    exact parity_original_historical_intrinsic_residual_zero_outside_skip434
      d L band slot δ ξ r hR
  unfold b633PrimeRest434
  apply Finset.sum_eq_zero
  intro p hp
  change (if p.Prime ∧ p∈Finset.Icc F.lo F.hi then
    imaginaryPower p 0 * F.residual (t/p) else 0)=0
  by_cases hPrime : p.Prime ∧ p∈Finset.Icc F.lo F.hi
  · have hpBand : p∈sourceOriginalQActualBands 20 d L band := by
      rw [←hBand]
      exact Finset.mem_filter.mpr ⟨hPrime.2,hPrime.1⟩
    have hRNot : t/p ∉ paritySourceB509SkipEndpointSupport434
        (Q := sourceActualSortedQ 20 d L band slot) δ := by
      intro hRMem
      have hDiv : p∣t := (Nat.mem_divisors.mp hp).1
      have htEq : p*(t/p)=t := Nat.mul_div_cancel_left' hDiv
      apply hOutside
      rw [←parity_original_historical_H0_support_eq_reserved_VStar434]
      unfold parityOriginalReservedHSupport434 parityOriginalReservedHCarrier434
      exact Finset.mem_image.mpr
        ⟨(p,t/p),Finset.mem_product.mpr ⟨hpBand,hRMem⟩,htEq⟩
    simp only [if_pos hPrime,hResidual (t/p) hRNot,mul_zero]
  · simp only [if_neg hPrime]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqH0AsPrimeRest -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 30000000

/-- Finite exact original reserved-prime fibre: for p>0,
  sum_{r in original B509 skip support, p*r=t} c_r
is exactly c_(t/p) when p divides t, zero otherwise. This keeps
all B509 factorial and Fourier collision coefficients; no mass
majorant or assumed positivity is used. -/
theorem parity_original_historical_one_reserved_prime_fibre434
    (S : Finset ℕ) (f : ℕ → ℂ) (p t : ℕ) (hp : 0<p)
    (hSupp : ∀r, r∉S → f r=0) :
    (∑r∈S, if p*r=t then f r else 0) =
    if p∣t then f (t/p) else 0 := by
  by_cases hDiv : p∣t
  · have hprod : p*(t/p)=t := Nat.mul_div_cancel_left' hDiv
    have hIff (r : ℕ) : p*r=t ↔ r=t/p := by
      constructor
      · intro h
        exact Nat.mul_left_cancel hp (by rw [h,hprod])
      · intro h
        rw [h,hprod]
    calc
      _ = ∑r∈S, if r=t/p then f r else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        by_cases hEq : r=t/p
        · have hMul := (hIff r).mpr hEq
          simp [hEq,hprod]
        · have hMul : ¬p*r=t := fun hh => hEq ((hIff r).mp hh)
          simp [hEq,hMul]
      _ = if t/p∈S then f (t/p) else 0 := Finset.sum_ite_eq' S (t/p) f
      _ = if p∣t then f (t/p) else 0 := by
        by_cases hIn : t/p∈S
        · simp [hIn,hDiv]
        · simp [hIn,hDiv,hSupp (t/p) hIn]
  · have hNo (r : ℕ) : ¬p*r=t := by
      intro h
      apply hDiv
      exact ⟨r,h.symm⟩
    simp only [if_neg hDiv]
    apply Finset.sum_eq_zero
    intro r hr
    simp only [if_neg (hNo r)]

/-- The ORIGINAL intrinsic H0 reserved-prime convolution is the
literal divisor-fibre over the native original Q band, at sigma=0.
The skipped prime residual F.residual has its full original B509
factorials, all repeated prime multiplicities, and exact finite
source support. No e-window or Pfree gate is imposed. -/
theorem parity_original_historical_intrinsic_H0_as_reserved_prime_sum434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (t : ℕ) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
    parityOriginalIntrinsicH434 d L band slot δ ξ 0 t =
      ∑p∈sourceOriginalQActualBands 20 d L band,
        if p∣t then F.residual (t/p) else 0 := by
  dsimp only
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
  let S := paritySourceB509SkipEndpointSupport434
    (Q := sourceActualSortedQ 20 d L band slot) δ
  have hSupp (r : ℕ) (hr : r∉S) : F.residual r=0 := by
    rw [parity_original_native_B509_residual_is_intrinsic434]
    exact parity_original_historical_intrinsic_residual_zero_outside_skip434
      d L band slot δ ξ r hr
  have hBand := parity_native_core_prime_slot434
    20 d L band slot δ ξ K alpha q chi 0 0
  dsimp only at hBand
  have hH : parityOriginalIntrinsicH434 d L band slot δ ξ 0 t =
      parityOriginalReservedH434 d L band slot δ ξ K alpha q chi 0 0 0 t := by
    exact (parity_original_reserved_H_is_intrinsic434
      d L band slot δ ξ K alpha q chi 0 0 0 t).symm
  rw [hH,parity_original_reserved_H_literal_prime_convolution434]
  apply Finset.sum_congr rfl
  intro p hp
  have hpPrime : p.Prime := by
    have hpQ := hBand.symm ▸ hp
    exact (Finset.mem_filter.mp hpQ).2
  have hpPos : 0<p := hpPrime.pos
  have hPhase : sourceOriginalPureMellinPhase434 0 p=1 := by
    unfold sourceOriginalPureMellinPhase434
    simp
  simp only [hPhase,one_mul]
  exact parity_original_historical_one_reserved_prime_fibre434
    S F.residual p t hpPos hSupp

/-- Strong original SOURCE support IDENTIFICATION: for every
positive t, the full unrestricted B633 reserved prime-slot
convolution equals the original natural B509 H0 coefficient,
not merely has the same support. This is the precise original
Eq(4.16) coefficient identification required before using the
unrestricted signed Parity Eq(4.17) saving. No missing prime-slot
factorials, custom residual or Pfree-e source gate. -/
theorem parity_original_historical_intrinsic_H0_eq_literal_B633_prime_rest434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (t : ℕ) (ht : 0<t) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
    parityOriginalIntrinsicH434 d L band slot δ ξ 0 t =
      b633PrimeRest434 F.lo F.hi 0 F.residual t := by
  dsimp only
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
  have hBand := parity_native_core_prime_slot434
    20 d L band slot δ ξ K alpha q chi 0 0
  dsimp only at hBand
  have hSet : (t.divisors.filter (fun p => p.Prime ∧ p∈Finset.Icc F.lo F.hi)) =
      (sourceOriginalQActualBands 20 d L band).filter (fun p => p∣t) := by
    ext p
    constructor
    · intro hp
      have hh := Finset.mem_filter.mp hp
      have hQ : p∈sourceOriginalQActualBands 20 d L band := by
        rw [←hBand]
        exact Finset.mem_filter.mpr ⟨hh.2.2,hh.2.1⟩
      exact Finset.mem_filter.mpr ⟨hQ,(Nat.mem_divisors.mp hh.1).1⟩
    · intro hp
      have hh := Finset.mem_filter.mp hp
      have hPQ := hBand.symm ▸ hh.1
      have hPQ' := Finset.mem_filter.mp hPQ
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hh.2,ht.ne'⟩,⟨hPQ'.2,hPQ'.1⟩⟩
  have hH := parity_original_historical_intrinsic_H0_as_reserved_prime_sum434
    d L band slot δ ξ K alpha q chi t
  dsimp only at hH
  rw [hH]
  unfold b633PrimeRest434
  calc
    (∑p∈sourceOriginalQActualBands 20 d L band,
        if p∣t then F.residual (t/p) else 0) =
        ∑p∈(sourceOriginalQActualBands 20 d L band).filter (fun p=>p∣t),
          F.residual (t/p) := by rw [Finset.sum_filter]
    _ = ∑p∈t.divisors.filter (fun p=>p.Prime ∧ p∈Finset.Icc F.lo F.hi),
          F.residual (t/p) := by rw [hSet]
    _ = ∑p∈t.divisors.filter (fun p=>p.Prime ∧ p∈Finset.Icc F.lo F.hi),
          imaginaryPower p 0 * F.residual (t/p) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hPow : imaginaryPower p 0 = 1 := by
              unfold imaginaryPower
              simp
            rw [hPow,one_mul]
    _ = ∑p∈t.divisors,
          if p.Prime ∧ p∈Finset.Icc F.lo F.hi then
            imaginaryPower p 0 * F.residual (t/p) else 0 := by
              rw [Finset.sum_filter]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqTwoCoreH0Support -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The FULL original Parity(4.16) B633 prime-slot convolution,
when evaluated at the ACTUAL P-ordinary part of ANY positive
physical v, equals the genuine original H0(ordinary_P(v))
with all B509 residuals and normalization. This is not a one-way
physical source term identification: it is an identity for every
v>0 before introducing e,n,z or their finite SOURCE windows. -/
theorem parity_original_historical_positive_v_B633_eq_intrinsic_H0434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (v : ℕ) (hv : 0<v) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
    let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
    b633PrimeRest434 F.lo F.hi 0 F.residual (sourceOriginalOrdinaryPart P v) =
      parityOriginalIntrinsicH434 d L band slot δ ξ 0 (sourceOriginalOrdinaryPart P v) := by
  dsimp only
  have hPos : 0<sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) v :=
    Nat.pos_of_ne_zero (parity_original_ordinary_part_nonzero434 _ v hv.ne')
  exact (parity_original_historical_intrinsic_H0_eq_literal_B633_prime_rest434
    d L band slot δ ξ K alpha q chi _ hPos).symm

/-- A TRUE original Parity(4.16) physical B633 two-core summand
vanishes IDENTICALLY when its first positive endpoint v=z/mp has
ordinary_P(v) outside the ACTUAL B509 reserved prime×skipped-Q
support. This holds for ANY source e (including Pbad e) and
arbitrary k,z,m,m', without assuming the source-coupled n windows.
The complex product, χ twists, imaginary powers, and signs are
preserved until the exact H0 factor vanishes; no subset dominance. -/
theorem parity_original_historical_B633_pair_zero_first_H0_outside434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (rho xi1 xi2 xi3 : ℝ) (signed : Bool)
    (m mp z zp : ℕ) (hv : 0<z/mp)
    (hOutside : sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (z/mp)
      ∉ parityOriginalReservedCartesianVStarSupport434 d L band slot δ) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
    parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha F.residual q chi F.lo F.hi
      m mp z zp=0 := by
  dsimp only
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
  have hPos : 0<sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (z/mp) :=
    Nat.pos_of_ne_zero (parity_original_ordinary_part_nonzero434 _ (z/mp) hv.ne')
  have hZero := parity_original_historical_B633_prime_rest_zero_outside_H0_carrier434
    d L band slot δ ξ K alpha q chi _ hPos hOutside
  simp only [Finset.univ_eq_attach] at hZero
  simp [parityOriginalHistoricalB633PhysicalPairTerm434, Finset.univ_eq_attach, hZero]

/-- Same pointwise B633 H0-zero criterion for the SECOND
positive endpoint v'=(z+2k)/m. Thus a literal unrestricted
Parity(4.17) two-core pair can survive only if BOTH original
B509 reserved-prime×skipped-Q ordinary parts are actually in
the source-defined natural vStar carrier. This closes one part
of SOURCE-to-unrestricted signed-support equivalence, but does
NOT identify the remaining shared n/u constraints or psi_Z cutoffs. -/
theorem parity_original_historical_B633_pair_zero_second_H0_outside434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (rho xi1 xi2 xi3 : ℝ) (signed : Bool)
    (m mp z zp : ℕ) (hv : 0<zp/m)
    (hOutside : sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (zp/m)
      ∉ parityOriginalReservedCartesianVStarSupport434 d L band slot δ) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
    parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha F.residual q chi F.lo F.hi
      m mp z zp=0 := by
  dsimp only
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
  have hPos : 0<sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (zp/m) :=
    Nat.pos_of_ne_zero (parity_original_ordinary_part_nonzero434 _ (zp/m) hv.ne')
  have hZero := parity_original_historical_B633_prime_rest_zero_outside_H0_carrier434
    d L band slot δ ξ K alpha q chi _ hPos hOutside
  simp only [Finset.univ_eq_attach] at hZero
  simp [parityOriginalHistoricalB633PhysicalPairTerm434, Finset.univ_eq_attach, hZero]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqReverseWindowCarrier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 27000000

/-- A nonzero literal Parity4.16 B633 physical pair FORCES both
actual original reserved B509 H0 prime-slot supports. No e,n
SOURCE window or spectral saving is inferred from this. -/
theorem parity_original_historical_B633_pair_nonzero_requires_both_H0_slots434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (rho xi1 xi2 xi3 : ℝ) (signed : Bool)
    (m mp z zp : ℕ) (hv : 0 < z/mp) (hvp : 0 < zp/m)
    (hNonzero :
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0).residual
        q chi
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0).lo
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0).hi
        m mp z zp ≠ 0) :
    sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (z/mp) ∈
      parityOriginalReservedCartesianVStarSupport434 d L band slot δ ∧
    sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (zp/m) ∈
      parityOriginalReservedCartesianVStarSupport434 d L band slot δ := by
  constructor
  · by_contra hOutside
    exact hNonzero (parity_original_historical_B633_pair_zero_first_H0_outside434
      d L band slot δ ξ K alpha q chi rho xi1 xi2 xi3 signed m mp z zp hv hOutside)
  · by_contra hOutside
    exact hNonzero (parity_original_historical_B633_pair_zero_second_H0_outside434
      d L band slot δ ξ K alpha q chi rho xi1 xi2 xi3 signed m mp z zp hvp hOutside)

/-- EXACT CONDITIONAL REVERSE from a full original Parity4.17
ordinary-P divisor pair to the true new ungated physical B509
(m',n) k/Z cell. Given original integer determinant, rough
coprimality and shifted z pair, reverse arithmetic recovers ONE
shared n; PROVIDED its hard source n∈J and u,u'≤Y and genuine
H0 prime-slot conditions, this n is in the ACTUAL source carrier.
No hypothesis that e is P-prime-free. Remaining analytical gap:
the unrestricted signed Parity4.17 sum has NO such sharp source
windows after Fourier separation; no complex subset transfer. -/
theorem parity_original_historical_reverse_417_into_ungated_physical_k_z_window434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp z zp Z : ℕ) (k : ℤ) (K J : Finset ℕ)
    (he : 0 < e) (hm : 0 < m) (hmp : 0 < mp)
    (hz : 0 < z) (hzp : 0 < zp)
    (hMPK : mp∈K) (hNE : m≠mp)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hShift : (z:ℤ)+2*k=(zp:ℤ))
    (hCop : m.Coprime k.natAbs)
    (hDivMp : mp∣sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z)
    (hDivM : m∣sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp)
    (hU : e*(z/mp)≤Y) (hUP : e*(zp/m)≤Y)
    (hJ : ∀n : ℕ, m*n=e*(z/mp)+2 → mp*n=e*(zp/m)+2 → n∈J)
    (hVS : sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (z/mp)∈
      parityOriginalReservedCartesianVStarSupport434 d L band slot δ)
    (hVPS : sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (zp/m)∈
      parityOriginalReservedCartesianVStarSupport434 d L band slot δ)
    (hZ : parityOriginalHistoricalActualZDyadicScale434 z=Z) :
    ∃n : ℕ,
      (mp,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z ∧
      parityOriginalHistoricalCanonicalZ434 e m mp n=z ∧
      m*n=e*(z/mp)+2 ∧ mp*n=e*(zp/m)+2 := by
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  obtain ⟨v,vp,n,hv,hvp,hZEq,hZpEq,hMN,hMpN⟩ :=
    parity_original_historical_reverse_417_divisor_pair_to_source_n434
      P m mp e z zp k hm hmp hz hzp hDet hShift hCop hDivMp hDivM
  have hVeq : z/mp=v := by
    rw [hZEq]
    exact Nat.mul_div_cancel_left v hmp
  have hVPeq : zp/m=vp := by
    rw [hZpEq]
    exact Nat.mul_div_cancel_left vp hm
  have hN : 0 < n := by
    have hPositive : 0 < m*n := by
      rw [hMN]
      exact Nat.add_pos_left (Nat.mul_pos he hv) _
    exact Nat.pos_of_mul_pos_left hPositive
  have hNMem : n∈J := by
    apply hJ n
    · rw [hVeq]
      exact hMN
    · rw [hVPeq]
      exact hMpN
  have hUE : e*v∈parityOriginalHistoricalFixedMNUSupport434 Y m n := by
    unfold parityOriginalHistoricalFixedMNUSupport434
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Ioc.mpr
      constructor
      · exact Nat.mul_pos he hv
      · rw [←hVeq]
        exact hU
    · exact ⟨hm,hN,hMN⟩
  have hUPE : e*vp∈parityOriginalHistoricalFixedMNUSupport434 Y mp n := by
    unfold parityOriginalHistoricalFixedMNUSupport434
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Ioc.mpr
      constructor
      · exact Nat.mul_pos he hvp
      · rw [←hVPeq]
        exact hUP
    · exact ⟨hmp,hN,hMpN⟩
  have hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n := by
    refine ⟨e*v,hUE,e*vp,hUPE,?_,?_,?_,?_⟩
    · exact dvd_mul_right e v
    · exact dvd_mul_right e vp
    · rw [Nat.mul_div_cancel_left v he,←hVeq]
      exact hVS
    · rw [Nat.mul_div_cancel_left vp he,←hVPeq]
      exact hVPS
  have hK : parityOriginalHistoricalOffdiagK434 e m mp=k :=
    parity_original_historical_physical_k_eq_quotient434 e m mp he k hDet
  have hMpK : mp∈parityOriginalHistoricalKPrimeFibre434 e m K k := by
    unfold parityOriginalHistoricalKPrimeFibre434
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hNE.symm,hMPK⟩,hK⟩
  have hZCanonical : parityOriginalHistoricalCanonicalZ434 e m mp n=z := by
    have hUeq : m*n-2=e*v := by omega
    unfold parityOriginalHistoricalCanonicalZ434
      parityOriginalHistoricalCanonicalV434
    rw [hUeq,Nat.mul_div_cancel_left v he]
    exact hZEq.symm
  have hCPos : 0 < parityOriginalHistoricalCanonicalZ434 e m mp n := by
    rw [hZCanonical]
    exact hz
  have hZscale : parityOriginalHistoricalActualZDyadicScale434
      (parityOriginalHistoricalCanonicalZ434 e m mp n)=Z := by
    rw [hZCanonical]
    exact hZ
  have hEvent : (mp,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z := by
    unfold parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hMpK,hNMem⟩,
       ⟨hValid,hCPos,hZscale⟩⟩
  refine ⟨n,hEvent,hZCanonical,?_,?_⟩
  · rw [hVeq]
    exact hMN
  · rw [hVPeq]
    exact hMpN
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSmoothDyadicPsi -/

section

open Filter Topology MeasureTheory Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- A single FIXED real C-infinity bump, identically one on [-1,1]
and identically zero on R outside (-2,2). Its profile is independent
of original source L,e,n,k,Z and requested Fourier error order. -/
def parityOriginalHistoricalDyadicSmoothStep434 : ContDiffBump (0:ℝ) :=
  ⟨1,2,by norm_num,by norm_num⟩

/-- A FIXED positive-half-line guard, equal to one on [1,4]
and zero at every nonpositive t and all t≥5. -/
def parityOriginalHistoricalDyadicPositiveGuard434 : ContDiffBump (5/2:ℝ) :=
  ⟨2,5/2,by norm_num,by norm_num⟩

def parityOriginalHistoricalDyadicSmoothPsiReal434 (t : ℝ) : ℝ :=
  (parityOriginalHistoricalDyadicPositiveGuard434 t : ℝ) *
    ((parityOriginalHistoricalDyadicSmoothStep434 (t/2):ℝ) -
     (parityOriginalHistoricalDyadicSmoothStep434 t:ℝ))

def parityOriginalHistoricalDyadicSmoothPsi434 (t : ℝ) : ℂ :=
  (parityOriginalHistoricalDyadicSmoothPsiReal434 t:ℂ)

/-- Exact C-infinity smoothness of a single fixed positive dyadic
profile psi(t), with two *fixed* Mathlib ContDiffBump bases. -/
theorem parity_original_historical_dyadic_smooth_psi_contDiff434 :
    ContDiff ℝ ∞ parityOriginalHistoricalDyadicSmoothPsi434 := by
  have hHalf : ContDiff ℝ ∞ (fun t:ℝ => t/2) :=
    contDiff_id.div_const 2
  have hCore : ContDiff ℝ ∞ (fun t:ℝ =>
      (parityOriginalHistoricalDyadicSmoothStep434 (t/2):ℝ) -
      (parityOriginalHistoricalDyadicSmoothStep434 t:ℝ)) :=
    (parityOriginalHistoricalDyadicSmoothStep434.contDiff.comp hHalf).sub
      parityOriginalHistoricalDyadicSmoothStep434.contDiff
  have hReal : ContDiff ℝ ∞ parityOriginalHistoricalDyadicSmoothPsiReal434 :=
    parityOriginalHistoricalDyadicPositiveGuard434.contDiff.mul hCore
  exact Complex.ofRealCLM.contDiff.comp hReal

/-- The fixed step is exactly one on its closed inner ball. -/
theorem parity_original_historical_dyadic_step_one434
    (t : ℝ) (ht : |t|≤1) :
    (parityOriginalHistoricalDyadicSmoothStep434 t:ℝ)=1 := by
  have hBall : t∈Metric.closedBall (0:ℝ) 1 := by
    simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using ht
  exact parityOriginalHistoricalDyadicSmoothStep434.one_of_mem_closedBall hBall

/-- The same source step is exactly ZERO at every radius ≥2.
Neither a finite dyadic support nor an error estimate is assumed. -/
theorem parity_original_historical_dyadic_step_zero434
    (t : ℝ) (ht : 2≤|t|) :
    (parityOriginalHistoricalDyadicSmoothStep434 t:ℝ)=0 := by
  by_contra hn
  have hBall : t∈Metric.ball (0:ℝ)
      parityOriginalHistoricalDyadicSmoothStep434.rOut := by
    rw [←parityOriginalHistoricalDyadicSmoothStep434.support_eq]
    exact hn
  have hh : |t|<2 := by
    change t∈Metric.ball (0:ℝ) 2 at hBall
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hBall
  linarith

/-- Positive-half-line guard: one on the entire active real
source interval [1,4], so it does not alter the desired
unconditional dyadic telescoping identity on physical z>0. -/
theorem parity_original_historical_dyadic_guard_one434
    (t : ℝ) (ht : 1≤t ∧ t≤4) :
    (parityOriginalHistoricalDyadicPositiveGuard434 t:ℝ)=1 := by
  have hBall : t∈Metric.closedBall (5/2:ℝ) 2 := by
    rw [Metric.mem_closedBall,Real.dist_eq]
    apply abs_le.mpr
    constructor <;> linarith [ht.1,ht.2]
  exact parityOriginalHistoricalDyadicPositiveGuard434.one_of_mem_closedBall hBall

/-- The fixed guard is zero for t≤0, preventing a negative-z
artifact when using psi in the FULL unrestricted Parity(4.17) sum. -/
theorem parity_original_historical_dyadic_guard_zero_nonpos434
    (t : ℝ) (ht : t≤0) :
    (parityOriginalHistoricalDyadicPositiveGuard434 t:ℝ)=0 := by
  by_contra hn
  have hBall : t∈Metric.ball (5/2:ℝ)
      parityOriginalHistoricalDyadicPositiveGuard434.rOut := by
    rw [←parityOriginalHistoricalDyadicPositiveGuard434.support_eq]
    exact hn
  have hdist : |t-(5/2:ℝ)|<5/2 := by
    change t∈Metric.ball (5/2:ℝ) (5/2) at hBall
    simpa only [Metric.mem_ball,Real.dist_eq] using hBall
  have hh := (abs_lt.mp hdist).1
  linarith
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSmoothDyadicPartition -/

section

open Filter Topology MeasureTheory Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 27000000

/-- On every positive dyadic argument, the ACTUAL C-infinity
positive-half guard is redundant. Thus our fixed ψ is exactly
the telescoping difference b(t/2)-b(t) where b is a FIXED
C-infinity compact real cutoff, not a sharp binary indicator. -/
theorem parity_original_historical_dyadic_psi_telescope_at_pos434
    (t : ℝ) (ht : 0<t) :
    parityOriginalHistoricalDyadicSmoothPsiReal434 t =
      (parityOriginalHistoricalDyadicSmoothStep434 (t/2):ℝ) -
      (parityOriginalHistoricalDyadicSmoothStep434 t:ℝ) := by
  by_cases hLow : t≤1
  · have hOne := parity_original_historical_dyadic_step_one434 t (by
      rw [abs_of_pos ht]
      exact hLow)
    have hOneHalf := parity_original_historical_dyadic_step_one434 (t/2) (by
      rw [abs_of_pos (by positivity : 0<t/2)]
      linarith)
    unfold parityOriginalHistoricalDyadicSmoothPsiReal434
    rw [hOneHalf,hOne]
    ring
  by_cases hHigh : 4≤t
  · have hZero := parity_original_historical_dyadic_step_zero434 t (by
      rw [abs_of_pos ht]
      linarith)
    have hZeroHalf := parity_original_historical_dyadic_step_zero434 (t/2) (by
      rw [abs_of_pos (by positivity : 0<t/2)]
      linarith)
    unfold parityOriginalHistoricalDyadicSmoothPsiReal434
    rw [hZeroHalf,hZero]
    ring
  · have hMid : 1≤t ∧ t≤4 := by
      constructor <;> linarith
    have hOne := parity_original_historical_dyadic_guard_one434 t hMid
    unfold parityOriginalHistoricalDyadicSmoothPsiReal434
    rw [hOne,one_mul]

/-- The FIXED Parity(4.17)-ready original ψ(t) is C∞ and supported
STRICTLY inside the positive compact interval (1,4), hence
satisfies the stated 1/64≤t≤64 support bound of original (3.3).
The source input is NOT a nonsmooth binary Z indicator; the
profile is a concrete smooth compact bump DIFFERENCE. -/
theorem parity_original_historical_dyadic_psi_compact_positive_support434
    (t : ℝ) (hNZ : parityOriginalHistoricalDyadicSmoothPsi434 t≠0) :
    1<t ∧ t<4 := by
  have ht : 0<t := by
    by_contra hh
    have hZero := parity_original_historical_dyadic_guard_zero_nonpos434
      t (le_of_not_gt hh)
    unfold parityOriginalHistoricalDyadicSmoothPsi434
      parityOriginalHistoricalDyadicSmoothPsiReal434 at hNZ
    simp [hZero] at hNZ
  have hPos := parity_original_historical_dyadic_psi_telescope_at_pos434 t ht
  have hNotZero : parityOriginalHistoricalDyadicSmoothPsiReal434 t ≠ 0 := by
    intro hh
    exact hNZ (by simp [parityOriginalHistoricalDyadicSmoothPsi434,hh])
  constructor
  · by_contra hh
    have hLow : t≤1 := le_of_not_gt hh
    have hOne := parity_original_historical_dyadic_step_one434 t (by
      rw [abs_of_pos ht]; exact hLow)
    have hHalf := parity_original_historical_dyadic_step_one434 (t/2) (by
      rw [abs_of_pos (by positivity : 0<t/2)]; linarith)
    apply hNotZero
    rw [hPos,hHalf,hOne]
    ring
  · by_contra hh
    have hHigh : 4≤t := le_of_not_gt hh
    have hZero := parity_original_historical_dyadic_step_zero434 t (by
      rw [abs_of_pos ht]; linarith)
    have hHalf := parity_original_historical_dyadic_step_zero434 (t/2) (by
      rw [abs_of_pos (by positivity : 0<t/2)]; linarith)
    apply hNotZero
    rw [hPos,hHalf,hZero]
    ring

/-- EXACT source independent smooth dyadic telescope: for ANY
real z>0, sum_{j=0}^{N} ψ(z/2^j) equals b(z/2^{N+1})-b(z).
All dyadic pieces have the SAME C∞ profile ψ(t), support (1,4),
and the exact source split has NO binary-cell discontinuity or
extra multiplicity. No Parity4.17 cancellation input. -/
theorem parity_original_historical_fixed_smooth_dyadic_telescope434
    (z : ℝ) (hz : 0<z) (N : ℕ) :
    (∑j∈Finset.range (N+1),
      parityOriginalHistoricalDyadicSmoothPsiReal434 (z/(2:ℝ)^j)) =
      (parityOriginalHistoricalDyadicSmoothStep434 (z/(2:ℝ)^(N+1)):ℝ) -
      (parityOriginalHistoricalDyadicSmoothStep434 z:ℝ) := by
  let f : ℕ → ℝ := fun j =>
    (parityOriginalHistoricalDyadicSmoothStep434 (z/(2:ℝ)^j):ℝ)
  have hOne (j : ℕ) :
      parityOriginalHistoricalDyadicSmoothPsiReal434 (z/(2:ℝ)^j) =
      f (j+1)-f j := by
    have ht : 0<z/(2:ℝ)^j := div_pos hz (by positivity)
    rw [parity_original_historical_dyadic_psi_telescope_at_pos434 _ ht]
    have hs : (z/(2:ℝ)^j)/2=z/(2:ℝ)^(j+1) := by
      rw [pow_succ]
      ring
    rw [hs]
  calc
    _ = ∑j∈Finset.range (N+1), (f (j+1)-f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hOne j
    _ = f (N+1)-f 0 := Finset.sum_range_sub f (N+1)
    _ = _ := by simp [f]

/-- The ACTUAL fixed smooth dyadic ψ family is an EXACT
partition of unity over every source z∈[2,2^(N+1)] with finitely
many dyadic scales 2^j (0≤j≤N); no approximate/unspecified
partition, no hard binary Z cutoff. This is the concrete smooth
ψ_Z object required before the Parity(4.17) LOW-FREQUENCY estimate.
A separate proof is still needed to replace old native B633 sharp
physical Z-cells and n/u windows with this genuine smooth family. -/
theorem parity_original_historical_fixed_smooth_dyadic_partition_one434
    (z : ℝ) (N : ℕ) (hzLo : 2≤z)
    (hzHi : z≤(2:ℝ)^(N+1)) :
    (∑j∈Finset.range (N+1),
      parityOriginalHistoricalDyadicSmoothPsiReal434 (z/(2:ℝ)^j)) = 1 := by
  have hz : 0<z := by linarith
  rw [parity_original_historical_fixed_smooth_dyadic_telescope434 z hz N]
  have hStart : (parityOriginalHistoricalDyadicSmoothStep434 z:ℝ)=0 :=
    parity_original_historical_dyadic_step_zero434 z (by
      rw [abs_of_pos hz]; exact hzLo)
  have hEnd : (parityOriginalHistoricalDyadicSmoothStep434
      (z/(2:ℝ)^(N+1)):ℝ)=1 := by
    apply parity_original_historical_dyadic_step_one434
    have hPos : 0≤z/(2:ℝ)^(N+1) := by positivity
    rw [abs_of_nonneg hPos]
    exact (div_le_iff₀ (by positivity : 0<(2:ℝ)^(N+1))).mpr (by simpa using hzHi)
  rw [hStart,hEnd]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSmoothDyadicBudget -/

section

open Filter Topology MeasureTheory Real
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- The new EXPLICIT original Parity lowfrequency smooth dyadic
ψ profile has exactly the required support `1/64≤t≤64`,
with the stronger actual strict interval `1<t<4`. All
derivatives and support are SOURCE-constructed, not assumptions. -/
theorem parity_original_historical_dyadic_psi_Parity417_support434
    (t : ℝ) (ht : parityOriginalHistoricalDyadicSmoothPsi434 t≠0) :
    (1/64:ℝ)≤t ∧ t≤64 := by
  have h := parity_original_historical_dyadic_psi_compact_positive_support434 t ht
  constructor <;> linarith

/-- One FIXED nonnegative derivative profile K_j, chosen before
L,k,Z,frequency cutoff and target saving, certifies ALL original
logarithmic derivative bounds of `ψ(exp u)`: sourceLogDerivativeBudget
with Cpsi=0 for EVERY L (including L<1). This is proved
by constructing an ACTUAL 1D Schwartz map from the SOURCE-fixed
C∞ compact ψ, not by positing derivative inequalities as a theorem
hypothesis. The native seminorm `SchwartzMap.seminorm ℂ 0 j`
controls each `iteratedDeriv j`. -/
theorem parity_original_historical_fixed_smooth_dyadic_psi_log_budget434 :
    ∃ K : ℕ → ℝ, (∀j,0≤K j) ∧
      ∀L : ℝ, sourceLogDerivativeBudget 0 K L
        (fun u : ℝ => parityOriginalHistoricalDyadicSmoothPsi434 (Real.exp u)) := by
  let ψ := parityOriginalHistoricalDyadicSmoothPsi434
  have hSmooth : ContDiff ℝ ∞ ψ :=
    parity_original_historical_dyadic_smooth_psi_contDiff434
  have hSupport : ∀t:ℝ, ψ t≠0 → (1/(64:ℝ))≤t ∧ t≤64 :=
    parity_original_historical_dyadic_psi_Parity417_support434
  let f := sourcePlainLogProfileSchwartz434 (64:ℝ) ψ
    (by norm_num : (1:ℝ)≤64) hSmooth hSupport
  let K : ℕ → ℝ := fun j => SchwartzMap.seminorm ℂ 0 j f
  refine ⟨K,(fun j=>apply_nonneg _ _),?_⟩
  intro L j u
  change ‖iteratedDeriv j (f : ℝ → ℂ) u‖ ≤
    K j*L^(0*((j : ℝ)+1))
  simpa only [K,pow_zero,one_mul,zero_mul,Real.rpow_zero,mul_one] using
    (SchwartzMap.le_seminorm' ℂ 0 j f u)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqExplicitPsiEq417Saving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- REAL, UNCONDITIONAL original Parity(4.17) CORE correlation
saving for EVERY positive inverse-log target, at the ONE
CONSTRUCTED fixed smooth dyadic profile ψ, with explicit
compact support (1,4) and proven C∞ logarithmic derivative
Schwartz seminorm budget Cpsi=0. No hypothetical ψ and no
analytic axiom are passed into the original 4.17 saving.
This is the FULL unrestricted original prime-slot correlation,
NOT the physically source-window-filtered old sharp Z-cell sum;
the latter equality is still OPEN. -/
theorem parity_eventually_original_Parity417_explicit_smooth_dyadic_psi_saving434
    (jQ : ℕ) (target Cfreq CZ Ck beta gamma : ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
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
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool),
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Fparity := b633ParityFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        let original := parityOriginalEq417WithFirstCore434 L rho xi3 Z k
          (Finset.Icc 1 ⌊64*Z⌋₊) Fparity Gcore tw parityOriginalHistoricalDyadicSmoothPsi434
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨Kpsi,hKpsi,hPsiBudget⟩ :=
    parity_original_historical_fixed_smooth_dyadic_psi_log_budget434
  obtain ⟨J,B,S,hSB,hSaving⟩ :=
    parity_eventually_B633_original_Parity417_direct_saving434
      jQ target Cfreq CZ Ck 0 beta gamma Kpsi hTarget hCZ hCk
      (by norm_num) hKpsi hbeta hgamma
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hSaving] with L hSavingL
  refine ⟨hSavingL.1,hSavingL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw
  dsimp only
  exact hSavingL.2.2 hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw
    parityOriginalHistoricalDyadicSmoothPsi434
    parity_original_historical_dyadic_smooth_psi_contDiff434
    parity_original_historical_dyadic_psi_Parity417_support434
    (hPsiBudget L)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSmoothDyadicLocal -/

section

open Filter Topology MeasureTheory Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- LOCALIZED EXACT C-infinity dyadic telescope on arbitrary
consecutive powers 2^a,...,2^b (inclusive), preserving only the
fixed ORIGINAL source smooth positive ψ profile. The telescoping
identity is exact with no dyadic sharp indicator. -/
theorem parity_original_historical_local_smooth_dyadic_telescope434
    (z : ℝ) (hz : 0<z) (a b : ℕ) (hab : a≤b) :
    (∑j∈Finset.Ico a (b+1),
      parityOriginalHistoricalDyadicSmoothPsiReal434 (z/(2:ℝ)^j)) =
      (parityOriginalHistoricalDyadicSmoothStep434 (z/(2:ℝ)^(b+1)):ℝ) -
      (parityOriginalHistoricalDyadicSmoothStep434 (z/(2:ℝ)^a):ℝ) := by
  let f : ℕ → ℝ := fun j =>
    (parityOriginalHistoricalDyadicSmoothStep434 (z/(2:ℝ)^(a+j)):ℝ)
  have hStep (j : ℕ) :
      parityOriginalHistoricalDyadicSmoothPsiReal434 (z/(2:ℝ)^(a+j)) =
      f (j+1)-f j := by
    have hpos : 0<z/(2:ℝ)^(a+j) := div_pos hz (by positivity)
    rw [parity_original_historical_dyadic_psi_telescope_at_pos434 _ hpos]
    have hPow : (z/(2:ℝ)^(a+j))/2 = z/(2:ℝ)^(a+(j+1)) := by
      have hh : a+(j+1)=(a+j)+1 := by omega
      rw [hh,pow_succ]
      ring
    rw [hPow]
  calc
    _ = ∑j∈Finset.range ((b+1)-a),
          parityOriginalHistoricalDyadicSmoothPsiReal434 (z/(2:ℝ)^(a+j)) :=
      Finset.sum_Ico_eq_sum_range _ a (b+1)
    _ = ∑j∈Finset.range ((b+1)-a), (f (j+1)-f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hStep j
    _ = f ((b+1)-a)-f 0 := Finset.sum_range_sub f ((b+1)-a)
    _ = _ := by
      have hab' : a≤b+1 := by omega
      have hadd : a+((b+1)-a)=b+1 := Nat.add_sub_of_le hab'
      simp only [f,add_zero,hadd]

/-- A precisely localized source-relevant smooth dyadic partition:
for EVERY z∈[2^(a+1),2^(b+1)], only the scales
Z_j=2^j (a≤j≤b) are needed, and their SOURCE-CONSTRUCTED
C∞ ψ(z/Z_j) sum is EXACTLY ONE. Thus the number of dyadic
pieces is b-a+1, which can later be proved O(log L) for the
actual SOURCE Parity4.17 permitted z-window. -/
theorem parity_original_historical_local_smooth_dyadic_partition_one434
    (z : ℝ) (a b : ℕ) (hab : a≤b)
    (hzLo : (2:ℝ)^(a+1)≤z)
    (hzHi : z≤(2:ℝ)^(b+1)) :
    (∑j∈Finset.Ico a (b+1),
      parityOriginalHistoricalDyadicSmoothPsiReal434 (z/(2:ℝ)^j))=1 := by
  have hz : 0<z := (by positivity : 0<(2:ℝ)^(a+1)).trans_le hzLo
  rw [parity_original_historical_local_smooth_dyadic_telescope434 z hz a b hab]
  have hBase : (parityOriginalHistoricalDyadicSmoothStep434
      (z/(2:ℝ)^a):ℝ)=0 := by
    apply parity_original_historical_dyadic_step_zero434
    have hpos : 0≤z/(2:ℝ)^a := by positivity
    rw [abs_of_nonneg hpos]
    have h2 : (2:ℝ)^(a+1)=2*(2:ℝ)^a := by
      rw [pow_succ]
      ring
    apply (le_div_iff₀ (by positivity : 0<(2:ℝ)^a)).mpr
    rw [←h2]
    exact hzLo
  have hTop : (parityOriginalHistoricalDyadicSmoothStep434
      (z/(2:ℝ)^(b+1)):ℝ)=1 := by
    apply parity_original_historical_dyadic_step_one434
    have hpos : 0≤z/(2:ℝ)^(b+1) := by positivity
    rw [abs_of_nonneg hpos]
    exact (div_le_iff₀ (by positivity : 0<(2:ℝ)^(b+1))).mpr (by simpa using hzHi)
  rw [hBase,hTop]
  ring

/-- The smooth dyadic partition inserts EXACTLY into ANY
original SIGNED finite complex B633 source sum over a genuine
positive physical z carrier: it is an algebraic equality, not an
upper bound or an equality with an unrelated unrestricted sum.
The dyadic factors ψ(z/2^j) are separately smooth, positive-compact
supported and have fixed log derivative budgets. This is the
safe first smoothization operation BEFORE attempting Parity(4.17).
It does NOT remove source's sharp n,u B509 windows. -/
theorem parity_original_historical_local_smooth_dyadic_signed_source_exact434
    (S : Finset ℕ) (W : ℕ → ℂ) (a b : ℕ) (hab : a≤b)
    (hRange : ∀z∈S,
      (2:ℝ)^(a+1)≤(z:ℝ) ∧ (z:ℝ)≤(2:ℝ)^(b+1)) :
    (∑z∈S,W z) =
      ∑j∈Finset.Ico a (b+1),
        ∑z∈S, parityOriginalHistoricalDyadicSmoothPsi434
          ((z:ℝ)/(2:ℝ)^j)*W z := by
  have hPsi (z : ℕ) (hz : z∈S) :
      (∑j∈Finset.Ico a (b+1),parityOriginalHistoricalDyadicSmoothPsi434
        ((z:ℝ)/(2:ℝ)^j))=(1:ℂ) := by
    have hh := parity_original_historical_local_smooth_dyadic_partition_one434
      (z:ℝ) a b hab (hRange z hz).1 (hRange z hz).2
    have hc := congrArg (fun t : ℝ => (t:ℂ)) hh
    rw [Complex.ofReal_sum] at hc
    simpa only [parityOriginalHistoricalDyadicSmoothPsi434,Complex.ofReal_one] using hc
  calc
    _ = ∑z∈S,((1:ℂ)*W z) := by simp
    _ = ∑z∈S,(∑j∈Finset.Ico a (b+1),
          parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/(2:ℝ)^j))*W z := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hPsi z hz]
    _ = ∑z∈S,∑j∈Finset.Ico a (b+1),
          parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/(2:ℝ)^j)*W z := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [Finset.sum_mul]
    _ = _ := Finset.sum_comm
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSmoothDyadicSourceInsert -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- A correct smooth dyadic partition INSERTION for ANY exact
finite original physical source events q=(m',n), with an arbitrary
noninjective canonical positive integer z=g(q):

  sum_{q physical} W(q) = sum_{a≤j≤b} sum_{q physical}
    ψ(g(q)/2^j)W(q).

This is exact for SIGNED complex W and keeps each physical
source event once, even if two n/m' map to the same z. It is
NOT the false inequality between a signed subset and the full
unrestricted Parity4.17 correlation. -/
theorem parity_original_historical_smooth_dyadic_general_physical_event_insert434
    {ι : Type} [DecidableEq ι] (S : Finset ι) (g : ι → ℕ)
    (W : ι → ℂ) (a b : ℕ) (hab : a≤b)
    (hRange : ∀q∈S,
      (2:ℝ)^(a+1)≤(g q:ℝ) ∧
      (g q:ℝ)≤(2:ℝ)^(b+1)) :
    (∑q∈S,W q) =
    ∑j∈Finset.Ico a (b+1),∑q∈S,
      parityOriginalHistoricalDyadicSmoothPsi434 ((g q:ℝ)/(2:ℝ)^j)*W q := by
  have hPsi (q : ι) (hq : q∈S) :
      (∑j∈Finset.Ico a (b+1),
        parityOriginalHistoricalDyadicSmoothPsi434 ((g q:ℝ)/(2:ℝ)^j))=(1:ℂ) := by
    have hOne := parity_original_historical_local_smooth_dyadic_partition_one434
      (g q:ℝ) a b hab (hRange q hq).1 (hRange q hq).2
    have hCast := congrArg (fun t : ℝ => (t:ℂ)) hOne
    rw [Complex.ofReal_sum] at hCast
    simpa only [parityOriginalHistoricalDyadicSmoothPsi434,Complex.ofReal_one] using hCast
  calc
    _ = ∑q∈S,((1:ℂ)*W q) := by simp
    _ = ∑q∈S,(∑j∈Finset.Ico a (b+1),
        parityOriginalHistoricalDyadicSmoothPsi434 ((g q:ℝ)/(2:ℝ)^j))*W q := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hPsi q hq]
    _ = ∑q∈S,∑j∈Finset.Ico a (b+1),
        parityOriginalHistoricalDyadicSmoothPsi434 ((g q:ℝ)/(2:ℝ)^j)*W q := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_mul]
    _ = _ := Finset.sum_comm

/-- SOURCE-SPECIFIC original Parity h=-2 true UNGATED B509 pair:
insert the EXACT smooth dyadic ψ_Z partition into the REAL
physical (m',n) carrier BEFORE 3D Fourier, with true complex
α, H0, ε, χ(m') and source η_eη_n unchanged. This is the
correct way to replace hard dyadic Z labels without paying a
spurious φ(2|k|) or invoking signed-subset monotonicity.
The Z-range hypothesis must come from the actual source geometry;
no assumption that this smooth source equals unrestricted (4.17)
is made. -/
theorem parity_original_historical_ungated_true_signed_k_physical_smooth_dyadic_insert434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs))
    (a b : ℕ) (hab : a≤b)
    (hRange : ∀q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k,
      (2:ℝ)^(a+1)≤(parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ) ∧
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)≤(2:ℝ)^(b+1)) :
    (∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2:ℝ):ℂ) *
        χ (q.1 : ZMod (2*k.natAbs)) *
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e q.2 m q.1) =
    ∑j∈Finset.Ico a (b+1),
      ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k,
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j) *
        ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2:ℝ):ℂ) *
        χ (q.1 : ZMod (2*k.natAbs)) *
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e q.2 m q.1 := by
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
  let g : ℕ×ℕ → ℕ := fun q => parityOriginalHistoricalCanonicalZ434 e m q.1 q.2
  let W : ℕ×ℕ → ℂ := fun q =>
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2:ℝ):ℂ)*
      χ (q.1 : ZMod (2*k.natAbs)) *
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e q.2 m q.1
  have hSplit := parity_original_historical_smooth_dyadic_general_physical_event_insert434
    S g W a b hab hRange
  dsimp [S,g,W] at hSplit ⊢
  convert hSplit using 1 <;> simp only [mul_assoc]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedEq417SourceWindows -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The EXACT additional arithmetic masks on an original Parity4.17
recovered two-prime-slot pair that make it a PHYSICAL event in the
corrected UNGATED Parity4.10 B509/H0 positive-source Cauchy square.
At original selected u≤Y, both endpoints u=e*v,u'=e*v' must
belong to the genuine positive source window; BOTH natural
vStar=ordinary_P(v),vStar'=ordinary_P(v') must lie in the real
reserved B509 carrier. This is the mask still left when one tries
to invoke Parity(4.17) for the FULL unrestricted z and z+2k sum.
There is NO e-Pfree gate, only e odd in the outer source. -/
def parityOriginalHistoricalUngatedEq417SourceWindow434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n v vp : ℕ) : Prop :=
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let H0 := parityOriginalReservedCartesianVStarSupport434 d L band slot δ
  0 < m ∧ 0 < mp ∧ 0 < n ∧ 0 < v ∧ 0 < vp ∧
    m*n=e*v+2 ∧ mp*n=e*vp+2 ∧
    e*v≤Y ∧ e*vp≤Y ∧
    sourceOriginalOrdinaryPart P v ∈ H0 ∧
    sourceOriginalOrdinaryPart P vp ∈ H0

/-- **EXACT BOTH DIRECTIONS** between the ACTUAL corrected
UNGATED physical original two-endpoint B509 source predicate and
its explicit Parity4.17 two-core reverse masks. For any odd or even
e>0, at fixed (m,m',n) the original source exists if and only if
there exist positive v,v' satisfying both h=-2 equations,
both positive capped u=e*v,u'=e*v' ≤Y, and both actual B509
H0 reserved ordinary-prime-slot membership requirements.

This isolates the true remaining source windows after removing the
spurious e-Pfree gate. It is not an equality to the unrestricted
complex signed Parity(4.17) correlation unless these additional
m,m',z-dependent masks are proved redundant or the spectral
estimate is extended to their supported form. -/
theorem parity_original_historical_ungated_physical_iff_two_core_windows434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : 0 < e) :
    parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n ↔
      ∃v vp : ℕ, parityOriginalHistoricalUngatedEq417SourceWindow434
        d L band slot δ Y e m mp n v vp := by
  constructor
  · intro hv
    obtain ⟨v,vp,vs,vps,hvPos,hvpPos,hmn,hmpn,hvSeq,hvpSeq,hVS,hVPS⟩ :=
      parity_original_historical_ungated_physical_valid_n_real_endpoints434
        d L band slot δ Y e m mp n he hv
    obtain ⟨u,hu,up,hup,hdiv,hdivp,hvs,hvps⟩ := hv
    have hm : 0 < m := (Finset.mem_filter.mp hu).2.1
    have hmp : 0 < mp := (Finset.mem_filter.mp hup).2.1
    have hn : 0 < n := (Finset.mem_filter.mp hu).2.2.1
    have hUle : e*v≤Y := by
      have h := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).2
      have hmnU : m*n=u+2 := (Finset.mem_filter.mp hu).2.2.2
      omega
    have hUPle : e*vp≤Y := by
      have h := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).2
      have hmpnU : mp*n=up+2 := (Finset.mem_filter.mp hup).2.2.2
      omega
    have hFirst : sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) v ∈
        parityOriginalReservedCartesianVStarSupport434 d L band slot δ := by
      rw [←hvSeq]
      exact hVS
    have hSecond : sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) vp ∈
        parityOriginalReservedCartesianVStarSupport434 d L band slot δ := by
      rw [←hvpSeq]
      exact hVPS
    exact ⟨v,vp,hm,hmp,hn,hvPos,hvpPos,hmn,hmpn,hUle,hUPle,hFirst,hSecond⟩
  · rintro ⟨v,vp,hm,hmp,hn,hvPos,hvpPos,hmn,hmpn,huLe,hupLe,hVS,hVPS⟩
    let u := e*v
    let up := e*vp
    have huPos : 0 < u := Nat.mul_pos he hvPos
    have hupPos : 0 < up := Nat.mul_pos he hvpPos
    have huMem : u∈parityOriginalHistoricalFixedMNUSupport434 Y m n := by
      unfold parityOriginalHistoricalFixedMNUSupport434
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨huPos,huLe⟩,
        hm,hn,hmn⟩
    have hupMem : up∈parityOriginalHistoricalFixedMNUSupport434 Y mp n := by
      unfold parityOriginalHistoricalFixedMNUSupport434
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hupPos,hupLe⟩,
        hmp,hn,hmpn⟩
    have hUDiv : e∣u := dvd_mul_right _ _
    have hUPDiv : e∣up := dvd_mul_right _ _
    have hUQuot : u/e=v := Nat.mul_div_cancel_left v he
    have hUPQuot : up/e=vp := Nat.mul_div_cancel_left vp he
    refine ⟨u,huMem,up,hupMem,hUDiv,hUPDiv,?_,?_⟩
    · rw [hUQuot]
      exact hVS
    · rw [hUPQuot]
      exact hVPS
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqBoxRemovesUCap -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- An EXPLICIT containing source u-window for the CORRECTED
original Parity(4.10) natural ungated full post-Cauchy square:

   K ⊆ (0,2U), n∈supp ηn ⊆ (0,3V),
      mn=e*v+2 ⇒ e*v ≤ ceil(6UV).

This is a SOURCE-actual arithmetic inequality with no assumption
UV≤x, no Pfree e, no analytic cancellation and no fake signed
subset inequality. The cap 6UV comes solely from the authentic
original cofactor and η_n support, and therefore is independent
of all e,k,χ,z and target Fourier precision.

NB: This is NOT a proof that the former native cutoff
Y0=floor(2exp L) is already redundant. To replace Y0 by this
larger cap in an ORIGINAL COMPLEX source sum one must establish
separate equality/error control before signed Gram. -/
theorem parity_original_historical_ungated_box_natural_u_cap434
    (U V : ℝ) (hU : 0≤U) (hV : 0≤V)
    (m n e v : ℕ)
    (hm : (m:ℝ)≤2*U) (hn : (n:ℝ)≤3*V)
    (hMN : m*n=e*v+2) :
    e*v≤Nat.ceil (6*U*V) := by
  have hm0 : 0≤(m:ℝ) := Nat.cast_nonneg _
  have hn0 : 0≤(n:ℝ) := Nat.cast_nonneg _
  have h2U : 0≤2*U := by positivity
  have h3V : 0≤3*V := by positivity
  have hMul : (m:ℝ)*(n:ℝ)≤(2*U)*(3*V) :=
    mul_le_mul hm hn hn0 h2U
  have hUV : (m*n:ℝ)≤6*U*V := by
    push_cast
    nlinarith [hMul]
  have hCapReal : (e*v:ℝ)≤6*U*V := by
    have hh : e*v ≤ m*n := by omega
    have hCast : (e*v:ℝ) ≤ (m*n:ℝ) := by exact_mod_cast hh
    exact hCast.trans hUV
  have hCeil : (6*U*V:ℝ)≤(Nat.ceil (6*U*V):ℝ) := Nat.le_ceil _
  exact_mod_cast hCapReal.trans hCeil

/-- The *two* original Parity4.17 physical B633 endpoints in the
full-odd post-Cauchy physical rectangle have the SAME single
universal cap ceil(6UV), including all Pbad e after the corrected
ungated source kernel. This is a safe upper bound on the positive
Cauchy domain, NOT a bound on a complex signed subcorrelation. -/
theorem parity_original_historical_ungated_box_both_natural_u_caps434
    (U V : ℝ) (hU : 0≤U) (hV : 0≤V)
    (m mp n e v vp : ℕ)
    (hm : (m:ℝ)≤2*U) (hmp : (mp:ℝ)≤2*U)
    (hn : (n:ℝ)≤3*V)
    (hMN : m*n=e*v+2) (hMpN : mp*n=e*vp+2) :
    e*v≤Nat.ceil (6*U*V) ∧ e*vp≤Nat.ceil (6*U*V) :=
  ⟨parity_original_historical_ungated_box_natural_u_cap434
      U V hU hV m n e v hm hn hMN,
   parity_original_historical_ungated_box_natural_u_cap434
      U V hU hV mp n e vp hmp hn hMpN⟩

/-- On the FULL ORIGINAL physically supported η_n range,
nonzero smooth weight automatically makes n belong to the actual
finite Nfull. This is TRUE for all odd e including Pbad e,
not an after-FFT truncation of a signed sum. -/
theorem parity_original_historical_ungated_nonzero_eta_n_in_full_envelope434
    (L E V : ℝ) (hL : 8≤L) (hE : 0<E) (hV : 0<V)
    (e n : ℕ)
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n≠0) :
    n∈parityOriginalHistoricalFullNEnvelope434 V := by
  have h := parity_original_historical_full_odd_nonzero_smooth_e_n_ranges434
    L E V hL hE hV e n hw
  unfold parityOriginalHistoricalFullNEnvelope434
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact Nat.le_floor h.2.2.2.le

/-- The NATIVE corrected full-odd source B509 u,u' sharp
Y-window becomes mathematically AUTOMATIC if one chooses the
containing box Ycap=ceil(6UV). The exact source two-ended
H0 predicate is then equivalent to the source-window-free
natural a_v(u/e) h=-2 equations and genuine reserved Q/B509
carriers. No e-Pfree condition, no hard n/Y mask manufactured.

This resolves the u≤Y *support issue at the new cap* but DOES
NOT identify the Ycap SOURCE sum with the historical earlier
Y0=floor(2exp L) definition. That source comparison is an
explicit remaining debt before applying unrestricted Parity(4.17). -/
theorem parity_original_historical_ungated_full_box_physical_iff_no_u_cap434
    (d : ℕ) (L U V : ℝ) (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (e m mp n : ℕ) (he : 0<e)
    (hm : (m:ℝ)≤2*U) (hmp : (mp:ℝ)≤2*U)
    (hn : (n:ℝ)≤3*V) :
    parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ (Nat.ceil (6*U*V)) e m mp n ↔
    ∃v vp : ℕ,
      0 < m ∧ 0 < mp ∧ 0 < n ∧ 0 < v ∧ 0 < vp ∧
      m*n=e*v+2 ∧ mp*n=e*vp+2 ∧
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) v ∈
        parityOriginalReservedCartesianVStarSupport434 d L band slot δ ∧
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) vp ∈
        parityOriginalReservedCartesianVStarSupport434 d L band slot δ := by
  rw [parity_original_historical_ungated_physical_iff_two_core_windows434
    d L band slot δ (Nat.ceil (6*U*V)) e m mp n he]
  constructor
  · rintro ⟨v,vp,hm0,hmp0,hn0,hv,hvp,hMN,hMpN,hU,hUP,hVS,hVPS⟩
    exact ⟨v,vp,hm0,hmp0,hn0,hv,hvp,hMN,hMpN,hVS,hVPS⟩
  · rintro ⟨v,vp,hm0,hmp0,hn0,hv,hvp,hMN,hMpN,hVS,hVPS⟩
    obtain ⟨hU,hUP⟩ := parity_original_historical_ungated_box_both_natural_u_caps434
      U V hU hV m mp n e v vp hm hmp hn hMN hMpN
    exact ⟨v,vp,hm0,hmp0,hn0,hv,hvp,hMN,hMpN,hU,hUP,hVS,hVPS⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqBoxPhysicalZ -/

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

   exp(L)/8 * L^K0 < z < 24*Cbox*exp(L)*L^(K0+88).

The lower support is unchanged from the original positive η_n
window and UV≥expL. The upper uses m≤2U,n<3V,
UV≤Cbox expL and e>E L^-88/2, NOT old u≤floor(2expL).
This is the mathematically correct physical source Z window
for arbitrary fixed original UV≈expL, with no exponential
penalty and no false reuse of the previous gated Y0 proof.
The factor Cbox is fixed geometry; it can later be absorbed into
a fixed logarithmic exponent when L sufficiently large. -/
theorem parity_original_historical_ungated_source_box_smoothed_physical_z_scale434
    (L U V E K0 Cbox : ℝ) (e m mp n u z : ℕ)
    (hL : 8≤L) (hU : 0<U) (hV : 0<V) (hCbox : 0<Cbox)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n≠0)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)<2*U)
    (hmpLo : U≤(mp:ℝ))
    (hmpHi : (mp:ℝ)<2*U)
    (hu : u∈parityOriginalHistoricalFixedMNUSupport434
      (Nat.ceil (6*U*V)) m n)
    (hEz : e*z=mp*u) :
    (Real.exp L/8)*L^K0 < (z:ℝ) ∧
    (z:ℝ) < 24*Cbox*Real.exp L*L^(K0+88) := by
  have hLp : 0<L := by linarith
  have hKpos : 0<L^K0 := Real.rpow_pos_of_pos hLp _
  have hInvpos : 0<L^(-88:ℝ) := Real.rpow_pos_of_pos hLp _
  have hEpos : 0<E := by rw [hE];exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  obtain ⟨heLo,heHi,hnLo,hnHi⟩ :=
    parity_original_historical_full_odd_nonzero_smooth_e_n_ranges434
      L E V hL hEpos hV e n hw
  have hePos : 0<(e:ℝ) :=
    (by positivity : 0<E*L^(-88:ℝ)/2).trans heLo
  have hnPos : 0≤(n:ℝ) := Nat.cast_nonneg _
  have huNat := (Finset.mem_filter.mp hu).2.2.2
  have huReal : (m:ℝ)*(n:ℝ)=(u:ℝ)+2 := by exact_mod_cast huNat
  have hX8 : (8:ℝ)≤Real.exp L := by
    have hx := Real.add_one_le_exp L
    linarith
  have hMN : (Real.exp L)/2 < (m:ℝ)*(n:ℝ) := by
    have h1 : U*(V/2)<U*(n:ℝ) := mul_lt_mul_of_pos_left hnLo hU
    have h2 : U*(n:ℝ)≤(m:ℝ)*(n:ℝ) :=
      mul_le_mul_of_nonneg_right hmLo hnPos
    have h3 : (Real.exp L)/2≤U*(V/2) := by nlinarith [hUV]
    linarith
  have huLow : Real.exp L/4 < (u:ℝ) := by
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
  have hProdLo : U*(Real.exp L/4) ≤ (mp:ℝ)*(u:ℝ) :=
    mul_le_mul hmpLo huLow.le (by positivity) (by positivity)
  have hLowerMul : ((Real.exp L/8)*L^K0)*(e:ℝ)<(e:ℝ)*(z:ℝ) := by
    calc
      _ < ((Real.exp L/8)*L^K0)*(2*E) :=
        mul_lt_mul_of_pos_left heHi (by positivity)
      _ = U*(Real.exp L/4) := by rw [show ((Real.exp L/8)*L^K0)*(2*E)=
          (Real.exp L/4)*(E*L^K0) by ring,hPair];ring
      _ ≤ (mp:ℝ)*(u:ℝ) := hProdLo
      _ = (e:ℝ)*(z:ℝ) := hEzReal.symm
  have hLower : (Real.exp L/8)*L^K0 < (z:ℝ) := by
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

/-! ## OriginalHistoricalLowfreqBoxDyadicZ -/

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
theorem parity_original_historical_ungated_full_box_smoothed_actual_Z_window434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K J : Finset ℕ) (e m : ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (hU : 0<U) (hV : 0<V) (hCbox : 0<Cbox)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (hm : m∈K) (hDyad : ∀mp∈K,
      U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ (Nat.ceil (6*U*V)) e m K J k Z)
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2≠0) :
    (Real.exp L/16)*L^K0 < (Z:ℝ) ∧
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
  have hZ := parity_original_historical_ungated_source_box_smoothed_physical_z_scale434
    L U V E K0 Cbox e m q.1 q.2 u z hL hU hV hCbox hUV hUVhi hE hw
    hmD.1 hmD.2 hmpD.1 hmpD.2 hu hEz
  have hzReal : (z:ℝ) < 2*(Z:ℝ) := by exact_mod_cast hDy.2.2
  have hZlo : (Real.exp L/16)*L^K0 < (Z:ℝ) := by
    have hLp : 0<L^K0 := Real.rpow_pos_of_pos (by linarith : 0<L) _
    nlinarith [hZ.1,hzReal,hLp]
  have hZR : (Z:ℝ)≤(z:ℝ) := by exact_mod_cast hDy.2.1
  exact ⟨hZlo,hZR.trans_lt hZ.2⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqBox417Height -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Numeric rescue of original PARITY(4.17) HEIGHT after correcting
the source cap to Ybox=ceil6UV with UV≤Cbox expL. At sufficiently
large fixed L, the additional factor 3*Cbox from the true u-box
fits the TWO original logarithmic powers already budgeted by
CZ=K0+90; neither K0 nor the original Parity correlation theorem
needs a new parameter. -/
theorem parity_original_historical_box_physical_Z_417_numeric434
    (L K0 Cbox Z : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (hCbox : 0≤Cbox) (hC : 24*Cbox≤L^2)
    (hZlo : (Real.exp L/16)*L^K0 < Z)
    (hZhi : Z < 24*Cbox*Real.exp L*L^(K0+88)) :
    Real.exp L*L^(-(K0+90))≤Z ∧
      Z≤Real.exp L*L^(K0+90) := by
  have hLp : 0<L := by linarith
  have hLow := (parity_original_historical_ungated_full_odd_smooth_Z_polylog_numeric434
    L K0 hL hK0).1
  have hx : 0≤Real.exp L/16 := by positivity
  have hLo : Real.exp L*L^(-(K0+90)) ≤ (Real.exp L/16)*L^K0 := by
    calc
      _ = (Real.exp L/16)*(16*L^(-(K0+90))) := by ring
      _ ≤ (Real.exp L/16)*L^K0 := mul_le_mul_of_nonneg_left hLow hx
  have hUp : 24*Cbox*Real.exp L*L^(K0+88) ≤
      Real.exp L*L^(K0+90) := by
    have hP : 0≤L^(K0+88) := Real.rpow_nonneg hLp.le _
    have h1 : (24*Cbox)*L^(K0+88) ≤ L^2*L^(K0+88) :=
      mul_le_mul_of_nonneg_right hC hP
    have h2 : L^2*L^(K0+88) = L^(K0+90) := by
      rw [←Real.rpow_natCast L 2,←Real.rpow_add hLp]
      congr 1
      ring
    have h3 := mul_le_mul_of_nonneg_left (h1.trans_eq h2)
      (Real.exp_pos L).le
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h3
  exact ⟨(hLo.trans_lt hZlo).le,(hZhi.trans_le hUp).le⟩

/-- SOURCE-CORRECT literal actual Parity(4.17) height legal for any
smoothed original physical k/Z nonzero event in the COMPLETELY
ungated original Ybox model, including e carrying group P primes.
If fixed Cbox≥1 and L≥max(8,24*Cbox), no extra K0 penalty:
 expL L^-(K0+90) ≤ Z ≤ expL L^(K0+90).

The decisive input is the NEW true box window with upper factor
24*Cbox, not the earlier artificially capped Y0 z-window. -/
theorem parity_original_historical_ungated_full_box_actual_Z_Parity417_legal434
    (d : ℕ) (L U V E K0 Cbox : ℝ)
    (hL : 8≤L) (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hLarge : 24*Cbox≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K J : Finset ℕ) (e m : ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (hm : m∈K) (hDyad : ∀mp∈K,
      U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ (Nat.ceil (6*U*V)) e m K J k Z)
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2≠0) :
    Real.exp L*L^(-(K0+90))≤(Z:ℝ) ∧
    (Z:ℝ)≤Real.exp L*L^(K0+90) := by
  have hCpos : 0<Cbox := by linarith
  have hLsq : 24*Cbox≤L^2 := by
    have hL1 : 1≤L := by linarith
    nlinarith [hLarge,hL1]
  have hZ := parity_original_historical_ungated_full_box_smoothed_actual_Z_window434
    d L U V E K0 Cbox hL band slot δ K J e m k Z he hU hV hCpos
    hUV hUVhi hE hm hDyad q hq hw
  exact parity_original_historical_box_physical_Z_417_numeric434
    L K0 Cbox (Z:ℝ) hL hK0 (by linarith) hLsq hZ.1 hZ.2
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqBoxEtaN3D -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- TRUE CAP-FREE Parity(4.14) new source Z upper factor 24 Cbox,
with fixed Cbox, still satisfies the ORIGINAL η_n composition
hypothesis at exponent K0+1:
  Z≤24 Cbox expL L^(K0+88)≤4 expL L^((K0+1)+88),
when 6 Cbox≤L. Consequently NO extra logarithmic derivative
loss beyond the old full-odd exponent K0+90 is needed.
The E=U L^-K0 relation and genuine h=-2 2/(UV) term stay exact. -/
theorem parity_original_historical_box_Z_upper_to_eta_n_polylog434
    (L Z K0 Cbox : ℝ) (hL : 8≤L) (hC : 0≤Cbox)
    (hLarge : 6*Cbox≤L)
    (hZ : Z≤24*Cbox*Real.exp L*L^(K0+88)) :
    Z≤4*Real.exp L*L^((K0+1)+88) := by
  have hLp : 0<L := by linarith
  have hPow : 0≤L^(K0+88) := Real.rpow_nonneg hLp.le _
  have hMul : 24*Cbox*Real.exp L*L^(K0+88) ≤
      4*Real.exp L*L^(K0+88)*L := by
    have h6 : 24*Cbox≤4*L := by linarith
    have hh := mul_le_mul_of_nonneg_right h6
      (mul_nonneg (Real.exp_pos L).le hPow)
    nlinarith [hh]
  calc
    _ ≤ 24*Cbox*Real.exp L*L^(K0+88) := hZ
    _ ≤ 4*Real.exp L*L^(K0+88)*L := hMul
    _ = 4*Real.exp L*L^((K0+1)+88) := by
      have heq : L^((K0+1)+88)=L^(K0+88)*L := by
        rw [show (K0+1)+88=(K0+88)+1 by ring]
        rw [Real.rpow_add hLp,Real.rpow_one]
      rw [heq]
      ring

/-- REAL original PARITY (4.14) all-order η_n 3D smoothness on
the CORRECTED cap-free source box Z≤24Cbox expL L^(K0+88):
‖D^J η_n(g_n)‖ ≤ J! K_J^ηn L^((K0+90)(J+1)).
This re-proves the uniform derivative budget for arbitrary
fixed UV≤Cbox expL instead of incorrectly applying a previous
source theorem whose Z hypothesis depended on artificial Y0.
All constants K_J remain truly SOURCE-fixed. -/
theorem parity_original_historical_box_eta_n_3d_composed_polylog434
    (L U V Z K0 Cbox A : ℝ) (k : ℤ)
    (hL : 8≤L) (hK0 : 0≤K0) (hCbox : 0≤Cbox)
    (hLargeC : 6*Cbox≤L)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hk : k≠0) (hZ : 0≤Z)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88))
    (hA : 0<A) (J : ℕ)
    (hLarge : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
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
  have hOld := parity_original_historical_actual_eta_n_3d_composed_polylog434
    L U V Z (K0+1) A k hL (by linarith) hU hV hUV hk
    hZ hZold hA J hLarge t h0 h1 h2
  simpa only [show (K0+1)+89=K0+90 by ring] using hOld
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqBoxFiveFactor3D -/

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
theorem parity_original_historical_box_five_factors_all_order_polylog434
    (L U E V Z K0 Cbox A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 → -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J : ℕ)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
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
  · have hThreshold := parity_original_eta_n_threshold_mono434
      A hA.le J r hr L hLargeN
    have hh := parity_original_historical_box_eta_n_3d_composed_polylog434
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

/-! ## OriginalHistoricalLowfreqBox3DSourceDerivative -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- Actual original full 3D log Fourier kernel has same bound
‖D^J F_(L,k,Z)(t)‖ ≤ K_J L^[5(K0+90)(J+1)] on fixed log cube
under fully corrected B' geometric Ybox=ceil6UV and physical
Z≤24Cbox expL L^(K0+88), with Cbox fixed, L≥6Cbox.
This is a new SOURCE-CORRECT derivative proof, not assumed
uniform Fourier decay or reuse of old Y0 cap. -/
theorem parity_original_historical_box_full_3d_source_derivative434
    (L U E V Z K0 Cbox A : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (k : ℤ) (hk : k≠0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0)) (hZ : 0≤Z)
    (hCbox : 0≤Cbox) (hLargeC : 6*Cbox≤L)
    (hZupper : Z≤24*Cbox*Real.exp L*L^(K0+88))
    (hA : 0<A)
    (buf : ℝ → ℂ) (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀ (s : ℝ), buf s ≠ 0 → -Real.log A ≤ s ∧ s ≤ Real.log A)
    (J : ℕ)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
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
    (parity_original_historical_box_five_factors_all_order_polylog434
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

/-! ## OriginalHistoricalLowfreqBox3DSeminorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Same fixed original 3D Schwartz seminorm budget at
CORRECT Ybox cap-free Parity4.7 physical z-height; all all-order
source Fréchet derivatives and exact Euclidean log support
under genuine 24Cbox factor, no old Y0. -/
theorem parity_original_historical_box_full_3d_source_seminorm434
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
    (J p : ℕ)
    (hLargeE : 2*A*(J.factorial:ℝ)≤L)
    (hLargeN : 8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+
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
    have hD := parity_original_historical_box_full_3d_source_derivative434
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

