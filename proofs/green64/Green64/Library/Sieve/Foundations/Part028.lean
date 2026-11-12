module

public import Green64.Library.Sieve.Foundations.Part027
public import Green64.Library.Sieve.Foundations.Part026
public import Green64.Library.Sieve.Foundations.Part021
public import Green64.Library.Sieve.Foundations.Part023
public import Green64.Library.Sieve.Foundations.Part025
public import Green64.Library.Sieve.Foundations.Part018
public import Green64.Library.Sieve.Foundations.Part022
public import Green64.Library.Sieve.Foundations.Part019
public import Green64.Library.Sieve.Foundations.Part017
public import Green64.Library.Sieve.Foundations.Part024
public import Green64.Library.Sieve.Foundations.Part008
public import Green64.Library.Sieve.Foundations.Part020

@[expose] public section

/-!
# Sieve / Foundations / Part028

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalFullOddGlobalTailAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 28000000

/-- Pure original Parity (4.15) global Fourier frequency exponent
accounting. The three sources of genuine polynomial loss are the
fixed 3D Fourier moment X, the physical bounded-k graph degree
K0+89, and the original shifted-eighth-divisor positive diagonal
M. Choosing ONE polynomial frequency radius T=L^(X+K0+89+M+D)
removes every such loss and gains arbitrary inverse-log D,
with only the source-fixed factor 4 for ceil of the degree. -/
theorem parity_original_historical_full_odd_global_tail_power_numeric434
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
theorem parity_eventually_original_full_odd_global_B633_fourier_tail_any_log434
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
      ‖parityOriginalHistoricalFullOddFilteredB633FourierOuter434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed ⌊2*Real.exp L⌋₊
        buf (-Real.log A) (Real.log A) hSmooth hSupport -
       parityOriginalHistoricalFullOddFilteredB633BallOuter434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed ⌊2*Real.exp L⌋₊
        buf (-Real.log A) (Real.log A) hSmooth hSupport T‖ ≤
      4*C1*Acoef^2*Real.exp L*L^(-D) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let J : ℕ := 1+P
  let Bfixed : ℝ := max
    (2*A*(J.factorial:ℝ))
    (8*A^2*(J.factorial:ℝ)*(2:ℝ)^J+(J.factorial:ℝ)*A)
  filter_upwards [parity_eventually_original_full_odd_global_B633_fourier_tail_polylog434
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
  have hNumeric := parity_original_historical_full_odd_global_tail_power_numeric434
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

/-! ## OriginalHistoricalFullOddLowFrequencyReduction -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 28000000

/-- Original h=-2 Parity(4.10)-(4.16) Cauchy/TypeII reduction to
ONE authentic physically-supported LOW-frequency B633 two-core
Fourier BALL, plus the proved diagonal and arbitrary L^-D error.
For all requested D>=0 the common polynomial radius is
T=L^[5(K0+90)(P+2)+K0+89+2CW1+256+D]. The source Q-selected e,
full-odd e on the positive factor, actual B509/Q/P prime slots,
signed ε=1/E, fine α, real χ mask and all Fourier phases are
unchanged. Low-frequency Parity4.17 saving remains OPEN. -/
theorem parity_eventually_original_full_odd_low_frequency_typeII_reduction434
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
        ‖parityOriginalHistoricalFullOddFilteredB633BallOuter434
          (sourceOriginalLiteralDepth 20 L) L U E V hLw
          band slot δ ξ rho K alpha signed ⌊2*Real.exp L⌋₊
          buf (-Real.log A) (Real.log A) hSmooth hSupport T‖ +
        4*C1*Acoef^2*Real.exp L*L^(-D)) := by
  filter_upwards [parity_eventually_original_full_odd_Cauchy_diag_B633_3d_fourier_bound434
    S beta gamma K0 hS hbeta hgamma A buf hSmooth hSupport hOne,
    parity_eventually_original_full_odd_global_B633_fourier_tail_any_log434
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
  let Full := parityOriginalHistoricalFullOddB633FourierOuter434
    d L U E V hLw band slot δ ξ rho K alpha signed Y
    buf (-Real.log A) (Real.log A) hSmooth hSupport
  let Filtered := parityOriginalHistoricalFullOddFilteredB633FourierOuter434
    d L U E V hLw band slot δ ξ rho K alpha signed Y
    buf (-Real.log A) (Real.log A) hSmooth hSupport
  let Ball := parityOriginalHistoricalFullOddFilteredB633BallOuter434
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
    parity_original_historical_full_odd_B633_outer_eq_nonzero_weight434
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

/-! ## OriginalHistoricalFullOddFixedBufferWitness -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- One actually CONSTRUCTED original Parity fixed logarithmic
C∞ Fourier buffer and ONE compact 3D Euclidean radius exist,
both chosen BEFORE any original large-L asymptotic, signed k,
character χ, dyadic Z, physical e,m,n or inverse-log D.
The C∞ buffer has support in [-log A,log A] and equals 1 on
[0,log 2], and the exact 3D source support cube is inside radius R.
This discharges the only fixed-profile prerequisites of the
native global arbitrary inverse-log high-frequency tail theorem
and the native TypeII-lowfreq reduction. Neither theorem requires
postulating a Fourier decay or synthetic parameter-dependent η. -/
theorem parity_original_full_odd_genuine_uniform_fourier_buffer_exists434 :
    ∃ A : ℝ, 64≤A ∧ ∃ R : ℝ,1≤R ∧
      ∃ buf : ℝ → ℂ,
        ∃ (hSmooth : ContDiff ℝ ∞ buf)
          (hSupport : ∀t : ℝ,buf t≠0 →
            -Real.log A≤t ∧ t≤Real.log A),
          (∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) ∧
          (∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,
            ‖t‖≤R) := by
  obtain ⟨A,hA,buf,hSmooth,hSupport,hOne,hNorm,K,hK,hBudget⟩ :=
    parity_original_historical_fixed_log_buffer_exists434
  obtain ⟨R,hR,hCube⟩ :=
    parity_original_historical_euclidean_fixed_log_cube_radius_exists434 A
  exact ⟨A,hA,R,hR,buf,hSmooth,hSupport,hOne,hCube⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddTruncTriangle -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Quantitative exact complex-weighted finite Fubini triangle:
no operator norm or #character factor arises by moving the
original Parity(2.6) coefficients outside the physical finite
Z-sum before 3D Fourier truncation. -/
theorem parity_original_finite_weighted_complex_truncation_error_le434
    {ι : Type} [DecidableEq ι]
    (S : Finset ι) (c f g : ι → ℂ) :
    ‖(∑i∈S,c i*f i) - (∑i∈S,c i*g i)‖ ≤
      ∑i∈S,‖c i‖*‖f i-g i‖ := by
  rw [←Finset.sum_sub_distrib]
  have hEq : (∑i∈S,(c i*f i-c i*g i)) =
      ∑i∈S,c i*(f i-g i) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hEq]
  calc
    _ ≤ ∑i∈S,‖c i*(f i-g i)‖ := norm_sum_le _ _
    _ = ∑i∈S,‖c i‖*‖f i-g i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul]

/-- Legitimate complex weighted source-to-ball Fourier truncation
triangle, including one original χ coefficient cχ and its
genuine **selected nonzero-weight Z support**: the error on
∑χ cχ ∑_{Z∈Sχ}Fχ,Z is bounded by ∑χ |cχ|∑Z |Fχ,Z−Gχ,Z|.
This preserves all possible complex cancellation inside each
selected physical B633 cell; the only triangle losses are explicit. -/
theorem parity_original_finite_nested_weighted_complex_truncation_le434
    {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (T : ι → Finset κ)
    (c : ι → ℂ) (f g : ι → κ → ℂ) :
    ‖(∑i∈S,c i*(∑j∈T i,f i j)) -
      (∑i∈S,c i*(∑j∈T i,g i j))‖ ≤
      ∑i∈S,‖c i‖*(∑j∈T i,‖f i j-g i j‖) := by
  have hFirst := parity_original_finite_weighted_complex_truncation_error_le434
    S c (fun i => ∑j∈T i,f i j) (fun i => ∑j∈T i,g i j)
  have hSecond : (∑i∈S,‖c i‖ * ‖(∑j∈T i,f i j) -
      (∑j∈T i,g i j)‖) ≤
    ∑i∈S,‖c i‖ * (∑j∈T i,‖f i j-g i j‖) := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [←Finset.sum_sub_distrib]
    exact norm_sum_le (T i) (fun j=>f i j-g i j)
  exact hFirst.trans hSecond
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddTruncOuterTriangle -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Original finite e,m,k signed SOURCE outer summation can be
compared to another signed source outer summation by a rigorously
accounted term-by-term norm, with THREE genuinely dependent
physical supports S_e × M_e × K_(e,m). This is only the valid
triangle bound on the difference of two COMPLEX sums, never a
bound of one restricted correlation by a larger complex sum. -/
theorem parity_original_three_nested_source_complex_triangle434
    {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (M : α → Finset β) (K : α → β → Finset γ)
    (f g : α → β → γ → ℂ) :
    ‖(∑a∈S,∑b∈M a,∑c∈K a b,f a b c) -
      (∑a∈S,∑b∈M a,∑c∈K a b,g a b c)‖ ≤
    ∑a∈S,∑b∈M a,∑c∈K a b,‖f a b c-g a b c‖ := by
  rw [←Finset.sum_sub_distrib]
  apply norm_sum_le_of_le S
  intro a ha
  rw [←Finset.sum_sub_distrib]
  apply norm_sum_le_of_le (M a)
  intro b hb
  rw [←Finset.sum_sub_distrib]
  exact norm_sum_le (K a b) (fun c=>f a b c-g a b c)

/-- Full original Parity(4.16) source B633 Fourier outer sum
truncated to a common real frequency BALL ||ζ||≤T ONLY AFTER
eliminating all physically attained binary Z cells with identically
zero actual eta_e,L*eta_n SOURCE weight. Its finite k/Z support,
original signed ε, b629 fine alpha, Q/P/B509, cχ, 2π U/U/Z,
all real source m',n physical H0 factor, and χ conjugations are
unchanged. No unsupported or all-zero weight Z term is inserted. -/
def parityOriginalHistoricalFullOddFilteredB633BallTruncatedOuter434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) : ℂ :=
  ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs χ *
          (∑Z∈parityOriginalHistoricalFullOddNonzeroWeightZCells434
              d L E V hL band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k,
            parityOriginalHistoricalFullOddB633TruncatedCell434
              d L U E V hL Z k band slot δ ξ rho α signed Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) χ
              buf a b hSmooth hSupp T)

/-- Exact arithmetic-error triangle for the ENTIRE original
physical full odd-e,n source B633 Fourier correlation before/after
low-frequency BALL truncation. The right hand side is the true
full e,m,k,χ,nonzero-weight-Z finite sum of the EXACT per-cell
full-minus-truncated 3D Fourier errors weighted by original |cχ|.
There is no hidden #chars/#m/#e/#Z factor and no dropped
zero-source cell, because it was removed at full Fourier level.

This establishes the correct analytic interface for summing the
previously proved uniform per-k/Z truncation errors. It does not
by itself bound this entire error by expL times inverse logs:
actual multiplicities and arithmetic z interactions must still
be controlled without a factor #m or #e. -/
theorem parity_original_historical_full_odd_B633_outer_trunc_triangle434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) :
    ‖parityOriginalHistoricalFullOddFilteredB633FourierOuter434
        d L U E V hL band slot δ ξ rho K α signed Y
        buf a b hSmooth hSupp -
      parityOriginalHistoricalFullOddFilteredB633BallTruncatedOuter434
        d L U E V hL band slot δ ξ rho K α signed Y
        buf a b hSmooth hSupp T‖ ≤
    ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
      ∑m∈K,
        ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
          ∑χ : DirichletCharacter ℂ (2*k.natAbs),
            ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
            (∑Z∈parityOriginalHistoricalFullOddNonzeroWeightZCells434
              d L E V hL band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k,
              ‖(∫ζ : EuclideanSpace ℝ (Fin 3),
                  parityOriginalHistoricalActualB6333DFourierCell434
                    d L U E V hL Z k band slot δ ξ rho α signed Y e m K
                    (parityOriginalHistoricalFullNEnvelope434 V) χ
                    buf a b hSmooth hSupp ζ) -
                parityOriginalHistoricalFullOddB633TruncatedCell434
                  d L U E V hL Z k band slot δ ξ rho α signed Y e m K
                  (parityOriginalHistoricalFullNEnvelope434 V) χ
                  buf a b hSmooth hSupp T‖) := by
  let S := parityOriginalHistoricalFullOddEEnvelope434 E
  let M : ℕ → Finset ℕ := fun _ => K
  let Q : ℕ → ℕ → Finset ℤ := fun e m =>
    parityOriginalHistoricalNonzeroKSupport434 e m K
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let ZS : ℕ → ℕ → ℤ → Finset ℕ := fun e m k =>
    parityOriginalHistoricalFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k
  let F : ℕ → ℕ → ℤ → ℂ := fun e m k =>
    ∑χ : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs χ *
      (∑Z∈ZS e m k,
        ∫ζ : EuclideanSpace ℝ (Fin 3),
          parityOriginalHistoricalActualB6333DFourierCell434
            d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
            buf a b hSmooth hSupp ζ)
  let G : ℕ → ℕ → ℤ → ℂ := fun e m k =>
    ∑χ : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs χ *
      (∑Z∈ZS e m k,
        parityOriginalHistoricalFullOddB633TruncatedCell434
          d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
          buf a b hSmooth hSupp T)
  let B : ℕ → ℕ → ℤ → ℝ := fun e m k =>
    ∑χ : DirichletCharacter ℂ (2*k.natAbs),
      ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
      (∑Z∈ZS e m k,
        ‖(∫ζ : EuclideanSpace ℝ (Fin 3),
            parityOriginalHistoricalActualB6333DFourierCell434
              d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
              buf a b hSmooth hSupp ζ) -
          parityOriginalHistoricalFullOddB633TruncatedCell434
            d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
            buf a b hSmooth hSupp T‖)
  change ‖(∑e∈S,∑m∈M e,∑k∈Q e m,F e m k) -
    (∑e∈S,∑m∈M e,∑k∈Q e m,G e m k)‖ ≤
    ∑e∈S,∑m∈M e,∑k∈Q e m,B e m k
  have hOuter := parity_original_three_nested_source_complex_triangle434
    S M Q F G
  have hEach (e m : ℕ) (k : ℤ) :
      ‖F e m k-G e m k‖ ≤ B e m k := by
    let C : DirichletCharacter ℂ (2*k.natAbs) → ℂ := fun χ =>
      parityShiftTwoMaskCoefficient434 k.natAbs χ
    let f : DirichletCharacter ℂ (2*k.natAbs) → ℕ → ℂ :=
      fun χ Z => ∫ζ : EuclideanSpace ℝ (Fin 3),
        parityOriginalHistoricalActualB6333DFourierCell434
          d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
          buf a b hSmooth hSupp ζ
    let g : DirichletCharacter ℂ (2*k.natAbs) → ℕ → ℂ :=
      fun χ Z => parityOriginalHistoricalFullOddB633TruncatedCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hSmooth hSupp T
    change ‖(∑χ : DirichletCharacter ℂ (2*k.natAbs),
        C χ * ∑Z∈ZS e m k,f χ Z) -
      (∑χ : DirichletCharacter ℂ (2*k.natAbs),
        C χ * ∑Z∈ZS e m k,g χ Z)‖ ≤
      ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        ‖C χ‖ * ∑Z∈ZS e m k,‖f χ Z-g χ Z‖
    exact parity_original_finite_nested_weighted_complex_truncation_le434
      (Finset.univ : Finset (DirichletCharacter ℂ (2*k.natAbs)))
      (fun _ => ZS e m k) C f g
  have hSums : (∑e∈S,∑m∈M e,∑k∈Q e m,‖F e m k-G e m k‖) ≤
    ∑e∈S,∑m∈M e,∑k∈Q e m,B e m k := by
    apply Finset.sum_le_sum
    intro e he
    apply Finset.sum_le_sum
    intro m hm
    apply Finset.sum_le_sum
    intro k hk
    exact hEach e m k
  exact hOuter.trans hSums
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedCauchy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Correct natural UNGATED original Parity(4.10) physical a_v(v)
when the e factor is an arbitrary positive divisor of source u.
Here v=u/e and vStar=ordinary_P(v), EXACTLY as in Parity(4.7).
The original VStar support and B509 prime convolution are retained;
no condition that e itself be P-free is imposed on the new
post-Cauchy quadratic domain.

On the ORIGINAL selected-Q e, the old e*vStar=ordinary_P(u)
gate is exactly equivalent to these natural conditions by the
previous native integer factorization theorem. -/
def parityOriginalHistoricalUngatedEVStarAtU434
    (d : ℕ) (L : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (e vStar : ℕ) : ℂ :=
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  if e ∣ u ∧ vStar = sourceOriginalOrdinaryPart P (u/e) then
    parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vStar (u/e)
  else 0

/-- True original selected-Q e source: old allocated P-free
prime-convolution endpoint = the new 4.10 UNGATED a_v(u/e) endpoint.
This is pointwise for EVERY u>0 and every source VStar; no loss
of B509 residual, Q/P powers, epsilon, W1 or Mellin frequency. -/
theorem parity_original_historical_Pfree_source_AV_eq_ungated434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (u e vs : ℕ)
    (hu : 0<u) (he : 0<e)
    (hFree : ∀p∈Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L),
      ¬p∣e) :
    parityOriginalIntrinsicUnwindowedEVStarAtU434
      d L u signed band slot δ ξ rho e vs =
    parityOriginalHistoricalUngatedEVStarAtU434
      d L u signed band slot δ ξ rho e vs := by
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  have hIff := parity_original_historical_Pfree_e_gate_iff_ungated_divisor434
    P u e vs hu he hFree
  change (if e*vs=sourceOriginalOrdinaryPart P u then
    parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vs
      (vs*sourceOriginalPPrimePart P u) else 0) =
    (if e∣u ∧ vs=sourceOriginalOrdinaryPart P (u/e) then
      parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vs (u/e) else 0)
  by_cases hg : e*vs=sourceOriginalOrdinaryPart P u
  · have hn := hIff.mp hg
    simp only [if_pos hg,if_pos hn]
    have hSplit := source_original_ordinary_times_P_part P u hu.ne'
    have huEq : u=e*(vs*sourceOriginalPPrimePart P u) := by
      calc
        _ = sourceOriginalOrdinaryPart P u*sourceOriginalPPrimePart P u := hSplit.symm
        _ = (e*vs)*sourceOriginalPPrimePart P u := by rw [hg]
        _ = e*(vs*sourceOriginalPPrimePart P u) := by ring
    have hDivEq : u/e=vs*sourceOriginalPPrimePart P u := by
      calc
        _ = (e*(vs*sourceOriginalPPrimePart P u))/e :=
          congrArg (fun w : ℕ => w/e) huEq
        _ = vs*sourceOriginalPPrimePart P u :=
          Nat.mul_div_cancel_left _ he
    rw [hDivEq]
  · have hn : ¬(e∣u ∧ vs=sourceOriginalOrdinaryPart P (u/e)) := by
      intro hh
      exact hg (hIff.mpr hh)
    simp only [if_neg hg,if_neg hn]

/-- Original Parity(4.10) UNGATED physical e,n,m coefficient:
its physical u=m*n-2, source u≤Y and reserved H0 support are
unmodified, but it treats an arbitrary e|u using v=u/e and
vStar=ordinary_P(v), not the P-free allocation shortcut.
It can therefore be nonzero for e containing P-group primes,
unlike the original allocated-e coefficient. -/
def parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (Y e n m : ℕ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    if (0 < m ∧ 0 < n ∧ m*n=u+2) then
      ∑vStar∈parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
        parityOriginalHistoricalUngatedEVStarAtU434
          d L u signed band slot δ ξ rho e vStar
    else 0

/-- Original selected-Q e and any genuine fixed n,m source:
NEW ungated 4.10 physical coefficient equals the ORIGINAL
P-free-gated B509 source one, on the nose. This is the main safe
interface to enlarge the NONNEGATIVE Cauchy square to an honest
ungated all-odd e domain BEFORE Gram, and then derive Parity(4.17)
without the artificial source-image subset in the old expansion. -/
theorem parity_original_historical_Pfree_e_Cauchy_physical_eq_ungated434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (Y e n m : ℕ)
    (he : 0<e)
    (hFree : ∀p∈Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L),
      ¬p∣e) :
    parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m =
    parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m := by
  unfold parityOriginalHistoricalCauchyPhysicalAtENM434
    parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
  apply Finset.sum_congr rfl
  intro u hu
  have huPos : 0<u := (Finset.mem_Ioc.mp hu).1
  by_cases hmn : 0 < m ∧ 0 < n ∧ m*n=u+2
  · simp only [if_pos hmn]
    apply Finset.sum_congr rfl
    intro vs hvs
    exact parity_original_historical_Pfree_source_AV_eq_ungated434
      d L band slot δ ξ rho signed u e vs huPos he hFree
  · simp only [if_neg hmn]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedCauchySourceJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- New corrected true historical h=-2 Cauchy bilinear amplitude
with original SELECTED-Q e coefficient only outside, but the
physical coefficient INSIDE is now the UNGATED natural a_v(u/e),
which is well-defined for arbitrary e|u, including e divisible
by original group P-primes. This is precisely the form needed
to enlarge the positive Cauchy square legitimately to all odd e
before seeking the FULL Parity(4.17) spectral correlation. -/
def parityOriginalHistoricalUngatedCauchyAtDelta434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑n∈J,
      (parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e * β n) *
      (∑m∈K, α m *
        parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m)

/-- The original Parity(4.7) Cauchy amplitude is EXACTLY the
ungated natural e|u, vStar=ordinary_P(u/e) physical Cauchy
on every TRUE selected-Q e support: the old allocated gate
and natural a_v agree because the true original selected e is
P-free. No β, α, Fourier, H0 or ε data are changed.
This identity requires only source e positivity on the selected
support, not any *ungated* estimate as an assumption. -/
theorem parity_original_historical_selected_Cauchy_eq_ungated434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (hePos : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,0<e) :
    parityOriginalHistoricalCauchyAtDelta434
      d L E band slot δ ξ rho K J α β signed Y =
    parityOriginalHistoricalUngatedCauchyAtDelta434
      d L E band slot δ ξ rho K J α β signed Y := by
  rw [parity_original_historical_cauchy_e_window_restrict_exact434]
  unfold parityOriginalHistoricalUngatedCauchyAtDelta434
  apply Finset.sum_congr rfl
  intro e he
  have hFree := parity_original_historical_actual_selected_e_P_free434
    d L hL band slot δ e (Finset.mem_filter.mp he).1
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [parity_original_historical_Pfree_e_Cauchy_physical_eq_ungated434
    d L band slot δ ξ rho signed Y e n m (hePos e he) hFree]

/-- Actual large-L original Parity SELECTED Q-allocated signed Cauchy
coefficient is the true natural UNGATED a_v(v) physical amplitude.
The original Q-selected e remain odd/positive and have no P-group
prime factors; e is NOT constrained in the new kernel after the
positive square is enlarged. This removes the additional source
gate that otherwise prevents applying Parity(4.17) to the full
Cauchy quadratic form. -/
theorem parity_eventually_original_selected_Cauchy_eq_natural_ungated434 :
    ∀ᶠ L : ℝ in atTop,0<L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (E rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (signed : Bool) (Y : ℕ),
      parityOriginalHistoricalCauchyAtDelta434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α β signed Y =
      parityOriginalHistoricalUngatedCauchyAtDelta434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α β signed Y := by
  filter_upwards [parity_eventually_original_cartesian_selected_e_odd_unit434,
    eventually_gt_atTop (0:ℝ)] with L hOdd hL
  refine ⟨hL,?_⟩
  intro band slot δ ξ E rho K J α β signed Y
  apply parity_original_historical_selected_Cauchy_eq_ungated434
    (sourceOriginalLiteralDepth 20 L) L E hL band slot δ ξ rho
    K J α β signed Y
  intro e he
  have hOdd' := (hOdd.2 band slot δ e (Finset.mem_filter.mp he).1).1
  exact hOdd'.pos
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedCauchyFullOdd -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- ORIGINAL source Cauchy nonnegative square on the true selected
Q e,n pair, using the natural UNGATED Parity(4.10) a_v(u/e) coefficient.
This is equal to the old selected-e Cauchy quadratic form whenever
original e is Q-selected/P-free. -/
def parityOriginalHistoricalUngatedWeightedActiveSquare434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℝ :=
  ∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑n∈J, w e n * ‖∑m∈K, α m *
      parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2

/-- Corrected original Parity(4.10) NONNEGATIVE full odd-e/n square,
using the physically natural a_v(u/e), not the SOURCE-selected-Q
P-free shortcut. When e contains original group P primes, this
new square can include real terms missing from the previous
P-gated square. We do NOT assume any spectral/cancellation saving. -/
def parityOriginalHistoricalUngatedWeightedExtendedSquare434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℝ :=
  ∑e∈Eenv,∑n∈Nenv,w e n * ‖∑m∈K,α m *
      parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2

/-- True original selected-Q P-free e source square is exactly the
new natural UNGATED a_v(v) Cauchy square on the historical e,n
support. The two squares must only be equated BEFORE any extension
of e into the full odd interval; for P-bad e they may differ.
All factorial B509 residuals and full h=-2 source signs survive. -/
theorem parity_original_historical_selected_gated_square_eq_ungated434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ)
    (hPos : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,0<e) :
    parityOriginalHistoricalWeightedActiveCauchySquare434
      d L E band slot δ ξ rho K J α signed Y w =
    parityOriginalHistoricalUngatedWeightedActiveSquare434
      d L E band slot δ ξ rho K J α signed Y w := by
  unfold parityOriginalHistoricalWeightedActiveCauchySquare434
    parityOriginalHistoricalUngatedWeightedActiveSquare434
  apply Finset.sum_congr rfl
  intro e he
  have hPFree := parity_original_historical_actual_selected_e_P_free434
    d L hL band slot δ e (Finset.mem_filter.mp he).1
  apply Finset.sum_congr rfl
  intro n hn
  have hInner :
      (∑m∈K,α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m) =
      ∑m∈K,α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [parity_original_historical_Pfree_e_Cauchy_physical_eq_ungated434
      d L band slot δ ξ rho signed Y e n m (hPos e he) hPFree]
  rw [hInner]

/-- The correct Parity(4.10) UNGATED nonnegative Cauchy square may be
extended from true sparse selected-Q source e,n to ANY finite
superset Eenv×Nenv, with no inequality asserted for complex
signed offdiagonal subsets. The proof is the actual positivity
of w(e,n)·||Σm α_m a_v(u/e)||². -/
theorem parity_original_historical_ungated_positive_carrier_enlarge434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ)
    (hEsub : parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ ⊆ Eenv)
    (hNsub : J ⊆ Nenv)
    (hw : ∀e∈Eenv,∀n∈Nenv,0≤w e n) :
    parityOriginalHistoricalUngatedWeightedActiveSquare434
      d L E band slot δ ξ rho K J α signed Y w ≤
    parityOriginalHistoricalUngatedWeightedExtendedSquare434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w := by
  let Q := parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ
  let A : ℕ×ℕ → ℝ := fun en => w en.1 en.2 *
    ‖∑m∈K,α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y en.1 en.2 m‖^2
  have hProd : Q.product J ⊆ Eenv.product Nenv := by
    intro p hp
    obtain ⟨he,hn⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨hEsub he,hNsub hn⟩
  have hPos : ∀p∈Eenv.product Nenv,0≤A p := by
    intro p hp
    obtain ⟨he,hn⟩ := Finset.mem_product.mp hp
    exact mul_nonneg (hw p.1 he p.2 hn) (sq_nonneg _)
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hProd
    (fun en hen hnot => hPos en hen)
  unfold parityOriginalHistoricalUngatedWeightedActiveSquare434
    parityOriginalHistoricalUngatedWeightedExtendedSquare434
  change (∑e∈Q,∑n∈J,A (e,n)) ≤ ∑e∈Eenv,∑n∈Nenv,A (e,n)
  rw [←Finset.sum_product,←Finset.sum_product]
  exact hh

/-- **NEW ACTUALLY UNGATED SOURCE Parity(4.10) Cauchy bound**:
the original signed Q-allocated bilinear source is controlled by
a positive quadratic form whose physical inner coefficient is the
natural Parity a_v(u/e) for EVERY e divisor, not e*vStar=ordinary_P(u).
This removes a mathematical barrier to invoking the whole Parity(4.17)
prime-slot correlation after the pre-Gram domain enlargement.
The SOURCE original sparse selected-Q e Pfree equality is proven
and the extension is valid only because the square is nonnegative.
No bound for the NEW UNGATED offdiagonal is assumed. -/
theorem parity_original_historical_ungated_source_Cauchy_enlarge434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J Eenv Nenv : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ)
    (hPos : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,0<e)
    (hOne : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,∀n∈J,1≤w e n)
    (hEsub : parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ ⊆ Eenv)
    (hNsub : J ⊆ Nenv)
    (hw : ∀e∈Eenv,∀n∈Nenv,0≤w e n) :
    ‖parityOriginalHistoricalCauchyAtDelta434
      d L E band slot δ ξ rho K J α β signed Y‖^2 ≤
    (∑e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,∑n∈J,
      ‖parityOriginalHistoricalWindowAE434
        d L E band slot δ ξ rho e*β n‖^2) *
    parityOriginalHistoricalUngatedWeightedExtendedSquare434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w := by
  have hOld := parity_original_historical_signed_weighted_active_Cauchy434
    d L E band slot δ ξ rho K J α β signed Y w hOne
  have hEq := parity_original_historical_selected_gated_square_eq_ungated434
    d L E hL band slot δ ξ rho K J α signed Y w hPos
  rw [hEq] at hOld
  have hSub := parity_original_historical_ungated_positive_carrier_enlarge434
    d L E band slot δ ξ rho K J Eenv Nenv α signed Y w
    hEsub hNsub hw
  have hMass : 0≤(∑e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,∑n∈J,
      ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e*β n‖^2) := by
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro n hn
    exact sq_nonneg _
  exact hOld.trans (mul_le_mul_of_nonneg_left hSub hMass)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedFullOddEtaCauchy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The REAL original Parity(4.10) *UNGATED* positive Cauchy square,
with actual source moving η_e,L and fixed η_n, over the WHOLE
permitted odd-e and n intervals, not a P-prime-free artificially
restricted image:

  |B'_source|² ≤ (Σoriginal selected-Q e,n |a_e β_n|²) *
    Σ_{all odd e≤floor(2E),0≤n≤floor(3V)}
       η_e(e/E)η_n(n/V) · |Σ_m α_m a_v((mn-2)/e)|²,

where a_v(v) is the authentic original B509 reserved-prime
H0(v_*), v_*=ordinary_P(v), with both signed ε choices and W1.
The original source selected e was proved Pfree, so the old
allocated-e coefficient equals the ungated one *before* Cauchy.
The enlarged nonnegative form includes P-bad e terms correctly.

This fixes the source-to-Parity(4.17) mask problem left by the
previous P-gated full-odd source expansion. It does NOT yet bound
the NEW ungated positive diagonal or signed low-frequency 4.17,
so unconditional original TypeII(4.2) is NOT claimed. -/
theorem parity_eventually_original_real_410_ungated_full_odd_eta_Cauchy434 :
    ∀ᶠ L : ℝ in atTop,8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (E V rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (signed : Bool) (Y : ℕ),
      0<E → 0<V →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      let Efull := parityOriginalHistoricalFullOddEEnvelope434 E
      let Nfull := parityOriginalHistoricalFullNEnvelope434 V
      let w := parityOriginalHistoricalDyadicEtaWeight434 L E V hLw
      ‖parityOriginalHistoricalCauchyAtDelta434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α β signed Y‖^2 ≤
      (∑e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*β n‖^2) *
      parityOriginalHistoricalUngatedWeightedExtendedSquare434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K Efull Nfull α signed Y w := by
  filter_upwards [parity_eventually_original_cartesian_selected_e_odd_unit434,
    eventually_ge_atTop (8:ℝ)] with L hOdd hL8
  refine ⟨hL8,?_⟩
  intro hLw band slot δ ξ E V rho K J α β signed Y hE hV hnRange
  dsimp only
  have hActiveOdd : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
       (sourceOriginalLiteralDepth 20 L) L E band slot δ,Odd e := by
    intro e he
    exact (hOdd.2 band slot δ e (Finset.mem_filter.mp he).1).1
  have hPositive : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
       (sourceOriginalLiteralDepth 20 L) L E band slot δ,0<e := by
    intro e he
    exact (hActiveOdd e he).pos
  have hEsub := parity_original_historical_active_selected_e_sub_full_odd434
    (sourceOriginalLiteralDepth 20 L) L E hE.le band slot δ hActiveOdd
  have hNsub := parity_original_historical_actual_n_dyad_sub_full_envelope434
    V hV.le J hnRange
  have hOne : ∀e∈parityOriginalHistoricalCauchyActiveESupport434
       (sourceOriginalLiteralDepth 20 L) L E band slot δ,
       ∀n∈J,1≤parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e n := by
    intro e he n hn
    exact parity_original_historical_dyadic_eta_weight_source_ge_one434
      L E V hLw hE hV e n (Finset.mem_filter.mp he).2
      (hnRange n hn).1 (hnRange n hn).2
  have hW : ∀e∈parityOriginalHistoricalFullOddEEnvelope434 E,
       ∀n∈parityOriginalHistoricalFullNEnvelope434 V,
         0≤parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e n := by
    intro e he n hn
    exact (parity_original_historical_dyadic_eta_weight_polylog434
      L E V hLw e n).1
  exact parity_original_historical_ungated_source_Cauchy_enlarge434
    (sourceOriginalLiteralDepth 20 L) L E (by linarith)
    band slot δ ξ rho K J
    (parityOriginalHistoricalFullOddEEnvelope434 E)
    (parityOriginalHistoricalFullNEnvelope434 V)
    α β signed Y (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw)
    hPositive hOne hEsub hNsub hW
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedFullOddGram -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- Native finite COMPLEX Gram at one genuine source (e,n), with
the correctly UNGATED a_v(u/e) physical source. This is the full
unrestricted odd e result, not the former artificially Pfree-e
offdiagonal. -/
theorem parity_original_historical_ungated_e_n_square_diag_offdiag434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y e n : ℕ) :
    (((‖∑ m ∈ K, α m * parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n m‖^2 : ℝ):ℂ)) =
      ((∑ m ∈ K,
        ‖α m * parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2 : ℝ) : ℂ) +
      (∑ m ∈ K, ∑ mp ∈ K.erase m,
        (α m * parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m) *
        star (α mp * parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n mp)) := by
  let F : ℕ → ℂ := fun m =>
    α m * parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m
  calc
    _ = (∑ m ∈ K, ∑ mp ∈ K, F m * star (F mp)) :=
      parity_original_complex_cauchy_gram434 K F
    _ = (∑ m ∈ K, F m * star (F m)) +
          (∑ m ∈ K, ∑ mp ∈ K.erase m, F m * star (F mp)) := by
      calc
        _ = ∑ m ∈ K, (F m * star (F m) +
              ∑ mp ∈ K.erase m, F m * star (F mp)) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hh := Finset.sum_erase_add K
            (fun mp => F m * star (F mp)) hm
          simpa only [add_comm] using hh.symm
        _ = _ := Finset.sum_add_distrib
    _ = ((∑ m ∈ K, ‖F m‖^2 : ℝ) : ℂ) +
          (∑ m ∈ K, ∑ mp ∈ K.erase m, F m * star (F mp)) := by
      rw [parity_original_complex_cauchy_gram_diagonal_norm434]
    _ = _ := rfl


/-- Original full-odd-e Parity (4.10) NATURAL UNGATED positive
Cauchy square = true positive diagonal + COMPLEX signed offdiag,
with both original Q/P/B509 prime-slot sources and multiplicities.
This is proved *after* legally expanding the positive square to
include P-bad e, avoiding the previous false equivalence between a
strict complex subset and the full Parity(4.17) correlation. -/
def parityOriginalHistoricalUngatedWeightedExtendedDiagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℝ :=
  ∑ e∈Eenv,
    ∑ n∈Nenv,w e n *
      ∑ m∈K,‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2

/-- Exact ORIGINAL smooth-weighted complex signed Parity (4.13)
OFFDIAGONAL, with η_e(e/E)η_n(n/V) outside the genuine m,m' pair.
Critically it is NOT assumed nonnegative, bounded by the raw
unweighted offdiagonal, or equal to the ungated physical source. -/
def parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) : ℂ :=
  ∑ e∈Eenv,
    ∑ n∈Nenv,((w e n:ℝ):ℂ) *
      (∑ m∈K,∑ mp∈K.erase m,
        (α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m) *
        star (α mp*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n mp))

/-- TRUE original Parity(4.10) weighted Gram identity. The smooth
majorant weights are introduced on the positive Cauchy square BEFORE
splitting into m=m' diagonal and m≠m' complex offdiagonal.
Every source h=-2 signed H0 coefficient is kept exact, even for
weights >1. This prevents invalid signed-offdiagonal monotonicity. -/
theorem parity_original_historical_ungated_weighted_extended_square_diag_offdiag434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) :
    ((parityOriginalHistoricalUngatedWeightedExtendedSquare434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w:ℝ):ℂ) =
    ((parityOriginalHistoricalUngatedWeightedExtendedDiagonal434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w:ℝ):ℂ) +
      parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
        d L band slot δ ξ rho K Eenv Nenv α signed Y w := by
  let Q := Eenv
  let F : ℕ → ℕ → ℕ → ℂ := fun e n m =>
    α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m
  have hOne (e n : ℕ) :
      ((‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
      ((∑m∈K,‖F e n m‖^2:ℝ):ℂ) +
        ∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp) :=
    parity_original_historical_ungated_e_n_square_diag_offdiag434
      d L band slot δ ξ rho K α signed Y e n
  unfold parityOriginalHistoricalUngatedWeightedExtendedSquare434
    parityOriginalHistoricalUngatedWeightedExtendedDiagonal434
    parityOriginalHistoricalUngatedWeightedExtendedOffdiag434
  change ((∑e∈Q,∑n∈Nenv,w e n*‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
    ((∑e∈Q,∑n∈Nenv,w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) +
      (∑e∈Q,∑n∈Nenv,((w e n:ℝ):ℂ)*
        (∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp)))
  have hCastL : ((∑e∈Q,∑n∈Nenv,w e n*‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
      ∑e∈Q,∑n∈Nenv,((w e n*‖∑m∈K,F e n m‖^2:ℝ):ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Complex.ofReal_sum]
  have hCastD : ((∑e∈Q,∑n∈Nenv,w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) =
      ∑e∈Q,∑n∈Nenv,((w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Complex.ofReal_sum]
  rw [hCastL,hCastD]
  calc
    _ = ∑e∈Q,∑n∈Nenv,
      (((w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) +
        ((w e n:ℝ):ℂ)*(∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp))) := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      calc
        ((w e n*‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
          ((w e n:ℝ):ℂ)*((‖∑m∈K,F e n m‖^2:ℝ):ℂ) := by push_cast; rfl
        _ = ((w e n:ℝ):ℂ) *
          (((∑m∈K,‖F e n m‖^2:ℝ):ℂ) +
            (∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp))) := by
              rw [hOne e n]
        _ = (((w e n*(∑m∈K,‖F e n m‖^2):ℝ):ℂ) +
          ((w e n:ℝ):ℂ)*(∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp))) := by
            push_cast
            ring
    _ = _ := by simp_rw [Finset.sum_add_distrib]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedFixedEU -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Exact GENUINE Parity(4.10) ungated physical vStar/H0 source sum
at a fixed e and u. This is defined using only natural e|u
and vStar=ordinary_P(u/e), not e*vStar=ordinary_P(u) which
would artificially require original selected-Q e P-freeness. -/
def parityOriginalHistoricalUngatedFixedEU434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (e u : ℕ) : ℂ :=
  ∑vs∈parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
    parityOriginalHistoricalUngatedEVStarAtU434
      d L u signed band slot δ ξ rho e vs

/-- The natural ungated h=-2 Cauchy source at u>0 still has NO
term unless e is an integer divisor of u, for any arbitrary e.
No group-P primality assumption on e is needed. -/
theorem parity_original_historical_ungated_fixedEU_zero_unless_divisor434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (e u : ℕ)
    (hNot : ¬e∣u) :
    parityOriginalHistoricalUngatedFixedEU434
      d L band slot δ ξ rho signed e u=0 := by
  unfold parityOriginalHistoricalUngatedFixedEU434
  apply Finset.sum_eq_zero
  intro vs hvs
  unfold parityOriginalHistoricalUngatedEVStarAtU434
  simp only [and_false,ite_false]
  split_ifs with hh
  · exact (hNot hh.1).elim
  · rfl

/-- The genuine natural prime-slot vStar=ordinary_P(u/e) source
at fixed e,u contains at most ONE distinct selected vStar value,
including repeated original Q and P prime factors. This holds
for arbitrary e, even if it contains group primes. -/
theorem parity_original_historical_ungated_vStar_card_le_one434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (e u : ℕ) :
    ((parityOriginalReservedCartesianVStarSupport434 d L band slot δ).filter
      (fun vs=>e∣u ∧ vs=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (u/e))).card≤1 := by
  apply Finset.card_le_one.mpr
  intro vs hv vps hvp
  have hvEq := (Finset.mem_filter.mp hv).2.2
  have hvpEq := (Finset.mem_filter.mp hvp).2.2
  exact hvEq.trans hvpEq.symm

/-- Actual Parity h=-2 natural a_v(u/e) physical H0 coefficient on
the full post-Cauchy e domain obeys the SAME original W1/H0
divisor-moment upper bound as the selected-Q domain:

 ||Σ_{vs in original skipped B509 Q} [e|u & vs=ordinary_P(u/e)]
     a_v(vs,u/e)|| ≤ L^CW1 τ(u)

for ALL e>0,u>0, even with P-group prime divisors in e. This
is a new genuine analytic input needed to extend the positive
Cauchy diagonal without the earlier artificial prime-free-e gate.
It is proved using the source intrinsic H0 pointwise estimate,
the REAL positive-divisor u/e, τ(vStar)≤τ(u), singleton support,
and the native arbitrary-signed source a_v(v) bound. -/
theorem parity_eventually_original_historical_ungated_fixed_e_u_norm_le_tau434 :
    ∀ᶠ L : ℝ in atTop, 0<L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (signed : Bool) (e u : ℕ),0<e → 0<u →
      ‖parityOriginalHistoricalUngatedFixedEU434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho signed e u‖ ≤
      L^parityOriginalW1PolylogExponent434*(u.divisors.card:ℝ) := by
  filter_upwards [parity_eventually_original_intrinsic_signed_AV_polylog_tau434,
    eventually_gt_atTop (0:ℝ)] with L hAV hL
  refine ⟨hL,?_⟩
  intro band slot δ ξ rho signed e u he hu
  let d := sourceOriginalLiteralDepth 20 L
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let S := (parityOriginalReservedCartesianVStarSupport434 d L band slot δ).filter
    (fun vs=>e∣u ∧ vs=sourceOriginalOrdinaryPart P (u/e))
  let C : ℝ := L^parityOriginalW1PolylogExponent434*(u.divisors.card:ℝ)
  have hCard : S.card≤1 :=
    parity_original_historical_ungated_vStar_card_le_one434
      d L band slot δ e u
  have hC : 0≤C := mul_nonneg (Real.rpow_nonneg hL.le _) (Nat.cast_nonneg _)
  have hTerm (vs : ℕ) (hvs : vs∈S) :
      ‖parityOriginalIntrinsicSignedAV434
        d L band slot δ ξ 0 rho signed vs (u/e)‖ ≤ C := by
    obtain ⟨hDiv,hVs⟩ := (Finset.mem_filter.mp hvs).2
    have hU : u=e*(u/e) := (Nat.mul_div_cancel_left' hDiv).symm
    have hvPos : 0<u/e := by
      have hh := hu
      rw [hU] at hh
      exact Nat.pos_of_mul_pos_left hh
    have hVsPos : 0<vs := by
      rw [hVs]
      exact Nat.pos_of_ne_zero (parity_original_ordinary_part_nonzero434
        P (u/e) hvPos.ne')
    have hSplit := source_original_ordinary_times_P_part P (u/e) hvPos.ne'
    have hVsDivV : vs∣u/e := by
      rw [hVs]
      exact ⟨sourceOriginalPPrimePart P (u/e),hSplit.symm⟩
    have hVsDivU : vs∣u := by
      have hMul : vs ∣ e*(u/e) := dvd_mul_of_dvd_right hVsDivV e
      rw [←hU] at hMul
      exact hMul
    have hAV := hAV band slot δ ξ 0 rho signed vs (u/e) hVsPos
    have hTau : (vs.divisors.card:ℝ)≤(u.divisors.card:ℝ) := by
      exact_mod_cast b656_divisors_card_mono434 vs u hu.ne' hVsDivU
    exact hAV.trans (mul_le_mul_of_nonneg_left hTau (Real.rpow_nonneg hL.le _))
  have hSum :
      (∑vs∈S,‖parityOriginalIntrinsicSignedAV434
        d L band slot δ ξ 0 rho signed vs (u/e)‖) ≤ (S.card:ℝ)*C := by
    have hh := Finset.sum_le_card_nsmul S
      (fun vs=>‖parityOriginalIntrinsicSignedAV434
        d L band slot δ ξ 0 rho signed vs (u/e)‖) C hTerm
    simpa only [nsmul_eq_mul,Nat.cast_ofNat] using hh
  unfold parityOriginalHistoricalUngatedFixedEU434
    parityOriginalHistoricalUngatedEVStarAtU434
  change ‖∑vs∈parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
    if e∣u ∧ vs=sourceOriginalOrdinaryPart P (u/e) then
      parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vs (u/e)
    else 0‖ ≤ C
  rw [←Finset.sum_filter]
  change ‖∑vs∈S,parityOriginalIntrinsicSignedAV434
    d L band slot δ ξ 0 rho signed vs (u/e)‖ ≤ C
  calc
    _ ≤ ∑vs∈S,‖parityOriginalIntrinsicSignedAV434
      d L band slot δ ξ 0 rho signed vs (u/e)‖ := norm_sum_le _ _
    _ ≤ (S.card:ℝ)*C := hSum
    _ ≤ (1:ℝ)*C := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hCard) hC
    _ = C := one_mul _
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedDiagonalFibre -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Native exact original h=-2 Cauchy coefficient with NATURAL
a_v(u/e) at arbitrary e|u, no Pfree-e restriction: its true
u=m*n-2 is a singleton source fibre with the original B509 H0. -/
theorem parity_original_historical_ungated_Cauchy_ENM_eq_fixed_EU434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (Y e n m : ℕ) :
    parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m =
    ∑ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
      parityOriginalHistoricalUngatedFixedEU434 d L band slot δ ξ rho signed e u := by
  unfold parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
    parityOriginalHistoricalFixedMNUSupport434
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : 0 < m ∧ 0 < n ∧ m*n=u+2
  · simp only [if_pos h]
    rfl
  · simp only [if_neg h]


theorem parity_original_historical_ungated_ENM_norm_sq_eq_U434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (Y e n m : ℕ) :
    ‖parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖^2 =
    ∑ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
      ‖parityOriginalHistoricalUngatedFixedEU434 d L band slot δ ξ rho signed e u‖^2 := by
  rw [parity_original_historical_ungated_Cauchy_ENM_eq_fixed_EU434]
  exact parity_original_complex_singleton_sum_norm_sq434 _ _
    (parity_original_historical_fixed_MN_source_u_card_le_one434 Y m n)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedDiagonalFinite -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Genuine original Parity(4.10) positive diagonal for ANY odd-e
full Cauchy envelope, using the natural ungated a_v(u/e) source.
This includes e having a P-group prime factor, unlike the earlier
allocated-e positive diagonal. All original H0, W1, signs and
prime-power multiplicities remain physical. -/
def parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℝ :=
  ∑e∈Eenv,∑n∈Nenv,∑m∈K,
    ‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖^2

/-- Exact original *UNGATED* Parity(4.11) diagonal upper bound over
arbitrary expanded finite e and n domains by the genuine shifted
τ(u)^3 τ(u+2) moment. The source H0 norm bound is now valid for
ALL e|u, not only original selected-Q P-free e.
No factor #e or #K and no unsupported spectral cancellation. -/
theorem parity_original_historical_ungated_extended_diagonal_finite_tau_moment434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (A C : ℝ)
    (hA : 0≤A) (hC : 0≤C)
    (hα : ∀m∈K,‖α m‖≤A)
    (hPhysical : ∀ e u : ℕ, 0<u → 0<e →
      ‖parityOriginalHistoricalUngatedFixedEU434 d L band slot δ ξ rho signed e u‖ ≤
        C*(u.divisors.card:ℝ)) :
    parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
      d L band slot δ ξ rho K Eenv Nenv α signed Y ≤
      A^2*C^2*(∑u∈Finset.Ioc 0 Y,
        (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) := by
  let Q := Eenv
  let U := Finset.Ioc 0 Y
  let w : ℕ → ℝ := fun u => A^2*C^2*(u.divisors.card:ℝ)^2
  have hw (u : ℕ) (hu : u∈U) : 0≤w u := by
    dsimp [w]
    positivity
  have hEach (e n m : ℕ) (hm : m∈K) :
      ‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2 ≤
      ∑u∈parityOriginalHistoricalFixedMNUSupport434 Y m n,
        if e∣u then w u else 0 := by
    rw [norm_mul, mul_pow]
    rw [parity_original_historical_ungated_ENM_norm_sq_eq_U434]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have huPos : 0<u :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
    by_cases hdiv : e∣u
    · have hePos : 0<e := by
        rcases hdiv with ⟨t,ht⟩
        by_contra hn
        have he0 : e=0 := Nat.eq_zero_of_not_pos hn
        rw [he0,zero_mul] at ht
        omega
      have hv := hPhysical e u huPos hePos
      have hASq : ‖α m‖^2 ≤ A^2 :=
        (sq_le_sq₀ (norm_nonneg _) hA).mpr (hα m hm)
      have hCSq : ‖parityOriginalHistoricalUngatedFixedEU434
          d L band slot δ ξ rho signed e u‖^2 ≤
          (C*(u.divisors.card:ℝ))^2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Nat.cast_nonneg _))).mpr hv
      simp only [if_pos hdiv]
      calc
        _ ≤ A^2*(C*(u.divisors.card:ℝ))^2 :=
          mul_le_mul hASq hCSq (sq_nonneg _) (sq_nonneg _)
        _ = w u := by dsimp [w]; ring
    · have hz := parity_original_historical_ungated_fixedEU_zero_unless_divisor434
        d L band slot δ ξ rho signed e u hdiv
      simp [hz,hdiv]
  unfold parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
  change (∑ e∈Q,∑ n∈Nenv,∑ m∈K,
    ‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖^2) ≤ _
  calc
    _ ≤ ∑e∈Q,∑n∈Nenv,∑m∈K,
      ∑u∈parityOriginalHistoricalFixedMNUSupport434 Y m n,
        if e∣u then w u else 0 := by
          apply Finset.sum_le_sum
          intro e he
          apply Finset.sum_le_sum
          intro n hn
          apply Finset.sum_le_sum
          intro m hm
          exact hEach e n m hm
    _ = ∑u∈U,∑e∈Q,
      ∑z∈parityOriginalShiftTwoPositivePairFibre434 K Nenv u,
        if e∣u then w u else 0 :=
      parity_original_historical_diagonal_ENM_u_reindex434 Q K Nenv Y w
    _ ≤ ∑u∈U,((u.divisors.card:ℝ)*((u+2).divisors.card:ℝ))*w u :=
      parity_original_historical_actual_e_and_pair_divisor_count434 Q K Nenv Y w hw
    _ = A^2*C^2*(∑u∈U,
      (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        dsimp [w]
        ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedDiagonalPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- True ungated original Parity(4.10)--(4.11) full odd-e/n
positive diagonal is bounded for arbitrary e including all P-bad
e whose a_v(u/e) remains a valid natural prime-slot coefficient.
This comparison is real and NONNEGATIVE, never a signed subset. -/
theorem parity_original_historical_ungated_extended_diagonal_weight_le434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (w : ℕ → ℕ → ℝ) (C : ℝ)
    (hw : ∀e∈Eenv,∀n∈Nenv,w e n ≤ C) :
    parityOriginalHistoricalUngatedWeightedExtendedDiagonal434
      d L band slot δ ξ rho K Eenv Nenv α signed Y w ≤
    C*parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
      d L band slot δ ξ rho K Eenv Nenv α signed Y := by
  let F : ℕ → ℕ → ℝ := fun e n =>
    ∑m∈K,‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖^2
  have hF : ∀e n, 0≤F e n := by
    intro e n
    apply Finset.sum_nonneg
    intro m hm
    exact sq_nonneg _
  have hS : (∑e∈Eenv,∑n∈Nenv,w e n*F e n) ≤
      ∑e∈Eenv,∑n∈Nenv,C*F e n := by
    apply Finset.sum_le_sum
    intro e he
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right (hw e he n hn) (hF e n)
  unfold parityOriginalHistoricalUngatedWeightedExtendedDiagonal434
    parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
  change (∑e∈Eenv,∑n∈Nenv,w e n*F e n) ≤
    C*(∑e∈Eenv,∑n∈Nenv,F e n)
  calc
    _ ≤ ∑e∈Eenv,∑n∈Nenv,C*F e n := hS
    _ = C*(∑e∈Eenv,∑n∈Nenv,F e n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]

/-- UNIVERSAL original Parity (4.11) unconditional physical shifted
τ(u)^3 τ(u+2) bound for arbitrary finite e,n supports after
PRE-GRAM Cauchy expansion. In particular, extending the selected
Q-e support to ALL odd e does NOT introduce any factor E, Q-depth,
or more than the original fixed divisor exponent:

  D_full(e,n) ≤ Acoef² exp L L^(2 C_W1+256).

This is proved from the native ORIGINAL fixed-e,u full H0 bound
and the genuine original shifted eighth divisor moment. It does
not require e to be selected-Q or the original n-dyad. -/
theorem parity_eventually_original_historical_ungated_extended_diagonal_polylog434 :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧
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
        K Eenv Nenv α signed ⌊2*Real.exp L⌋₊ ≤
        Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+256) := by
  filter_upwards [parity_eventually_original_historical_ungated_fixed_e_u_norm_le_tau434,
    eventually_ge_atTop ((3:ℝ)^256)] with L hPhys hL
  refine ⟨hL,?_⟩
  intro band slot δ ξ rho K Eenv Nenv α signed Acoef hAcoef hα
  let C : ℝ := L^parityOriginalW1PolylogExponent434
  have hLp : 0<L := by nlinarith [hL]
  have hC : 0≤C := Real.rpow_nonneg hLp.le _
  have hFixed (e u : ℕ) (hu : 0<u) (he : 0<e) :
      ‖parityOriginalHistoricalUngatedFixedEU434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho signed e u‖ ≤
        C*(u.divisors.card:ℝ) := by
    simpa only [parityOriginalHistoricalUngatedFixedEU434,C] using
      (hPhys.2 band slot δ ξ rho signed e u he hu)
  have hFinite := parity_original_historical_ungated_extended_diagonal_finite_tau_moment434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
    K Eenv Nenv α signed ⌊2*Real.exp L⌋₊
    Acoef C hAcoef hC hα hFixed
  have hMoment := parity_original_shift_two_tau_cube_moment_original_x_scale434 L hL
  calc
    _ ≤ Acoef^2*C^2*(∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
      (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) := hFinite
    _ ≤ Acoef^2*C^2*(Real.exp L*L^256) :=
      mul_le_mul_of_nonneg_left hMoment (mul_nonneg (sq_nonneg _) (sq_nonneg _))
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

/-- The ACTUAL original dyadic SOURCE η_e,L η_n positive full
odd e,n Cauchy diagonal is bounded with the precise fixed exponent
2 C_W1+344 after the legitimate sparse-support enlargement:

  D_full_odd(e,n;eta_e eta_n) ≤ 2 Acoef² exp L L^(2CW1+344).

This remains valid for ALL e∈odd≤2E and ALL n≤3V,
not only original selected e and n dyads, and for BOTH signed
ε branches. Neither the target Fourier precision nor K0 affects
the fixed diagonal exponent. The source 4.17 restricted complex
offdiagonal is NOT bounded by this theorem. -/
theorem parity_eventually_original_historical_ungated_full_odd_diagonal_polylog434 :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (E V rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      parityOriginalHistoricalUngatedWeightedExtendedDiagonal434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K (parityOriginalHistoricalFullOddEEnvelope434 E)
          (parityOriginalHistoricalFullNEnvelope434 V)
          α signed ⌊2*Real.exp L⌋₊
          (parityOriginalHistoricalDyadicEtaWeight434 L E V hLw) ≤
      2*Acoef^2*Real.exp L*
        L^(2*parityOriginalW1PolylogExponent434+344) := by
  filter_upwards [parity_eventually_original_historical_ungated_extended_diagonal_polylog434,
    eventually_ge_atTop (8:ℝ)] with L hDiag hLw
  refine ⟨hDiag.1,hLw,?_⟩
  intro hL band slot δ ξ E V rho K α signed Acoef hA hα
  have hLp : 0<L := by linarith
  let D := parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
      (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V) α signed ⌊2*Real.exp L⌋₊
  have hBound := parity_original_historical_ungated_extended_diagonal_weight_le434
      (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K
      (parityOriginalHistoricalFullOddEEnvelope434 E)
      (parityOriginalHistoricalFullNEnvelope434 V) α signed ⌊2*Real.exp L⌋₊
      (parityOriginalHistoricalDyadicEtaWeight434 L E V hL) (2*L^(88:ℝ))
      (by intro e he n hn; exact (parity_original_historical_dyadic_eta_weight_polylog434 L E V hL e n).2)
  have hD := hDiag.2 band slot δ ξ rho K
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

/-! ## OriginalHistoricalUngatedTypeIIPrecursor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- CORRECTED ORIGINAL Parity(4.10)--(4.13) source TypeII precursor:

 |A_original_selected_Q|² ≤
  (Σ_{original selected-Q e,n} |a_e β_n|²) ·
    [ 2 Acoef² exp(L) L^(2CW1+344)
       + ||OD_ungated(all odd e, all n)|| ].

CRUCIAL: OD_ungated is the REAL full post-Cauchy signed complex
correlation obtained by first replacing the original selected-Q
gate `e*vStar=ordinary_P(u)` with its mathematically equal natural
`e|u, vStar=ordinary_P(u/e)` on original P-free e, THEN legally
enlarging the POSITIVE Cauchy square to all odd e,n, THEN
expanding the Gram. Thus e containing primes from original P
is INCLUDED in the second factor just as the literal manuscript
Parity(4.10). This avoids the actual support mismatch in the earlier
P-gated expanded square. The original B509 H0, h=-2, signed ε=1/E,
W1, source b629 alpha and prime-power multiplicities are exact.

The full ungated offdiagonal has NOT YET been Fourier-reindexed
onto the unrestricted Parity(4.17) two-prime-slot correlation. NO
analytic saving for its norm is assumed here, and neither TypeII
nor Green64 is declared proved. -/
theorem parity_eventually_original_ungated_full_odd_Cauchy_diag_offdiag434 :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (E V rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0<E → 0<V →
      (∀n∈J,V≤(n:ℝ) ∧ (n:ℝ)≤2*V) →
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      let Y : ℕ := ⌊2*Real.exp L⌋₊
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
    parity_eventually_original_historical_ungated_full_odd_diagonal_polylog434]
    with L hCauchy hDiagonal
  refine ⟨hDiagonal.1,hDiagonal.2.1,?_⟩
  intro hLw band slot δ ξ E V rho K J α β signed Acoef
    hE hV hNRange hAcoef hα
  dsimp only
  let Y : ℕ := ⌊2*Real.exp L⌋₊
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
    hDiagonal.2.2 hLw band slot δ ξ E V rho K α signed Acoef hAcoef hα
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

/-! ## OriginalHistoricalUngatedGcd -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- ORIGINAL Parity(4.13) key arithmetical fact on the CORRECTED
UNGATED post-Cauchy domain: e is odd and m*n=e*v+2, so
  gcd(e,n)=1.
This does NOT need e to be prime, Q-selected or free of P-group
primes; the shift b=2 supplies the necessary coprimality.
It is the precise Euclidean input to recover the source k from
all legitimate ungated original (e,n,m,m') pairs. -/
theorem parity_original_historical_ungated_odd_e_coprime_shared_n434
    (e n m v : ℕ) (he : Odd e)
    (hMN : m*n=e*v+2) : e.Coprime n := by
  let g := Nat.gcd e n
  have hGE : g∣e := Nat.gcd_dvd_left e n
  have hGN : g∣n := Nat.gcd_dvd_right e n
  have hA : g∣m*n := dvd_mul_of_dvd_right hGN m
  have hB : g∣e*v := dvd_mul_of_dvd_left hGE v
  have h2 : g∣2 := by
    have hD := Nat.dvd_sub hA hB
    have hEq : m*n-e*v=2 := by omega
    rwa [hEq] at hD
  have hG2 : g.Coprime 2 :=
    Nat.Coprime.of_dvd hGE (dvd_refl 2) he.coprime_two_right
  have hOne := hG2.eq_one_of_dvd h2
  exact Nat.coprime_iff_gcd_eq_one.mpr hOne

/-- The source shared n is coprime to e on BOTH genuine h=-2
endpoints; the second equality is not needed for coprimality.
This is the correct Parity original 4.13 structural fact under the
ungated natural a_v(u/e) and all-odd-e post-Cauchy extension. -/
theorem parity_original_historical_ungated_two_endpoint_coprime_n434
    (e n m mp v vp : ℕ) (he : Odd e)
    (hMN : m*n=e*v+2)
    (hMpN : mp*n=e*vp+2) :
    e.Coprime n :=
  parity_original_historical_ungated_odd_e_coprime_shared_n434
    e n m v he hMN
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedDeterminant -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- EXACT ORIGINAL Parity (4.13) UNGATED arithmetic parametrization:
At both h=-2 physical endpoints, assume only odd e>0 and the
natural ungated factor identities
   m*n=e*v+2,   m'*n=e*v'+2.

Then e and n are automatically coprime. Thus e divides the
SIGNED integer m'-m, producing a UNIQUE integer k with
  m'-m=e*k,  v'-v=k*n,  m'*v+2*k=m*v'.

In particular, no artificial requirement that e be free of the
original P-group primes enters the genuine Cauchy offdiagonal
parametrization. This is the required first step toward the FULL
Parity(4.17) pair-domain equivalence from the honest ungated (4.10)
positive square. The original shared n and shift h=-2 are literal.
No Fourier or cancellation estimate is assumed. -/
theorem parity_original_historical_ungated_two_endpoint_signed_k_exists434
    (e n m mp v vp : ℕ) (he : Odd e)
    (hMN : m*n=e*v+2) (hMpN : mp*n=e*vp+2) :
    ∃k : ℤ,
      (mp:ℤ)-(m:ℤ)=(e:ℤ)*k ∧
      (vp:ℤ)-(v:ℤ)=k*(n:ℤ) ∧
      (mp:ℤ)*(v:ℤ)+2*k=(m:ℤ)*(vp:ℤ) := by
  have hCop := parity_original_historical_ungated_odd_e_coprime_shared_n434
    e n m v he hMN
  have hCoprimeInt : IsCoprime (e:ℤ) (n:ℤ) := hCop.isCoprime
  have hMNInt : (m:ℤ)*(n:ℤ)=(e:ℤ)*(v:ℤ)+2 := by exact_mod_cast hMN
  have hMpNInt : (mp:ℤ)*(n:ℤ)=(e:ℤ)*(vp:ℤ)+2 := by exact_mod_cast hMpN
  have hProduct : ((mp:ℤ)-(m:ℤ))*(n:ℤ) =
      (e:ℤ)*((vp:ℤ)-(v:ℤ)) := by
    linear_combination hMpNInt - hMNInt
  have hDivProd : (e:ℤ) ∣ (n:ℤ)*((mp:ℤ)-(m:ℤ)) :=
    ⟨(vp:ℤ)-(v:ℤ),by rw [mul_comm]; exact hProduct⟩
  have hDiv : (e:ℤ) ∣ (mp:ℤ)-(m:ℤ) :=
    hCoprimeInt.dvd_of_dvd_mul_left hDivProd
  obtain ⟨k,hDet⟩ := hDiv
  have hDet' : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k := hDet
  have hePos : 0 < e := he.pos
  have heInt : (e:ℤ)≠0 := by exact_mod_cast hePos.ne'
  have hVShift : (vp:ℤ)-(v:ℤ)=k*(n:ℤ) := by
    have hh : (e:ℤ)*(((vp:ℤ)-(v:ℤ))-k*(n:ℤ))=0 := by
      linear_combination -hProduct + (n:ℤ)*hDet'
    have hZero := (mul_eq_zero.mp hh).resolve_left heInt
    exact sub_eq_zero.mp hZero
  have hShift : (mp:ℤ)*(v:ℤ)+2*k=(m:ℤ)*(vp:ℤ) := by
    linear_combination -k*hMNInt - (m:ℤ)*hVShift + (v:ℤ)*hDet'
  exact ⟨k,hDet',hVShift,hShift⟩

/-- The original signed canonical integer k is not zero when the
two genuine cofactor rows m,m' differ. This is now established on
the actual newly UNGATED source for all odd e, without a P-free
or selected-Q assumption, including physical shifted negative k. -/
theorem parity_original_historical_ungated_two_endpoint_nonzero_k434
    (e n m mp v vp : ℕ) (he : Odd e)
    (hne : m≠mp)
    (hMN : m*n=e*v+2) (hMpN : mp*n=e*vp+2) :
    ∃k : ℤ, k≠0 ∧
      (mp:ℤ)-(m:ℤ)=(e:ℤ)*k ∧
      (vp:ℤ)-(v:ℤ)=k*(n:ℤ) ∧
      (mp:ℤ)*(v:ℤ)+2*k=(m:ℤ)*(vp:ℤ) := by
  obtain ⟨k,hDet,hVp,hShift⟩ :=
    parity_original_historical_ungated_two_endpoint_signed_k_exists434
      e n m mp v vp he hMN hMpN
  have hk : k≠0 := by
    intro hk0
    rw [hk0,mul_zero] at hDet
    have hh : (mp:ℤ)=(m:ℤ) := by omega
    exact hne (by exact_mod_cast hh.symm)
  exact ⟨k,hk,hDet,hVp,hShift⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedB633TwoCores -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- FORWARD ORIGINAL Parity (4.13)--(4.17) true source n-to-two-core
arithmetic under the CORRECTED ungated all-odd-e physical source.
If the real h=-2 endpoints have m*n=e*v+2,m'*n=e*v'+2,
cofactors m,m' free of original P-group primes, and m≠m', then
there is a nonzero signed k with m'-m=e*k and z=m'v,
z+2k=mv'. The two B633 ordinary-part divisor cores are EXACT:

 ordinary_P(z)=m'*ordinary_P(v),
 ordinary_P(z+2k)=m*ordinary_P(v').

This theorem DOES NOT require e to be P-group-prime-free; in
particular it covers the legitimate extra e terms included by
extending the new positive UNGATED Parity(4.10) square.
No source spectral saving or H0 coefficient support assumed. -/
theorem parity_original_historical_ungated_two_core_forward434
    (P : Finset ℕ) (e n m mp v vp : ℕ)
    (he : Odd e) (hne : m≠mp)
    (hm : 0 < m) (hmp : 0 < mp) (hv : 0 < v) (hvp : 0 < vp)
    (hMFree : ∀p∈P,¬p∣m) (hMpFree : ∀p∈P,¬p∣mp)
    (hMN : m*n=e*v+2) (hMpN : mp*n=e*vp+2) :
    ∃k : ℤ,
      k≠0 ∧ (mp:ℤ)-(m:ℤ)=(e:ℤ)*k ∧
      ((mp*v:ℕ):ℤ)+2*k=(m*vp:ℕ) ∧
      sourceOriginalOrdinaryPart P (mp*v)=mp*sourceOriginalOrdinaryPart P v ∧
      sourceOriginalOrdinaryPart P (m*vp)=m*sourceOriginalOrdinaryPart P vp ∧
      mp ∈ (sourceOriginalOrdinaryPart P (mp*v)).divisors ∧
      m ∈ (sourceOriginalOrdinaryPart P (m*vp)).divisors := by
  obtain ⟨k,hk,hDet,hShiftV,hShift⟩ :=
    parity_original_historical_ungated_two_endpoint_nonzero_k434
      e n m mp v vp he hne hMN hMpN
  have hOrdZ := parity_original_ordinary_part_mul_prime_free434
    P mp v hmp.ne' hv.ne' hMpFree
  have hOrdZp := parity_original_ordinary_part_mul_prime_free434
    P m vp hm.ne' hvp.ne' hMFree
  have hOrdZ0 : sourceOriginalOrdinaryPart P (mp*v)≠0 :=
    parity_original_ordinary_part_nonzero434 P (mp*v) (Nat.mul_ne_zero hmp.ne' hv.ne')
  have hOrdZp0 : sourceOriginalOrdinaryPart P (m*vp)≠0 :=
    parity_original_ordinary_part_nonzero434 P (m*vp) (Nat.mul_ne_zero hm.ne' hvp.ne')
  have hDivZ : mp∈(sourceOriginalOrdinaryPart P (mp*v)).divisors :=
    Nat.mem_divisors.mpr ⟨by rw [hOrdZ]; exact dvd_mul_right _ _,hOrdZ0⟩
  have hDivZp : m∈(sourceOriginalOrdinaryPart P (m*vp)).divisors :=
    Nat.mem_divisors.mpr ⟨by rw [hOrdZp]; exact dvd_mul_right _ _,hOrdZp0⟩
  have hShiftNat : ((mp*v:ℕ):ℤ)+2*k=(m*vp:ℕ) := by
    simpa only [Nat.cast_mul] using hShift
  exact ⟨k,hk,hDet,hShiftNat,hOrdZ,hOrdZp,hDivZ,hDivZp⟩

/-- REVERSE ORIGINAL Parity(4.17) TWO PRIME-SLOT CORRELATION CARRIER
into the CORRECTED ungated Parity(4.10) source. Given positive z,z+2k
and B633 ordinary-part divisor m' and m, genuine determinant
m'-m=e*k with e>0, small k coprime to rough m, and P-free
rough cofactors m,m', there exist TRUE positive v,v' and ONE
shared integer n with the original h=-2 endpoints, and unique
literal natural B509 prime-slot arguments vStar=ordinary_P(v),
vStar'=ordinary_P(v'):

  ordinary_P(z)=m'*vStar,
  ordinary_P(z+2k)=m*vStar'.

CRUCIALLY, the source-reconstructed e MAY CONTAIN ANY P-prime
powers. This is valid because the physical e*vStar=ordinary_P(u)
shortcut was replaced by the correct ungated e|u and vStar=
ordinary_P(u/e), BEFORE positive Cauchy enlargement. Further
original actual n/u source windows, B509 reserved H0 support and
ψ_Z smoothing are separate conditions and remain to be addressed;
this theorem does not claim the analytic signed 4.17 estimate. -/
theorem parity_original_historical_ungated_two_core_reverse434
    (P : Finset ℕ) (m mp e z zp : ℕ) (k : ℤ)
    (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z) (hzp : 0 < zp)
    (hMFree : ∀p∈P,¬p∣m) (hMpFree : ∀p∈P,¬p∣mp)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hShift : (z:ℤ)+2*k=(zp:ℤ))
    (hCop : m.Coprime k.natAbs)
    (hDivMp : mp∣sourceOriginalOrdinaryPart P z)
    (hDivM : m∣sourceOriginalOrdinaryPart P zp) :
    ∃v vp n vs vps : ℕ,
      0<v ∧ 0<vp ∧ 0<n ∧ 0<vs ∧ 0<vps ∧
      z=mp*v ∧ zp=m*vp ∧
      m*n=e*v+2 ∧ mp*n=e*vp+2 ∧
      vs=sourceOriginalOrdinaryPart P v ∧
      vps=sourceOriginalOrdinaryPart P vp ∧
      sourceOriginalOrdinaryPart P z=mp*vs ∧
      sourceOriginalOrdinaryPart P zp=m*vps := by
  obtain ⟨v,vp,n,hv,hvp,hZ,hZp,hMN,hMpN⟩ :=
    parity_original_historical_reverse_417_divisor_pair_to_source_n434
      P m mp e z zp k hm hmp hz hzp hDet hShift hCop hDivMp hDivM
  let vs := sourceOriginalOrdinaryPart P v
  let vps := sourceOriginalOrdinaryPart P vp
  have hvs : 0<vs := Nat.pos_of_ne_zero
    (parity_original_ordinary_part_nonzero434 P v hv.ne')
  have hvps : 0<vps := Nat.pos_of_ne_zero
    (parity_original_ordinary_part_nonzero434 P vp hvp.ne')
  have hn : 0<n := by
    have hh : 0 < m*n := by rw [hMN]; omega
    exact Nat.pos_of_mul_pos_left hh
  have hOrdZ := parity_original_ordinary_part_mul_prime_free434
    P mp v hmp.ne' hv.ne' hMpFree
  have hOrdZp := parity_original_ordinary_part_mul_prime_free434
    P m vp hm.ne' hvp.ne' hMFree
  refine ⟨v,vp,n,vs,vps,hv,hvp,hn,hvs,hvps,hZ,hZp,
    hMN,hMpN,rfl,rfl,?_,?_⟩
  · rw [hZ]
    exact hOrdZ
  · rw [hZp]
    exact hOrdZp
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedPairB633 -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- EXACT UNGATED original Parity (4.16)--(4.17) signed h=-2 B633
TWO-PRIME-SLOT PHYSICAL PAIR IDENTITY for any positive v,v',m,m',
INCLUDING physical e with original P-group factors.

The original natural a_v(v)=v^(iρ) W1(v)ε(v) H0(ordinary_P(v))
coefficient and its conjugate, multiplied by original χ(m') conjχ(m)
and the THREE separated imaginary powers m,m',z=m'v, equal the
LITERAL Parity B633 original `parityOriginalHistoricalB633PhysicalPairTerm434`
with the SAME α_m, α_mp, b629 fine source H0 residual sigma=0,
full P multiplicities, signs and 2π-free unnormalized power parameters.

Unlike earlier equality requiring source e*vStar=ordinary_P(u),
this identity ONLY requires positive actual natural v/v' and their
P-ordinary parts. It is exactly the coefficient that can be used
inside the corrected ungated full odd-e/n Cauchy offdiagonal.
No 4.17 correlation cancellation bound assumed. -/
theorem parity_original_historical_ungated_intrinsic_pair_eq_B633434
    (d : ℕ) (L : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (m mp v vp : ℕ) (hm : 0 < m) (hmp : 0 < mp)
    (hv : 0 < v) (hvp : 0 < vp)
    (rho xi1 xi2 xi3 : ℝ) (signed : Bool) :
    let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
    let z := mp*v
    let zp := m*vp
    let vs := sourceOriginalOrdinaryPart P v
    let vps := sourceOriginalOrdinaryPart P vp
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
    chi (mp:ZMod q)*star (chi (m:ZMod q)) *
      imaginaryPower m xi1*imaginaryPower mp xi2*imaginaryPower z xi3 *
      ((alpha m*parityOriginalIntrinsicSignedAV434
          d L band slot δ ξ 0 rho signed vs v) *
        star (alpha mp*parityOriginalIntrinsicSignedAV434
          d L band slot δ ξ 0 rho signed vps vp)) =
    parityOriginalHistoricalB633PhysicalPairTerm434 L rho xi1 xi2 xi3 signed
      alpha F.residual q chi F.lo F.hi m mp z zp := by
  dsimp only
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let vs := sourceOriginalOrdinaryPart P v
  let vps := sourceOriginalOrdinaryPart P vp
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
  have hvs : 0 < vs := Nat.pos_of_ne_zero
    (parity_original_ordinary_part_nonzero434 P v hv.ne')
  have hvps : 0 < vps := Nat.pos_of_ne_zero
    (parity_original_ordinary_part_nonzero434 P vp hvp.ne')
  have hDivZ : (mp*v)/mp=v := Nat.mul_div_cancel_left v hmp
  have hDivZp : (m*vp)/m=vp := Nat.mul_div_cancel_left vp hm
  have hPair := parity_original_historical_intrinsic_signed_pair_eq_B633434
    d L band slot δ ξ K alpha q chi m mp vs vps v vp
    hvs hvps hv hvp rho signed
  dsimp only at hPair
  unfold parityOriginalHistoricalB633PhysicalPairTerm434
  rw [hDivZ,hDivZp]
  dsimp only [vs,vps,F]
  rw [hPair]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedPhysicalCarrier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- True NEW ungated h=-2 Parity4.10 physical pair carrier at one
full-odd e, shared n, and cofactor m,m'. Both original positive
u=m*n-2 and u'=m'*n-2 lie in the actual u≤Y source range,
and e divides both, while the NATURAL a_v(v) reserved B509 source
prime-slot values ordinary_P(u/e),ordinary_P(u'/e) belong to the
actual original native H0 carrier. No e Pfree group restriction.
This is the physically correct finite support after expanding the
natural ungated Cauchy square, not the old source Q-allocation gate. -/
def parityOriginalHistoricalUngatedPhysicalValidN434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) : Prop :=
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let V := parityOriginalReservedCartesianVStarSupport434 d L band slot δ
  ∃u∈parityOriginalHistoricalFixedMNUSupport434 Y m n,
    ∃up∈parityOriginalHistoricalFixedMNUSupport434 Y mp n,
      e∣u ∧ e∣up ∧
      sourceOriginalOrdinaryPart P (u/e)∈V ∧
      sourceOriginalOrdinaryPart P (up/e)∈V

/-- A REAL original full-odd-e post-Cauchy source event in the
correct UNGATED carrier has positive natural v=u/e, v'=u'/e,
with exact original h=-2 endpoints m*n=e*v+2 and m'*n=e*v'+2.
No Pprime-free condition on e. The reserved original H0 arguments
vs=ordinary_P(v),vps=ordinary_P(v') are truly in their B509 slots.
This is the exact source hypothesis needed for Parity4.13 signed k and
the original B633 two prime-slot convolution at z=m'v. -/
theorem parity_original_historical_ungated_physical_valid_n_real_endpoints434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : 0 < e)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n) :
    ∃v vp vs vps : ℕ,
      0 < v ∧ 0 < vp ∧
      m*n=e*v+2 ∧ mp*n=e*vp+2 ∧
      vs=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) v ∧
      vps=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) vp ∧
      vs∈parityOriginalReservedCartesianVStarSupport434 d L band slot δ ∧
      vps∈parityOriginalReservedCartesianVStarSupport434 d L band slot δ := by
  obtain ⟨u,hu,up,hup,hDiv,hDivp,hVS,hVPS⟩ := hValid
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let v := u/e
  let vp := up/e
  let vs := sourceOriginalOrdinaryPart P v
  let vps := sourceOriginalOrdinaryPart P vp
  have huPos : 0 < u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hupPos : 0 < up := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
  have hMN0 : m*n=u+2 := (Finset.mem_filter.mp hu).2.2.2
  have hMpN0 : mp*n=up+2 := (Finset.mem_filter.mp hup).2.2.2
  have hUEq : u=e*v := by
    dsimp [v]
    exact (Nat.mul_div_cancel_left' hDiv).symm
  have hUPEq : up=e*vp := by
    dsimp [vp]
    exact (Nat.mul_div_cancel_left' hDivp).symm
  have hv : 0 < v := by
    have hh := huPos
    rw [hUEq] at hh
    exact Nat.pos_of_mul_pos_left hh
  have hvp : 0 < vp := by
    have hh := hupPos
    rw [hUPEq] at hh
    exact Nat.pos_of_mul_pos_left hh
  have hMN : m*n=e*v+2 := by rw [hMN0,hUEq]
  have hMpN : mp*n=e*vp+2 := by rw [hMpN0,hUPEq]
  exact ⟨v,vp,vs,vps,hv,hvp,hMN,hMpN,rfl,rfl,hVS,hVPS⟩

/-- The true CORRECTED natural ungated original Cauchy (4.10)
physical source two-endpoint event has EXACT canonical nonzero
signed Parity (4.13) k=(m'-m)/e, with actual z=m'(mn-2)/e>0,
positive z+2k=m*(m'n-2)/e, both original B509 vStars, and
NO requirement that e have no original P-group factors.
This bridges the newly source-correct Cauchy event to the real
unrestricted Parity(4.17) pair arithmetic, without yet asserting
the low-frequency analytic correlation saving. -/
theorem parity_original_historical_ungated_physical_valid_k_z434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hne : m≠mp)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n) :
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let zp := ((z:ℤ)+2*k).toNat
    k≠0 ∧ 0 < z ∧ 0 < zp ∧
      (mp:ℤ)-(m:ℤ)=(e:ℤ)*k ∧
      (z:ℤ)+2*k=(zp:ℤ) := by
  dsimp only
  obtain ⟨v,vp,vs,vps,hv,hvp,hMN,hMpN,hvs,hvps,hS,hSp⟩ :=
    parity_original_historical_ungated_physical_valid_n_real_endpoints434
      d L band slot δ Y e m mp n he.pos hValid
  have hK := parity_original_historical_ungated_two_endpoint_nonzero_k434
    e n m mp v vp he hne hMN hMpN
  obtain ⟨k,hk,hDet,hVShift,hShift⟩ := hK
  have hKCan := parity_original_historical_physical_k_eq_quotient434
    e m mp he.pos k hDet
  have hU : m*n-2=e*v := by omega
  have hV : parityOriginalHistoricalCanonicalV434 e m n=v := by
    unfold parityOriginalHistoricalCanonicalV434
    rw [hU]
    exact Nat.mul_div_cancel_left v he.pos
  have hz : parityOriginalHistoricalCanonicalZ434 e m mp n=mp*v := by
    unfold parityOriginalHistoricalCanonicalZ434
    rw [hV]
  have hmppos : 0 < mp := by
    obtain ⟨u,hu,up,hup,hdiv,hdivp,hvs,hvps⟩ := hValid
    exact (Finset.mem_filter.mp hup).2.1
  have hmpos : 0 < m := by
    obtain ⟨u,hu,up,hup,hdiv,hdivp,hvs,hvps⟩ := hValid
    exact (Finset.mem_filter.mp hu).2.1
  have hzpos : 0 < parityOriginalHistoricalCanonicalZ434 e m mp n := by
    rw [hz]
    exact Nat.mul_pos hmppos hv
  have hzp : ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℤ)+
      2*parityOriginalHistoricalOffdiagK434 e m mp).toNat=m*vp := by
    rw [hz,hKCan]
    have hh : ((mp*v:ℕ):ℤ)+2*k=((m*vp:ℕ):ℤ) := by
      simpa only [Nat.cast_mul] using hShift
    have hhToNat := congrArg Int.toNat hh
    simpa only [← Nat.cast_mul,Int.toNat_natCast] using hhToNat
  have hzpPos : 0 < ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℤ)+
      2*parityOriginalHistoricalOffdiagK434 e m mp).toNat := by
    rw [hzp]
    exact Nat.mul_pos hmpos hvp
  refine ⟨?_,hzpos,hzpPos,?_,?_⟩
  · rw [hKCan]
    exact hk
  · rw [hKCan]
    exact hDet
  · calc
      (parityOriginalHistoricalCanonicalZ434 e m mp n:ℤ)+
          2*parityOriginalHistoricalOffdiagK434 e m mp =
          ((mp*v:ℕ):ℤ)+2*k := by rw [hz,hKCan]
      _ = ((m*vp:ℕ):ℤ) := by simpa only [Nat.cast_mul] using hShift
      _ = (((parityOriginalHistoricalCanonicalZ434 e m mp n:ℤ)+
          2*parityOriginalHistoricalOffdiagK434 e m mp).toNat:ℤ) :=
            (congrArg (fun t:ℕ => (t:ℤ)) hzp).symm
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedCharacterMask -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- **FULL odd-e original Parity (2.6) character mask** after
legitimate original (4.10) positive-Cauchy expansion to ALL odd e.

For every nonzero actual constructed smooth η_e,L at the physical
e, ANY odd e (not necessarily selected Q) with BOTH genuine UNGATED B509 h=-2 physical endpoints, fine b629 alpha_m,alpha_mp ≠0 and original
m,m' dyad admits a nonzero signed canonical k with
|k|<L^(K0+89), k EVEN, and EXACT original (2.6) character
projector value 1:
  Σχ cχ χ(m') conjχ(m)=1.

The new K0+89 (rather than source sparse K0+88) precisely pays the
factor 2 width of the moving η_e positive-buffer support.
Rough cofactor m,m' makes χ units mod 2|k|; no assumption about
a sparse selected e, a made-up character modulus or spectral 4.17
saving. Full original physical e|u,e|u', natural B509 H0 and signed negative k
are preserved. -/
theorem parity_eventually_original_ungated_full_odd_smooth_fine_mask434
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
      ∀ (e m mp n : ℕ),
      Odd e → m≠mp →
      U≤(m:ℝ) → (m:ℝ)<2*U →
      U≤(mp:ℝ) → (mp:ℝ)<2*U →
      parityOriginalHistoricalDyadicEtaEAtLReal434 L hL ((e:ℝ)/E)≠0 →
      parityOriginalHistoricalUngatedPhysicalValidN434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m mp n →
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
    e m mp n he hNe hmLo hmHi hmpLo hmpHi hEta hValid hAm hAmp
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  have hRoughM : sourceD20Rough (Real.exp (Real.sqrt L)) m :=
    hRough prime lFine uFine hl hFineLow K m hAm
  have hRoughMp : sourceD20Rough (Real.exp (Real.sqrt L)) mp :=
    hRough prime lFine uFine hl hFineLow K mp hAmp
  have hPhysical := parity_original_historical_ungated_physical_valid_k_z434
    (sourceOriginalLiteralDepth 20 L) L band slot δ
    ⌊2*Real.exp L⌋₊ e m mp n he hNe hValid
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

/-! ## OriginalHistoricalUngatedPhysicalSingleton -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- The corrected original Parity(4.10) natural a_v(u/e) B509
source H0 coefficient at a positive source endpoint u=m*n-2
is an EXACT SINGLE genuine term when e|u and the true reserved
prime-slot ordinary_P(u/e) is in the original skipped-Q carrier.
No Pfree-e hypothesis and no synthetic reserved prime. -/
theorem parity_original_historical_ungated_fixedEU_eq_physical_AV434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (e u : ℕ)
    (hDiv : e∣u)
    (hVS : sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (u/e) ∈
      parityOriginalReservedCartesianVStarSupport434 d L band slot δ) :
    parityOriginalHistoricalUngatedFixedEU434
      d L band slot δ ξ rho signed e u =
    parityOriginalIntrinsicSignedAV434
      d L band slot δ ξ 0 rho signed
      (sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (u/e)) (u/e) := by
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let vs := sourceOriginalOrdinaryPart P (u/e)
  let V := parityOriginalReservedCartesianVStarSupport434 d L band slot δ
  have hFilter : V.filter (fun w => e∣u ∧ w=vs) = {vs} := by
    ext w
    constructor
    · intro hw
      exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hw).2.2
    · intro hw
      have hEq := Finset.mem_singleton.mp hw
      subst w
      exact Finset.mem_filter.mpr ⟨hVS,⟨hDiv,rfl⟩⟩
  unfold parityOriginalHistoricalUngatedFixedEU434
    parityOriginalHistoricalUngatedEVStarAtU434
  change (∑w∈V,if e∣u ∧ w=vs then
    parityOriginalIntrinsicSignedAV434
      d L band slot δ ξ 0 rho signed w (u/e) else 0) = _
  rw [←Finset.sum_filter,hFilter]
  simp only [Finset.sum_singleton]
  rfl

/-- A populated true h=-2 endpoint (u=m*n-2), e|u and
vStar=ordinary_P(u/e) present in ACTUAL original B509 carrier,
collapses the FULL natural ungated Cauchy e,n,m physical sum into
that literal original 4.7 signed a_v(v), with v=u/e.
Unlike old e*vStar source gate this remains valid even when e
contains a group P prime. -/
theorem parity_original_historical_ungated_Cauchy_ENM_eq_physical_AV434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (Y e n m u : ℕ)
    (hu : u∈parityOriginalHistoricalFixedMNUSupport434 Y m n)
    (hDiv : e∣u)
    (hVS : sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (u/e) ∈
      parityOriginalReservedCartesianVStarSupport434 d L band slot δ) :
    parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m =
    parityOriginalIntrinsicSignedAV434
      d L band slot δ ξ 0 rho signed
      (sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) (u/e)) (u/e) := by
  let S := parityOriginalHistoricalFixedMNUSupport434 Y m n
  have hCard := parity_original_historical_fixed_MN_source_u_card_le_one434 Y m n
  have hUnique := Finset.card_le_one.mp hCard
  have hSingle : S={u} := by
    ext u'
    constructor
    · intro hu'
      exact Finset.mem_singleton.mpr (hUnique u' hu' u hu)
    · intro hu'
      have hh := Finset.mem_singleton.mp hu'
      subst u'
      exact hu
  rw [parity_original_historical_ungated_Cauchy_ENM_eq_fixed_EU434]
  change (∑u'∈S,parityOriginalHistoricalUngatedFixedEU434
    d L band slot δ ξ rho signed e u') = _
  rw [hSingle]
  simp only [Finset.sum_singleton]
  exact parity_original_historical_ungated_fixedEU_eq_physical_AV434
    d L band slot δ ξ rho signed e u hDiv hVS
end Green64Analytic.Parity

end

end

